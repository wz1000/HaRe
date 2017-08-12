{-#LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.Refact.Refactoring.Monadification
  (monadification,compMonadification) where

import Language.Haskell.Refact.API
import qualified GhcMod as GM (Options(..))
import System.Directory (canonicalizePath)
import qualified GHC.SYB.Utils as SYB
import Data.Generics as SYB
import qualified GHC as GHC
import Control.Monad.State

monadification :: RefactSettings -> GM.Options -> FilePath -> IO [FilePath]
monadification settings cradle fileName = do
  absFileName <- canonicalizePath fileName
  runRefacSession settings cradle (compMonadification fileName)


compMonadification :: FilePath -> RefactGhc [ApplyRefacResult]
compMonadification fileName = do
  (refRes@((_fp,ismod),_), ()) <- applyRefac (doMonadification fileName ) (RSFile fileName)
  case ismod of
    RefacUnmodifed -> error "Monadification failed"
    RefacModified -> return ()
  return [refRes]


doMonadification :: FilePath -> RefactGhc ()
doMonadification fileName = do
  parsed <- getRefactParsed
  let (Just fRdr) = locToRdrName (4,1) parsed
      (Just fFunBind) = getHsBind (GHC.unLoc fRdr) parsed
      (Just hRdr) = locToRdrName (11,1) parsed
      (Just hFunBind) = getHsBind (GHC.unLoc hRdr) parsed
  logData "doMonadification" fFunBind
  return ()


replaceBndRHS :: (ParsedLMatch -> RefactGhc ParsedLMatch) -> ParsedBind -> RefactGhc ParsedBind
replaceBndRHS fun fb@(GHC.FunBind _ _ _ _ _ _) = SYB.everywhereM (SYB.mkM fun) fb
replaceBndRHS _ bnd = return bnd

modMatchRHSExpr :: (ParsedLExpr -> RefactGhc ParsedLExpr) -> (ParsedLMatch -> RefactGhc ParsedLMatch)
modMatchRHSExpr fun = comp
  where comp lm  =  SYB.everywhereM (SYB.mkM comp') lm
        comp' :: ParsedGRHS -> RefactGhc ParsedGRHS
        comp' (GHC.GRHS lst body) = (fun body) >>= (\newBody -> return (GHC.GRHS lst newBody))

isFunCall :: [GHC.Name] -> GHC.HsExpr GHC.Name -> Bool
isFunCall nms (GHC.HsVar nm2) = elem nm2 nms
isFunCall nms (GHC.HsPar (GHC.L _ (GHC.HsVar nm2))) = elem nm2 nms
isFunCall nms (GHC.HsApp lhs _) = isFunCall nms (GHC.unLoc lhs)
isFunCall _ _ = False

isModFunCall :: ParsedLExpr -> MonadifyState Bool
isModFunCall e = do
  renE <- lift $ lookupRenamedExpr e 
  st <- get
  return $ isFunCall (funNames st) (GHC.unLoc renE)


data NameState = NS {
  num :: Int,
  name :: String
                    }

initNS :: String -> NameState
initNS nm = NS 1 nm

getNextName :: NameState -> (GHC.RdrName, NameState)
getNextName ns = (rdr, newState)
  where nameStr = (name ns) ++ (show (num ns))
        rdr = mkRdrName nameStr
        newState = ns {num = (num ns) + 1}

newName :: MonadifyState GHC.RdrName
newName = state (\s -> let n = names s
                           (rdr,ns) = getNextName n in
                         (rdr, s {names = ns}))

data MS = MS {
  names :: NameState,
  queue :: [(Maybe GHC.RdrName, ParsedLExpr)],
  funNames :: [GHC.Name]
                     }

initMS :: [GHC.Name] -> MS
initMS fns = let iNS = initNS "hare" in
  MS iNS [] fns

type MonadifyState = StateT MS RefactGhc

popQueue :: MonadifyState (Maybe GHC.RdrName, ParsedLExpr)
popQueue = state (\s -> let (e:es) = queue s
                   in (e, s {queue = es}))

--TODO the queue should eventually become [(pattern,expr)] because when
--the refactoring handles lets we'll want the argument to the lambda to
-- be the variables boind by the let

--TODO: Not sure if the queue should be a Maybe because I don't think there is a
--case where a pure function would be monadified with the >> operator
pushQueue :: (Maybe GHC.RdrName, ParsedLExpr) -> MonadifyState ()
pushQueue e = appendToQueue [e]

appendToQueue :: [(Maybe GHC.RdrName, ParsedLExpr)] -> MonadifyState ()
appendToQueue lst = state (\s -> let oldQ = queue s in
                              ((), s {queue = oldQ ++ lst}))

monadifyFunRHS :: [GHC.Name] -> ParsedLExpr -> RefactGhc ParsedLExpr
monadifyFunRHS fNames e = let initState = initMS fNames in
                              evalStateT (monadifyExpr e) initState 

    --This function handles the top expression from the rhs of a function
monadifyExpr :: ParsedLExpr -> MonadifyState ParsedLExpr
monadifyExpr expr = do
  st <- get
  strippedExpr <- applyAtArgSubTrees stripMonArgs expr
  isMonadCall <- isModFunCall expr
  newE <- if isMonadCall
    -- In this case the expression is monadic and doesn't need to be wrapped in a return
          then
            return strippedExpr
    -- Otherwise the expression needs to be wrapped with a call to return
          else
            lift $ wrapWithReturn strippedExpr
  composeWithBinds newE

lookupRenamedExpr :: ParsedLExpr -> RefactGhc (GHC.LHsExpr GHC.Name) 
lookupRenamedExpr parsedElem = do
  (grp,_ ,_, _) <- getRefactRenamed
  let (strtPos,endPos) = getStartEndLoc parsedElem
      (mRenExpr :: Maybe (GHC.LHsExpr GHC.Name)) = locToExp strtPos endPos (GHC.hs_valds grp)
  return $ gfromJust "lookupRenamedExpr: Renamed expression not found" mRenExpr

--Wraps the given expression with a return call
--If the expression isn't a HsPar it will be parenthisized first
wrapWithReturn :: ParsedLExpr -> RefactGhc ParsedLExpr
wrapWithReturn e = undefined

--Takes the expressions from the queue and binds those expressions
--with a lambda expression of the given 
composeWithBinds :: ParsedLExpr -> MonadifyState ParsedLExpr
composeWithBinds = undefined
            
--If this is called with a subtree that is a call to a monadified function
--It stores the original expression in the queue and returns a HsVar with the new name
stripMonArgs :: ParsedLExpr -> MonadifyState ParsedLExpr
stripMonArgs e = do
  st <- get
  let oldQ = queue st
  put (st {queue = []})
  stripped <- applyAtArgSubTrees stripMonArgs e
  newQ <- get >>= (\s -> return (queue s))
  modify (\s -> s {queue = oldQ})
  isMonadCall <- isModFunCall e
  resE <- if isMonadCall 
          then do
    --If this expression is a call to monad then we need to generate a new name
    --locate (HsVar newName)
    --push the new name and original expression onto the queue
    nm <- newName
    lE <- lift (locate (GHC.HsVar nm))
    pushQueue ((Just nm), e)
    return lE  
          else
    --otherwise just return the stripped expression
            return stripped
  --If the whole expression is monadic then it needs to be added to the queue
  --before the monadic calls in this expression's arguments
  appendToQueue newQ
  return resE


--Takes in an expression that should represent either a function application or an operator applicator
--The function will be applied to each argument subtree
applyAtArgSubTrees :: (ParsedLExpr -> MonadifyState ParsedLExpr) -> ParsedLExpr -> MonadifyState ParsedLExpr
applyAtArgSubTrees f (GHC.L l (GHC.HsApp lhs@(GHC.L _ (GHC.HsVar _)) rhs)) = f rhs >>= (\newRhs -> return (GHC.L l (GHC.HsApp lhs newRhs)))
applyAtArgSubTrees f (GHC.L l (GHC.HsPar e)) = do
  newE <- applyAtArgSubTrees f e
  return (GHC.L l (GHC.HsPar newE))
applyAtArgSubTrees f (GHC.L l (GHC.HsApp lhs rhs)) = do
  newLhs <- applyAtArgSubTrees f lhs
  newRhs <- f rhs
  return (GHC.L l (GHC.HsApp newLhs newRhs))
applyAtArgSubTrees _ ast = return ast
