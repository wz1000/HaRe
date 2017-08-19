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
import Language.Haskell.GHC.ExactPrint.Types
import Language.Haskell.GHC.ExactPrint
import qualified Bag as GHC
import qualified BasicTypes as GHC (RecFlag)

monadification :: RefactSettings -> GM.Options -> FilePath -> [SimpPos] -> IO [FilePath]
monadification settings cradle fileName posLst = do
  absFileName <- canonicalizePath fileName
  runRefacSession settings cradle (compMonadification fileName posLst)


compMonadification :: FilePath -> [SimpPos] -> RefactGhc [ApplyRefacResult]
compMonadification fileName posLst = do
  (refRes@((_fp,ismod),_), ()) <- applyRefac (doMonadification fileName posLst) (RSFile fileName)
  case ismod of
    RefacUnmodifed -> error "Monadification failed"
    RefacModified -> return ()
  return [refRes]

doMonadification :: FilePath -> [SimpPos] -> RefactGhc ()
doMonadification fileName posLst = do
  nmsList <- getNames posLst
  mapM_ (monadifyFunc nmsList) posLst

getNames :: [SimpPos] -> RefactGhc [GHC.Name]
getNames posLst = mapM lookupNm posLst
  where lookupNm pos = do
          parsed <- getRefactParsed
          let rdr = gfromJust ("Unable to find name at " ++ (show pos)) (locToRdrName pos parsed)
          rdrName2Name rdr



monadifyFunc :: [GHC.Name] -> SimpPos -> RefactGhc ()
monadifyFunc nmsList pos = do
  parsed <- getRefactParsed
  let (Just rdr) = locToRdrName pos parsed
      (Just funBind) = getHsBind (GHC.unLoc rdr) parsed
  monadifyFunBind pos nmsList funBind
  --logParsedSource "After monadification"
  addMonadToSig pos
  finParsed <- getRefactParsed
  --logDataWithAnns "Post monadification refactoring" finParsed
  return ()

monadifyFunBind :: SimpPos -> [GHC.Name] -> ParsedBind -> RefactGhc ()
monadifyFunBind pos nms bnd = do
  newBnd <- replaceBndRHS (modMatchRHSExpr (monadifyFunRHS nms)) bnd
  replaceFunBind pos newBnd

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
isFunCall nms (GHC.HsPar e) = isFunCall nms (GHC.unLoc e)
isFunCall nms (GHC.HsApp lhs _) = isFunCall nms (GHC.unLoc lhs)
isFunCall nms (GHC.HsLet _ e) = isFunCall nms (GHC.unLoc e)
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
  queue :: [(GHC.LPat GHC.RdrName, ParsedLExpr)],
  funNames :: [GHC.Name]
                     }

showQueue :: [(GHC.LPat GHC.RdrName, ParsedLExpr)] -> RefactGhc String
showQueue [] = return ""
showQueue ((mNm,expr):rst) = do
  anns <- fetchAnnsFinal
  let str = exactPrint expr anns
  rStr <- showQueue rst
  return $ "(" ++ (SYB.showData SYB.Parser 3 mNm) ++ ", " ++ str ++ ")\n" ++ rStr

initMS :: [GHC.Name] -> MS
initMS fns = let iNS = initNS "hare" in
  MS iNS [] fns

type MonadifyState = StateT MS RefactGhc

popQueue :: MonadifyState (GHC.LPat GHC.RdrName, ParsedLExpr)
popQueue = state (\s -> let (e:es) = queue s
                   in (e, s {queue = es}))

--TODO the queue should eventually become [(pattern,expr)] because when
--the refactoring handles lets we'll want the argument to the lambda to
-- be the variables boind by the let

--TODO: Not sure if the queue should be a Maybe because I don't think there is a
--case where a pure function would be monadified with the >> operator
pushQueue :: (GHC.LPat GHC.RdrName, ParsedLExpr) -> MonadifyState ()
pushQueue e = appendToQueue [e]

appendToQueue :: [(GHC.LPat GHC.RdrName, ParsedLExpr)] -> MonadifyState ()
appendToQueue lst = state (\s -> let oldQ = queue s in
                              ((), s {queue = oldQ ++ lst}))

isQueueEmpty :: MonadifyState Bool
isQueueEmpty = get >>= (\s -> return (null (queue s)))

monadifyFunRHS :: [GHC.Name] -> ParsedLExpr -> RefactGhc ParsedLExpr
monadifyFunRHS fNames e = let initState = initMS fNames in do
  newE <- evalStateT (monadifyExpr e) initState
  return newE

printQueueStatus :: MonadifyState ()
printQueueStatus = do
  st <- get
  let q = queue st
  lift $ logm ("The queue has " ++ (show $ length q) ++ " elements")
  qStat <- lift (showQueue q)
  lift $ logm qStat

isLet (GHC.L _ (GHC.HsLet _ _)) = True
isLet _ = False

    --This function handles the top expression from the rhs of a function
monadifyExpr :: ParsedLExpr -> MonadifyState ParsedLExpr
monadifyExpr expr = do
  st <- get
  strippedExpr <- applyAtArgSubTrees (stripMonArgs True) expr
  isMonadCall <- isModFunCall expr
  newE <- if isMonadCall || isLet expr
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
wrapWithReturn e@(GHC.L _ (GHC.HsPar _)) = do
  retVar <- locate (GHC.HsVar returnRdr)
  addAnnVal retVar
  locate (GHC.HsApp retVar e)
wrapWithReturn e@(GHC.L _ (GHC.HsVar _)) = do
  retVar <- locate (GHC.HsVar returnRdr)
  addAnnVal retVar
  locate (GHC.HsApp retVar e)
wrapWithReturn e = do
  retVar <- locate (GHC.HsVar returnRdr)
  addAnnVal retVar
  zeroDP e
  isPared <- isWrappedInPars e
  pE <- if isPared
        then do
    setDP (DP (0,1)) e
    return e
        else wrapInPars e
  locate (GHC.HsApp retVar pE)

returnRdr :: GHC.RdrName
returnRdr = mkRdrName "return"

--Takes the expressions from the queue and binds those expressions
--with a lambda expression made from the given expression and the variable from the top of the queue
composeWithBinds :: ParsedLExpr -> MonadifyState ParsedLExpr
composeWithBinds e = do
  done <- isQueueEmpty
  if done
    then return e
    else do
    (pat, lhsExpr) <- popQueue
    --Make lambda
    --lamPat <- lift $ mkVarPat var
    lamRHS <- lift $ mkGRHSs e
    lambda <- lift $ wrapInLambda pat lamRHS
    --locate + annVal bindRdr
    lBindOp <- lift (locate (GHC.HsVar bindRdr))
    lift $ addAnnVal lBindOp
    --opApp lhsExpr locBnd lambda
    let opApp = (GHC.OpApp lhsExpr lBindOp GHC.PlaceHolder lambda)
    lOpApp <- lift $ locate opApp
    composeWithBinds lOpApp
    
mkGRHSs :: ParsedLExpr -> RefactGhc ParsedGRHSs
mkGRHSs rhsExpr = do
  let grhs = (GHC.GRHS [] rhsExpr)
  lGrhs <- locate grhs
  return (GHC.GRHSs [lGrhs] GHC.EmptyLocalBinds)

mkVarPat :: GHC.RdrName -> RefactGhc (GHC.LPat GHC.RdrName)
mkVarPat nm = do
  let pat = (GHC.VarPat nm)
  lPat <- locate pat
  addAnnVal lPat
  return lPat
  

bindRdr :: GHC.RdrName
bindRdr = mkRdrName ">>="
    
--If this is called with a subtree that is a call to a monadified function
--It stores the original expression in the queue and returns a HsVar with the new name
stripMonArgs :: Bool -> ParsedLExpr -> MonadifyState ParsedLExpr
stripMonArgs wrap e = do
  st <- get
  let oldQ = queue st
  put (st {queue = []})
  stripped <- applyAtArgSubTrees (stripMonArgs wrap) e
  newQ <- get >>= (\s -> return (queue s))
  modify (\s -> s {queue = oldQ})
  isMonadCall <- isModFunCall e
  resE <- if isMonadCall && wrap
          then do
    --If this expression is a call to monad then we need to generate a new name
    --locate (HsVar newName)
    --push the new name and original expression onto the queue
    nm <- newName
    lE <- lift (locWithAnnVal (GHC.HsVar nm))
    pat <- lift (mkVarPat nm)
    pushQueue (pat, e)
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
applyAtArgSubTrees f (GHC.L l (GHC.HsLet locBnds expr)) = do
  renamed <- lift getRefactRenamed
  let renExpr = getNamedExprByPos l renamed
  mBnds <- filterBinds renExpr
  newExpr <- f expr
  retExpr <- lift $ wrapWithReturn newExpr
  lift $ logm ("newEXPR::::: " ++ (SYB.showData SYB.Parser 3 newExpr) )
  case mBnds of
    Just bnds -> return (GHC.L l (GHC.HsLet bnds retExpr))
    Nothing -> return retExpr
applyAtArgSubTrees _ ast = return ast

getNamedExprByPos :: (Data a) => GHC.SrcSpan -> a -> GHC.LHsExpr GHC.Name
getNamedExprByPos pos a = let res = SYB.something (Nothing `SYB.mkQ` comp) a in
  gfromJust "getNamedExprByPos: No expression found." res
  where comp ::  GHC.LHsExpr GHC.Name -> Maybe (GHC.LHsExpr GHC.Name)
        comp e@(GHC.L l _) = if l == pos
                             then (Just e)
                             else Nothing
        comp _ = Nothing

getParsedExprByPos :: (Data a) => GHC.SrcSpan -> a -> ParsedLExpr
getParsedExprByPos = getParsedByPos

getParsedBindByPos :: (Data a) => GHC.SrcSpan -> a -> ParsedLBind
getParsedBindByPos = getParsedByPos

getParsedByPos pos a = let res = SYB.something (Nothing `SYB.mkQ` comp) a in
  gfromJust "getNamedExprByPos: No expression found." res
  where comp e@(GHC.L l _) = if l == pos
                             then (Just e)
                             else Nothing
        comp _ = Nothing

filterBinds :: GHC.LHsExpr GHC.Name -> MonadifyState (Maybe (GHC.HsLocalBinds GHC.RdrName))
filterBinds (GHC.L l (GHC.HsLet locBnds _)) = case locBnds of
  (GHC.HsValBinds (GHC.ValBindsOut lst _)) -> do
    newLst <- mMapMaybe handleBind (reverse lst)
    case newLst of
      [] -> return Nothing
      lst -> return (Just (GHC.HsValBinds (GHC.ValBindsIn (GHC.listToBag (reverse lst)) [])))    
filterBinds _ = error "filterBinds: Called with a non-let expression."

{- This is what handles an expression on the rhs of a let
   any monadic calls inside of the expression are stripped and added to the queue before
   the top level let expression 

Assuming mon and mon2 are monadic
let f = mon (mon2 4) 5 in
expr ===>
(mon2 4) >>= (\hare1 -> mon hare1 5 >>= (f -> expr))
-}  

handleBind :: (GHC.RecFlag, GHC.LHsBinds GHC.Name) -> MonadifyState (Maybe (GHC.LHsBindLR GHC.RdrName GHC.RdrName))
handleBind (_, bg) = do
  let [(GHC.L l bnd)] = GHC.bagToList bg
  parsed <- lift getRefactParsed
  let pBnd = getParsedBindByPos l parsed
  case pBnd of
    (GHC.L l fb@(GHC.FunBind (GHC.L _ id) _ mg _ _ _)) -> do
      let expr = getExprFromMG mg
      isModCall <- isModFunCall expr
      newExpr <- stripMonArgs False expr
      if isModCall
        then do
        pat <- lift (mkVarPat id)
        pushQueue (pat,newExpr)
        return Nothing
        else return (Just (GHC.L l (fb {GHC.fun_matches = replaceMGExpr newExpr mg})))
    (GHC.L l pb@(GHC.PatBind pat grhss _ _ _)) -> do
      let expr = getExprFromGRHSs grhss
      newExpr <- stripMonArgs False expr
      isModCall <- isModFunCall expr
      if isModCall
        then do
        pushQueue (pat, newExpr)
        return Nothing
        else return (Just (GHC.L l (pb {GHC.pat_rhs = replaceGRHSsExpr newExpr grhss})))
      

replaceMGExpr :: ParsedLExpr -> ParsedMatchGroup -> ParsedMatchGroup
replaceMGExpr e = SYB.everywhere (SYB.mkT (replaceGRHSExpr e))

replaceGRHSsExpr :: ParsedLExpr -> ParsedGRHSs -> ParsedGRHSs
replaceGRHSsExpr e = SYB.everywhere (SYB.mkT (replaceGRHSExpr e))

replaceGRHSExpr :: ParsedLExpr -> ParsedGRHS -> ParsedGRHS
replaceGRHSExpr e (GHC.GRHS stmts _) = (GHC.GRHS stmts e)
replaceGRHSExpr _ grhs = grhs

getExprFromGRHSs :: ParsedGRHSs -> ParsedLExpr
getExprFromGRHSs grhs = let res = SYB.something (Nothing `SYB.mkQ` comp) grhs in
  gfromJust "getExprFromMG" res
  where comp :: ParsedLExpr -> Maybe ParsedLExpr
        comp e = Just e 

getExprFromMG :: ParsedMatchGroup -> ParsedLExpr
getExprFromMG mg = let res = SYB.something (Nothing `SYB.mkQ` comp) mg in
  gfromJust "getExprFromMG" res
  where comp :: ParsedLExpr -> Maybe ParsedLExpr
        comp e = Just e
                       

mMapMaybe :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
mMapMaybe _ [] = return []
mMapMaybe f (x:xs) = do
  mElem <- f x
  rst <- mMapMaybe f xs
  case mElem of
    Nothing -> return rst
    (Just elem) -> return (elem:rst)
  

getTypeSigByName :: (Data t) => GHC.RdrName -> t -> Maybe (GHC.Sig GHC.RdrName)
getTypeSigByName nm t = SYB.something (Nothing `SYB.mkQ` comp) t
  where comp :: GHC.Sig GHC.RdrName -> Maybe (GHC.Sig GHC.RdrName)
        comp s@(GHC.TypeSig [(GHC.L _ x)] _ _) = if nm == x
                                       then Just s
                                       else Nothing
        comp _ = Nothing


--This adds the monad class constraint to the front of a
--binds type signature and wraps the result type with the monad type variable
--It may also not affect anything if there is no signature found
addMonadToSig :: SimpPos -> RefactGhc ()
addMonadToSig pos = do
  parsed <- getRefactParsed
  let (Just (GHC.L _ rdrNm)) = locToRdrName pos parsed
      tySig = getTypeSigByName rdrNm parsed
  case tySig of
    (Just sig) -> do
      newSig <- modTySig sig
      replaceTypeSig pos newSig
    Nothing -> return ()
    where modTySig :: GHC.Sig GHC.RdrName -> RefactGhc (GHC.Sig GHC.RdrName)
          modTySig (GHC.TypeSig nms ty pstRn) = (modType ty)  >>= (\nTy -> return (GHC.TypeSig nms nTy pstRn))
          modTySig _ = error "addMonadToSig: modTySig called with an unknown constructor."
          modType :: GHC.LHsType GHC.RdrName -> RefactGhc (GHC.LHsType GHC.RdrName)
          modType (GHC.L l (GHC.HsForAllTy flg mSpn bndrs (GHC.L l2 cntxt) ty)) = do            
            lMonTy <- locWithAnnVal (GHC.HsTyVar (mkRdrName "Monad"))
            zeroDP lMonTy
            lVarTy <- locWithAnnVal (GHC.HsTyVar (mkRdrName "m"))
            newTy <- wrapResTy (mkRdrName "m") ty
            let appTy = (GHC.HsAppTy lMonTy lVarTy)
            lAppTy <- locWithAnnVal appTy
            zeroDP lAppTy
            newCntxt <- if (null cntxt)
                        then do
              lCntxt <- locate [lAppTy]
              (addNewKeyword (G GHC.AnnDarrow, DP (0,1)) lCntxt)
              zeroDP lCntxt
              return lCntxt
                        else return (GHC.L l2 (lAppTy:cntxt))
            setDP  (DP (0,1)) newTy            
            return (GHC.L l (GHC.HsForAllTy flg mSpn bndrs newCntxt newTy))
          wrapResTy :: GHC.RdrName -> GHC.LHsType GHC.RdrName -> RefactGhc (GHC.LHsType GHC.RdrName)
          wrapResTy rdr (GHC.L l (GHC.HsFunTy lTy rTy)) = (wrapResTy rdr rTy) >>= (\nRTy -> return (GHC.L l (GHC.HsFunTy lTy nRTy)))
          wrapResTy rdr locTy = locWithAnnVal (GHC.HsTyVar rdr) >>= (\ lTyVar -> locate (GHC.HsAppTy lTyVar locTy))
