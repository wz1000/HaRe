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

pushQueue :: (Maybe GHC.RdrName, ParsedLExpr) -> MonadifyState ()
pushQueue e = state (\s -> let oldQ = queue s in
                        ((), s {queue = oldQ ++ [e]}))

monadifyExpr :: [GHC.Name] -> ParsedLExpr -> RefactGhc ParsedLExpr
monadifyExpr funNames e = undefined
