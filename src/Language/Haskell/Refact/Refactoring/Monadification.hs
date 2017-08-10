module Language.Haskell.Refact.Refactoring.Monadification
  (monadification,compMonadification) where

import Language.Haskell.Refact.API
import qualified GhcMod as GM (Options(..))
import System.Directory (canonicalizePath)
import qualified GHC.SYB.Utils as SYB
import Data.Generics as SYB
import qualified GHC as GHC

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
  let (Just lrdr) = locToRdrName (15,1) parsed
      (Just funBind) = getHsBind (GHC.unLoc lrdr) parsed
  logData "doMonadification" funBind
  return ()


replaceBndRHS :: (ParsedLMatch -> RefactGhc ParsedLMatch) -> ParsedBind -> RefactGhc ParsedBind
replaceBndRHS fun fb@(GHC.FunBind _ _ _ _ _ _) = SYB.everywhereM (SYB.mkM fun) fb
replaceBndRHS _ bnd = return bnd

modMatchRHSExpr :: (ParsedLExpr -> RefactGhc ParsedLExpr) -> (ParsedLMatch -> RefactGhc ParsedLMatch)
modMatchRHSExpr fun = comp
  where comp lm  =  SYB.everywhereM (SYB.mkM comp') lm
        comp' :: ParsedGRHS -> RefactGhc ParsedGRHS
        comp' (GHC.GRHS lst body) = (fun body) >>= (\newBody -> return (GHC.GRHS lst newBody))


isFunCall :: GHC.Name -> GHC.HsExpr GHC.Name -> Boolean
isFunCall nm (GHC.HsVar nm2) = nm == nm2
isFunCall nm (GHC.HsPar (GHC.L _ (GHC.HsVar nm2))) = nm == nm2
isFunCall nm (GHC.HsApp lhs _) = isFunCall nm lhs
isFunCall _ _ = False
