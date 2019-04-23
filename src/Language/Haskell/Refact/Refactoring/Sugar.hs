module Language.Haskell.Refact.Refactoring.Sugar (sugar, compSugar) where

import Language.Haskell.Refact.API
import qualified Haskell.Ide.Engine.PluginApi as HIE (Options(..))

sugar :: RefactSettings -> HIE.Options -> FilePath -> SimpPos -> IO [FilePath]
sugar settings cradle fileName pos = do
  absFileName <- normaliseFilePath fileName
  runRefacSession settings cradle (compSugar absFileName pos)

compSugar :: FilePath -> SimpPos -> RefactGhc [ApplyRefacResult]
compSugar fileName pos = do
  (refRes@((_fp,ismod),_), ()) <- applyRefac (doSugaring pos) (RSFile fileName)
  case ismod of
    RefacUnmodifed -> error "Desugaring failed"
    RefacModified -> return ()
  return [refRes]

doSugaring :: SimpPos -> RefactGhc ()
doSugaring _pos = do
  -- parsed <- getRefactParsed

  return ()
