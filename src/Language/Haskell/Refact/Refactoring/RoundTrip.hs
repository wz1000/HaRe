module Language.Haskell.Refact.Refactoring.RoundTrip(roundTrip) where

import qualified Haskell.Ide.Engine.PluginApi as HIE (Options(..))
import Language.Haskell.Refact.API

-- import System.Directory

-- ---------------------------------------------------------------------

-- | Roundtrip the source code, to check that the infrastructure is solid
roundTrip :: RefactSettings -> HIE.Options -> FilePath -> IO [FilePath]
roundTrip settings opts fileName = do
  absFileName <- normaliseFilePath fileName
  runRefacSession settings opts (comp absFileName)

comp :: FilePath -> RefactGhc [ApplyRefacResult]
comp fileName = do
  parseSourceFileGhc fileName
  (r,_) <- applyRefac (setRefactStreamModified RefacModified) RSAlreadyLoaded
  return [r]

-- EOF
