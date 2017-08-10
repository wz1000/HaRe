module Language.Haskell.Refact.Refactoring.Monadification
  (monadification,compMonadification) where

import Language.Haskell.Refact.API
import qualified GhcMod as GM (Options(..))
import System.Directory (canonicalizePath)

monadification :: RefactSettings -> GM.Options -> FilePath -> IO [FilePath]
monadification settings cradle fileName = do
  absFileName <- canonicalizePath fileName
  runRefacSession settings cradle (compMonadification fileName)


compMonadification :: FilePath -> RefactGhc [ApplyRefacResult]
compMonadification fileName = undefined
