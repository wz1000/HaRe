module Language.Haskell.Refact.Refactoring.HughesList
       (hughesList, compHughesList) where

import Language.Haskell.Refact.API
import qualified Language.Haskell.GhcMod as GM
import System.Directory

hughesList :: RefactSettings -> GM.Options -> FilePath -> String -> SimpPos -> IO [FilePath]
hughesList settings cradle fileName funNm pos = do
  absFileName <- canonicalizePath fileName
  runRefacSession settings cradle (compHughesList fileName funNm pos)

compHughesList :: FilePath -> String -> SimpPos -> RefactGhc [ApplyRefacResult]
compHughesList fileName funNm pos = undefined


