{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
module Language.Haskell.Refact.Refactoring.Simple(removeBracket) where

import qualified Data.Generics         as SYB

import qualified GHC           as GHC

import qualified GhcModCore as GM (Options(..))
import Language.Haskell.Refact.API

-- To be moved into HaRe API
import Language.Haskell.GHC.ExactPrint.Transform
import Language.Haskell.GHC.ExactPrint.Types

import Data.Maybe
import System.Directory

-- import Debug.Trace

-- ---------------------------------------------------------------------

-- | Convert an if expression to a case expression
removeBracket :: RefactSettings -> GM.Options -> FilePath -> SimpPos -> SimpPos -> IO [FilePath]
removeBracket settings opts fileName beginPos endPos = do
  absFileName <- normaliseFilePath fileName
  let applied = (:[]) . fst <$> applyRefac
                  (removeBracketTransform absFileName beginPos endPos)
                  (RSFile absFileName)
  runRefacSession settings opts applied

-- type HsExpr a = GHC.Located (GHC.HsExpr a)

removeBracketTransform  :: FilePath -> SimpPos -> SimpPos -> RefactGhc ()
removeBracketTransform fileName beginPos endPos = do
       parsed <- getRefactParsed
       let expr :: GHC.Located (GHC.HsExpr GhcPs)
           expr = fromJust $ locToExp beginPos endPos parsed
           removePar :: GHC.LHsExpr GhcPs -> RefactGhc (GHC.LHsExpr GhcPs)
#if __GLASGOW_HASKELL__ >= 806
           removePar e@(GHC.L _ (GHC.HsPar _ s))
#else
           removePar e@(GHC.L _ (GHC.HsPar s))
#endif
            | sameOccurrence e expr = do
              startAnns <- liftT $ getAnnsT
              let oldkey = mkAnnKey e
                  newkey = mkAnnKey s
                  newanns = fromMaybe startAnns $ replace oldkey newkey startAnns
              setRefactAnns newanns
              return s
           removePar e = return e
       p2 <- SYB.everywhereM (SYB.mkM removePar) parsed
       putRefactParsed p2 emptyAnns
       logm $ "logm: after refactor\n" ++ showGhc p2

-- EOF

