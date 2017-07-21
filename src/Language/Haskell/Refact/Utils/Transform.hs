module Language.Haskell.Refact.Utils.Transform
  (
    addSimpleImportDecl
  , wrapInLambda
  , wrapInPars
  , addNewLines
  , locate
  ) where

import qualified GHC as GHC
import qualified BasicTypes as GHC
import qualified Data.Map as Map
import Data.Data

import Language.Haskell.GHC.ExactPrint
import Language.Haskell.GHC.ExactPrint.Types

import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.MonadFunctions
import Language.Haskell.Refact.Utils.TypeUtils
import Language.Haskell.Refact.Utils.Synonyms
import Language.Haskell.Refact.Utils.ExactPrint

-- The goal of this module is to provide basic transformations of the ast and
-- annotations that are useful in multiple refactorings


--Takes in a string corresponding to the module name to be imported
--Adds the import declaration at the end of that module's imports 
addSimpleImportDecl :: String -> RefactGhc ()
addSimpleImportDecl modName = do
  let modNm' = GHC.mkModuleName modName
  parsed <- getRefactParsed
  newP <- addImportDecl parsed modNm' Nothing False False False Nothing False []
  currAnns <- fetchAnnsFinal
  putRefactParsed newP currAnns

--Takes in a lhs pattern and a rhs. Wraps those in a lambda and adds the annotations associated with the lambda. Returns the new located lambda expression

wrapInLambda :: String -> GHC.LPat GHC.RdrName -> ParsedGRHSs -> RefactGhc (GHC.LHsExpr GHC.RdrName)
wrapInLambda funNm varPat rhs = do
  match <- mkLamMatch varPat rhs  
  let mg = GHC.MG [match] [] GHC.PlaceHolder GHC.Generated
  --logm $ "Anns :" ++ (show $ getAllAnns currAnns match)
  l_lam <- locate (GHC.HsLam mg)
  let key = mkAnnKey l_lam
      dp = (G GHC.AnnLam, DP (0,0))
  addNewKeyword dp l_lam 
  par_lam <- wrapInPars l_lam
  logDataWithAnns "newLambda" par_lam
  logExactprint "lam2" l_lam
  return par_lam

  --This function makes a match suitable for use inside of a lambda expression. 
mkLamMatch :: GHC.LPat GHC.RdrName -> GHC.GRHSs GHC.RdrName (GHC.LHsExpr GHC.RdrName) -> RefactGhc (GHC.LMatch GHC.RdrName (GHC.LHsExpr GHC.RdrName))
mkLamMatch varPat rhs = do
  lMatch@(GHC.L l m) <- locate (GHC.Match Nothing [varPat] Nothing rhs)
  let dp = [(G GHC.AnnRarrow, DP (0,1))]
      newAnn = annNone {annsDP = dp, annEntryDelta = DP (0,0)}
  zeroDP varPat
  addAnn lMatch newAnn
  return lMatch

--Wraps a given expression in parenthesis and add the appropriate annotations, returns the modified ast chunk. 
wrapInPars :: GHC.LHsExpr GHC.RdrName -> RefactGhc (GHC.LHsExpr GHC.RdrName)
wrapInPars expr = do
  newAst <- locate (GHC.HsPar expr)
  let dp = [(G GHC.AnnOpenP, DP (0,1)), (G GHC.AnnCloseP, DP (0,0))]
      newAnn = annNone {annsDP = dp}
  addAnn newAst newAnn
  return newAst

--Takes a piece of AST and adds an n row offset
addNewLines :: (Data a) => Int -> GHC.Located a -> RefactGhc ()
addNewLines n ast = do
  currAnns <- fetchAnnsFinal
  let key = mkAnnKey ast
      mv = Map.lookup key currAnns
  case mv of
    Nothing -> return ()
    Just v -> do
      let (DP (row,col)) = annEntryDelta v
          newDP = (DP (row+n,col))
          newAnn = v {annEntryDelta = newDP}
          newAnns = Map.insert key newAnn currAnns
      setRefactAnns newAnns
