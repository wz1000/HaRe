{-# LANGUAGE CPP #-}
module Language.Haskell.Refact.Utils.Transform
  (
    addSimpleImportDecl
  , wrapInLambda
  , wrapInPars
  , wrapInParsWithDPs
  , addNewLines
  , locate
  , removePars
  , replaceTypeSig
  , replaceFunBind
  , addBackquotes
  , constructLHsTy
  , constructHsVar
  ) where

import qualified GHC as GHC
import qualified BasicTypes as GHC
import qualified Data.Map as Map
import Data.Data
import qualified Data.Generics as SYB

import Language.Haskell.GHC.ExactPrint
import Language.Haskell.GHC.ExactPrint.Types

import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.MonadFunctions
import Language.Haskell.Refact.Utils.Types
import Language.Haskell.Refact.Utils.Utils
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
  match@(GHC.L l match') <- mkMatch varPat rhs
  --logm $ "Match: " ++ (SYB.showData SYB.Parser 3 match)
#if __GLASGOW_HASKELL__ <= 710
  let mg = GHC.MG [match] [] GHC.PlaceHolder GHC.Generated
#else
  lMatchLst <- locate [match]
  let mg = GHC.MG lMatchLst [] GHC.PlaceHolder GHC.Generated
#endif
  currAnns <- fetchAnnsFinal
  --logm $ "Anns :" ++ (show $ getAllAnns currAnns match)
  let l_lam = (GHC.L l (GHC.HsLam mg))
      key = mkAnnKey l_lam
      dp = [(G GHC.AnnLam, DP (0,0))]
      newAnn = annNone {annsDP = dp}
  setRefactAnns $ Map.insert key newAnn currAnns
  par_lam <- wrapInPars l_lam
  return par_lam

  --This function makes a match suitable for use inside of a lambda expression. Should change name or define it elsewhere to show that this is not a general-use function. 
mkMatch :: GHC.LPat GHC.RdrName -> GHC.GRHSs GHC.RdrName (GHC.LHsExpr GHC.RdrName) -> RefactGhc (GHC.LMatch GHC.RdrName (GHC.LHsExpr GHC.RdrName))
mkMatch varPat rhs = do
#if __GLASGOW_HASKELL__ <= 710
  lMatch@(GHC.L l m) <- locate (GHC.Match Nothing [varPat] Nothing rhs)
#else
  lMatch@(GHC.L l m) <- locate (GHC.Match GHC.NonFunBindMatch [varPat] Nothing rhs)
#endif
  let dp = [(G GHC.AnnRarrow, DP (0,1))]
      newAnn = annNone {annsDP = dp, annEntryDelta = DP (0,-1)}
  zeroDP varPat
  addAnn lMatch newAnn
  return lMatch

wrapInParsWithDPs :: DeltaPos -> DeltaPos -> GHC.LHsExpr GHC.RdrName -> RefactGhc (GHC.LHsExpr GHC.RdrName)
wrapInParsWithDPs openDP closeDP expr = do
  newAst <- locate (GHC.HsPar expr)
  let dp = [(G GHC.AnnOpenP, openDP), (G GHC.AnnCloseP, closeDP)]
      newAnn = annNone {annsDP = dp}
  addAnn newAst newAnn
  return newAst


--Wraps a given expression in parenthesis and add the appropriate annotations, returns the modified ast chunk. 
wrapInPars :: GHC.LHsExpr GHC.RdrName -> RefactGhc (GHC.LHsExpr GHC.RdrName)
wrapInPars = wrapInParsWithDPs (DP (0,1)) (DP (0,0))

--Does the opposite of wrapInPars
removePars :: ParsedLExpr -> RefactGhc ParsedLExpr
removePars (GHC.L _ (GHC.HsPar expr)) = do
  setDP (DP (0,1)) expr
  return expr
removePars expr = return expr
  
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


--This function replaces the type signature of the function that is defined at the simple position
replaceTypeSig :: SimpPos -> GHC.Sig GHC.RdrName -> RefactGhc ()
replaceTypeSig pos sig = do
  parsed <- getRefactParsed
  let (Just (GHC.L _ rdrNm)) = locToRdrName pos parsed
  newParsed <- SYB.everywhereM (SYB.mkM (comp rdrNm)) parsed
  putRefactParsed newParsed emptyAnns
    where comp :: GHC.RdrName -> GHC.Sig GHC.RdrName -> RefactGhc (GHC.Sig GHC.RdrName)
#if __GLASGOW_HASKELL__ <= 710
          comp nm oldTy@(GHC.TypeSig [(GHC.L _ oldNm)]  _ _)
#else
          comp nm oldTy@(GHC.TypeSig [(GHC.L _ oldNm)]  _)         
#endif
            | oldNm == nm = return sig
            | otherwise = return oldTy
          comp _ x = return x

--Replaces the HsBind at the given position
replaceFunBind :: SimpPos -> GHC.HsBind GHC.RdrName -> RefactGhc ()
replaceFunBind pos bnd = do
  parsed <- getRefactParsed
  let (Just (GHC.L _ rdrNm)) = locToRdrName pos parsed
  newParsed <- SYB.everywhereM (SYB.mkM (comp rdrNm)) parsed
  putRefactParsed newParsed emptyAnns
    where comp :: GHC.RdrName -> GHC.HsBind GHC.RdrName -> RefactGhc (GHC.HsBind GHC.RdrName)
#if __GLASGOW_HASKELL__ <= 710          
          comp nm b@(GHC.FunBind (GHC.L _ id) _ _ _ _ _)
#else
          comp nm b@(GHC.FunBind (GHC.L _ id) _ _ _ _)
#endif
            | id == nm = return bnd
            | otherwise = return b
          comp _ x = return x
              
 
--Adds backquotes around a function call
addBackquotes :: ParsedLExpr -> RefactGhc ()
addBackquotes var@(GHC.L l _) = do
  anns <- liftT getAnnsT
  let (Just oldAnn) = Map.lookup (mkAnnKey var) anns
      annsLst = annsDP oldAnn
      bqtAnn = ((G GHC.AnnBackquote),DP (0,0))
      newLst = bqtAnn:(annsLst++[bqtAnn])
      newAnn = oldAnn {annsDP = newLst}
  addAnn var newAnn


--The next two functions construct variables and type variables respectively from RdrNames.
--They keep the amount of CPP in refactoring code to a minimum.
constructHsVar :: GHC.RdrName -> RefactGhc ParsedLExpr
constructHsVar nm = do
#if __GLASGOW_HASKELL__ <= 710
  newVar <- locate (GHC.HsVar nm)
#else
  lNm <- locate nm
  newVar <- locate (GHC.HsVar lNm)
#endif
  return newVar

constructLHsTy :: GHC.RdrName -> RefactGhc (GHC.LHsType GHC.RdrName)
constructLHsTy nm = do
#if __GLASGOW_HASKELL__ <= 710
  newTy <- locate (GHC.HsTyVar nm)
#else
  lNm <- locate nm
  newTy <- locate (GHC.HsTyVar lNm)
#endif
  return newTy    
