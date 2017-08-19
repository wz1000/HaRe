{-# LANGUAGE CPP #-}
module Language.Haskell.Refact.Utils.Transform
  (
    addSimpleImportDecl
  , wrapInLambda
  , wrapInPars
  , wrapInParsWithDPs
  , addNewLines
  , locate
  , locWithAnnVal
  , removePars
  , replaceTypeSig
  , replaceFunBind
  , addBackquotes
  , constructLHsTy
  , constructHsVar
  , insertNewDecl
  , rmFun
  , replaceFunRhs
  , traverseTypeSig
  ) where

import qualified GHC as GHC
import qualified BasicTypes as GHC
import qualified Data.Map as Map
import Data.Data
import Data.Maybe
import qualified Data.Generics as SYB
import qualified GHC.SYB.Utils as SYB
import qualified FastString as GHC
import Language.Haskell.GHC.ExactPrint
import Language.Haskell.GHC.ExactPrint.Types
import Language.Haskell.GHC.ExactPrint.Parsers
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
addSimpleImportDecl :: String -> Maybe String -> RefactGhc ()
addSimpleImportDecl modName mqual = do
  let modNm' = GHC.mkModuleName modName
  parsed <- getRefactParsed
  newP <- addImportDecl parsed modNm' Nothing False False (isJust mqual) mqual False []
  putRefactParsed newP mempty



--Locates an piece of abstract syntax and adds a AnnVal annotation at the new location
locWithAnnVal :: Data a => a -> RefactGhc (GHC.Located a)
locWithAnnVal a = do
  lA <- locate a
  addAnnVal lA
  return lA


--Takes in a lhs pattern and a rhs. Wraps those in a lambda and adds the annotations associated with the lambda. Returns the new located lambda expression
wrapInLambda :: GHC.LPat GHC.RdrName -> ParsedGRHSs -> RefactGhc (GHC.LHsExpr GHC.RdrName)
wrapInLambda varPat rhs = do
  match@(GHC.L l match') <- mkMatch varPat rhs
  --logm $ "Match: " ++ (SYB.showData SYB.Parser 3 match)
#if __GLASGOW_HASKELL__ <= 710
  let mg = GHC.MG [match] [] GHC.PlaceHolder GHC.Generated
#else
  lMatchLst <- locate [match]
  let mg = GHC.MG lMatchLst [] GHC.PlaceHolder GHC.Generated
#endif
  let l_lam = (GHC.L l (GHC.HsLam mg))
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
  let dp = [(G GHC.AnnRarrow, DP (0,1)),(G GHC.AnnLam, DP (0,0))]
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
replaceFunBind :: SimpPos -> ParsedBind -> RefactGhc ()
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
  logm $ "New var construction ghc 8"
  lNm <- locate nm
  addAnnVal lNm
  zeroDP lNm
  newVar <- locate (GHC.HsVar lNm)
#endif
  addAnnVal newVar
  return newVar

constructLHsTy :: GHC.RdrName -> RefactGhc (GHC.LHsType GHC.RdrName)
constructLHsTy nm = do
#if __GLASGOW_HASKELL__ <= 710
  logm "New ty var ghc 7" 
  newTy <- locate (GHC.HsTyVar nm)
#else
  lNm <- locate nm
  addAnnVal lNm
  zeroDP lNm
  newTy <- locate (GHC.HsTyVar lNm)
#endif
  addAnnVal newTy
  zeroDP newTy
  return newTy

-- Inserts the string representation of the decl
-- at the end of the target module returns the location
-- of the new declaration
insertNewDecl :: String -> RefactGhc ParsedLDecl
insertNewDecl declStr = do
  (GHC.L pSpn hsMod) <- getRefactParsed
  trgtMod <- getRefactTargetModule
  -- Use a fake filepath the ensure that the location remains unique
  let fp = "HaRe"--GM.mpPath trgtMod
  logm $ "Inserting decl into " ++ fp
  df <- GHC.getSessionDynFlags
  let pRes = parseDecl df fp declStr
  case pRes of
    Left (_spn, str) -> error $ "insertNewDecl: decl parse failed with message:\n" ++ str
    Right (anns, decl@(GHC.L spn _)) -> do
      let oldDecs = GHC.hsmodDecls hsMod
          newParsed = (GHC.L pSpn (hsMod {GHC.hsmodDecls = oldDecs ++ [decl]}))      
      putRefactParsed newParsed anns
      addNewLines 1 decl
      return decl

rmFun :: GHC.RdrName -> RefactGhc ()
rmFun nm = do
  parsed <- getRefactParsed
  let newP = SYB.everywhere (SYB.mkT filterDeclLst) parsed
  putRefactParsed newP mempty
    where filterDeclLst :: [GHC.LHsDecl GHC.RdrName] -> [GHC.LHsDecl GHC.RdrName]
          filterDeclLst = filter (\dec -> not $ isFun dec)
#if __GLASGOW_HASKELL__ <= 710
          isFun (GHC.L _ (GHC.ValD (GHC.FunBind lNm _ _ _ _ _))) = (GHC.unLoc lNm) == nm
#else
          isFun (GHC.L _ (GHC.ValD (GHC.FunBind lNm _ _ _ _))) = (GHC.unLoc lNm) == nm
#endif
          isFun _ = False


replaceFunRhs :: SimpPos -> ParsedLExpr -> RefactGhc ()
replaceFunRhs pos newRhs = do
  parsed <- getRefactParsed
  let rdrNm = locToRdrName pos parsed
  case rdrNm of
    Nothing -> error "replaceFunRhs: Position does not correspond to a binding."
    (Just (GHC.L _ rNm)) -> do
      newParsed <- SYB.everywhereM (SYB.mkM (worker rNm)) parsed
      putRefactParsed newParsed emptyAnns
      logParsedSource "GenApplicative.replaceFunRhs"
  where worker :: GHC.RdrName -> ParsedBind -> RefactGhc ParsedBind
#if __GLASGOW_HASKELL__ <= 710
        worker rNm fBind@(GHC.FunBind (GHC.L _ fNm) _ mg _ _ _)
#else
        worker rNm fBind@(GHC.FunBind (GHC.L _ fNm) mg _ _ _)
#endif
          | fNm == rNm = do
              newMg <- replaceMG mg
              return $ fBind{GHC.fun_matches = newMg}
          | otherwise = return fBind
        worker _ bind = return bind
        replaceMG :: ParsedMatchGroup -> RefactGhc ParsedMatchGroup
        replaceMG mg = do
#if __GLASGOW_HASKELL__ <= 710
          let [(GHC.L l match)] = GHC.mg_alts mg
#else
          let (GHC.L _ [(GHC.L l match)]) = GHC.mg_alts mg
#endif
              oldGrhss = GHC.m_grhss match
              newGrhss = mkGrhss oldGrhss newRhs
              newLMatch = (GHC.L l (match{GHC.m_grhss = newGrhss}))
#if __GLASGOW_HASKELL__ <= 710
          return mg{GHC.mg_alts = [newLMatch]}
#else
          lMatchLst <- locate [newLMatch]
          return mg{GHC.mg_alts = lMatchLst}
#endif
        mkGrhss old newExpr = let [(GHC.L l (GHC.GRHS lst _))] = GHC.grhssGRHSs old in
          old{GHC.grhssGRHSs = [(GHC.L l (GHC.GRHS lst newExpr))]}


--This function will apply the given function to the appropriate type signature element.
--The int denotes which argument the function should be applied to starting at one
--For example when: "traverseTypeSig 2 g"
--Is applied to the signature "f :: Int -> (Int -> String) -> String"
--g will be applied to "(Int -> String)"
--You also need to handle spacing before the type signature element
traverseTypeSig :: Int -> (GHC.LHsType GHC.RdrName -> RefactGhc (GHC.LHsType GHC.RdrName)) -> GHC.Sig GHC.RdrName -> RefactGhc (GHC.Sig GHC.RdrName)
traverseTypeSig argNum f (GHC.TypeSig lst ty rn) = do
  newTy <- comp argNum ty
  return (GHC.TypeSig lst newTy rn)
  where
    comp argNum (GHC.L l (GHC.HsForAllTy flg msp bndrs cntxt ty)) =
      case ty of
        (GHC.L _ (GHC.HsFunTy _ _)) -> comp' argNum ty >>= (\res -> return (GHC.L l (GHC.HsForAllTy flg msp bndrs cntxt res)))
        _ -> f ty >>= (\res -> return (GHC.L l (GHC.HsForAllTy flg msp bndrs cntxt res)))
    comp' 1 (GHC.L l (GHC.HsFunTy lhs rhs)) = do
      resLHS <- f lhs
      let funTy = (GHC.L l (GHC.HsFunTy resLHS rhs))
      zeroDP funTy
      return funTy
    comp' 1 lTy = f lTy 
    comp' n (GHC.L l (GHC.HsFunTy lhs rhs)) = comp' (n-1) rhs >>= (\res -> return (GHC.L l (GHC.HsFunTy lhs res)))
    comp' _ lHsTy@(GHC.L _ ty) = return lHsTy
        
traverseTypeSig _ _ sig = error $ "traverseTypeSig: Unsupported constructor: " ++ show (toConstr sig)
