{-# LANGUAGE CPP #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.Haskell.Refact.Refactoring.HughesList
       (hughesList, compHughesList) where

import Language.Haskell.Refact.API
import Language.Haskell.Refact.Utils.Types
import qualified Language.Haskell.GhcMod as GM
import System.Directory
import qualified GHC.SYB.Utils as SYB
import Data.Generics as SYB
import qualified GHC as GHC
import qualified FastString as GHC
import qualified RdrName as GHC
import qualified OccName as GHC
import qualified Name as GHC
import qualified Bag as GHC
import Data.Generics.Strafunski.StrategyLib.StrategyLib
import Language.Haskell.GHC.ExactPrint.Types
import Language.Haskell.GHC.ExactPrint.Parsers
import qualified Unique as Unique (mkUniqueGrimily)
import Control.Applicative
import Outputable
import qualified TypeRep as GHC
import qualified Module as GHC
import Data.Maybe (fromMaybe)
import qualified Data.Map as M
import qualified Id as GHC

import qualified TypeRep as GHC
import qualified TyCon as GHC
import qualified HscTypes as GHC
import qualified HscMain as GHC
import qualified RnExpr as GHC
import qualified TcRnDriver as GHC
import qualified ErrUtils as GHC

import Exception
import qualified Unique as GHC
{-
This refactoring will rewrite functions to use Hughes lists (also called difference lists) instead of the standard list interface.

The standard implementation of Hughes lists is here: http://hackage.haskell.org/package/dlist

This refactoring will need to transform the target function(s) as well as any functions that call the refactored function(s).

We can think about this refactoring as a mapping from one interface to another.

E.g.

[] => empty
[x] => singleton


x ++ y => x `append` y
     or
x ++ y => (fromList x) `append` (fromList y)

depending on the type of x and y

TODO: Handle refactoring multiple functions simultaneously

TODO: Figure out strategy for name conflicts. Probably need another optional argument that qualifies the import to Data.DList
   The argument could also be made that the DList import should always be qualified.
-}

hughesList :: RefactSettings -> GM.Options -> FilePath -> String -> SimpPos -> Int -> IO [FilePath]
hughesList settings cradle fileName funNm pos argNum = do
  absFileName <- canonicalizePath fileName
  runRefacSession settings cradle (compHughesList fileName funNm pos argNum)

compHughesList :: FilePath -> String -> SimpPos -> Int -> RefactGhc [ApplyRefacResult]
compHughesList fileName funNm pos argNum = do
  (refRes@((_fp,ismod),_), ()) <- applyRefac (doHughesList fileName funNm pos argNum) (RSFile fileName)
  case ismod of
    RefacUnmodifed -> error "Introducing Hughes lists failed"
    RefacModified -> return ()
  return [refRes]

doHughesList :: FilePath -> String -> SimpPos -> Int -> RefactGhc ()
doHughesList fileName funNm pos argNum = do
  let mqual = Just "DList"
  addSimpleImportDecl "Data.DList" mqual
  ty <- getDListTy mqual
  parsed <- getRefactParsed
  let
    (Just lrdr) = locToRdrName pos parsed
    rdr = GHC.unLoc lrdr
    dlistCon = getTyCon ty
    newFType = resultTypeToDList dlistCon 
    (Just funBind) = getHsBind rdr parsed
    (Just tySig) = getTypeSig pos funNm parsed
    newResTy = getResultType ty
  iSt <- getInitState mqual newResTy
  bind' <- isoRefact argNum mqual rdr ty iSt funBind
  replaceFunBind pos bind'
  newTySig <- fixTypeSig argNum tySig
  replaceTypeSig pos newTySig
  let modQual = case mqual of
                  (Just s) -> s ++ "."
                  Nothing -> ""
  fixClientFunctions modQual (numTypesOfBind funBind) argNum rdr
  addConstructorImport

fixTypeSig :: Int -> GHC.Sig GHC.RdrName -> RefactGhc (GHC.Sig GHC.RdrName)
fixTypeSig argNum =  traverseTypeSig argNum replaceList
  where    
    replaceList :: GHC.LHsType GHC.RdrName -> RefactGhc (GHC.LHsType GHC.RdrName)
    replaceList (GHC.L l (GHC.HsListTy innerTy)) = do
      let dlistFS = GHC.fsLit "DList"
          dlistUq = GHC.mkVarUnqual dlistFS
      dlistTy <- constructLHsTy dlistUq          
      lTy <- locate (GHC.HsAppTy dlistTy innerTy)
      setDP (DP (0,1)) innerTy
      setDP (DP (0,1)) lTy
      return lTy
    replaceList x = return x

addConstructorImport :: RefactGhc ()
addConstructorImport = do
  let modNm = GHC.mkModuleName "Data.DList"
      rdr = mkRdrName "DList"
  parsed <- getRefactParsed
  newP <- addImportDecl parsed modNm Nothing False False False Nothing False [rdr]
  putRefactParsed newP mempty

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
        otherwise -> f ty >>= (\res -> return (GHC.L l (GHC.HsForAllTy flg msp bndrs cntxt res)))
    comp' 1 (GHC.L l (GHC.HsFunTy lhs rhs)) = do
      resLHS <- f lhs
      let funTy = (GHC.L l (GHC.HsFunTy resLHS rhs))
      zeroDP funTy
      return funTy
    comp' 1 lTy = f lTy 
    comp' n (GHC.L l (GHC.HsFunTy lhs rhs)) = comp' (n-1) rhs >>= (\res -> return (GHC.L l (GHC.HsFunTy lhs res)))
    comp' _ lHsTy@(GHC.L _ ty) = return lHsTy
        
traverseTypeSig _ _ sig = error $ "traverseTypeSig: Unsupported constructor: " ++ show (toConstr sig)
         
numTypesOfBind :: ParsedBind -> Int
numTypesOfBind bnd = let mg = GHC.fun_matches bnd
                         ((GHC.L _ match):_) = GHC.mg_alts mg                         
                     in (length (GHC.m_pats match)) + 1
                                                         
--TODO: This will eventually handle all the different ways that
-- this refactoring will need to change functions not part of the main refactoring
-- First tackling: f :: sometype -> [a] ==> f_refact :: sometype -> DList a
-- in this case all uses of f must be wrapped in toList
-- Other patterns:

--                 f :: [a] -> [a] ==> f_refact :: DList a -> DList a
-- Here any list parameters will need to be wrapped in fromList
-- and any uses of f will be wrapped in toList

--                 f :: [a] -> sometype ==> f_refact :: DList a -> sometype
-- Any parameters of type list need to be wrapped in fromList

--TODO 2: Modify this to use the isomorphic refactoring state so that this can
-- Generically refactor types based on their projection and abstraction functions 
fixClientFunctions :: String -> Int -> Int -> GHC.RdrName -> RefactGhc ()
fixClientFunctions modNm totalParams argNum name = if (totalParams == argNum)
                                    then wrapCallsWithToList modNm name
                                    else applyAtCallPoint name (modifyNthParam totalParams argNum (wrapExpr fromLstRdr))
  where fromLstRdr = mkRdrName (modNm ++ "fromList")

--This function handles the case where callsites need to be wrapped with toList
wrapCallsWithToList :: String -> GHC.RdrName -> RefactGhc ()
wrapCallsWithToList modNm name = applyAtCallPoint name comp
  where comp :: ParsedLExpr -> RefactGhc ParsedLExpr
        comp e = do
          zeroDP e
          parE <- wrapInPars e
#if __GLASGOW_HASKELL__ > 710
          toListVar <- toListVar'
#endif
          lLhs <- locate toListVar
          addAnnVal lLhs
          logm $ "ToList being inserted: " ++ SYB.showData SYB.Parser 3 lLhs
          res <- locate $ (GHC.HsApp lLhs parE)
          return res
#if __GLASGOW_HASKELL__ <= 710          
        toListVar = GHC.HsVar (mkRdrName (modNm ++ "toList"))
#else
        toListVar' = do
           lNm <- locate (mkRdrName (modNm ++ "toList"))
           return (GHC.HsVar lNm)
#endif

-- This function takes in a function that transforms the call points of the given identifier
-- The function will be applied over the parsed AST
--applyAtCallPoint assumes that the function handles any changes to annotations itself
applyAtCallPoint :: GHC.RdrName -> (ParsedLExpr -> RefactGhc ParsedLExpr) -> RefactGhc ()
applyAtCallPoint nm f = do
  parsed <- getRefactParsed
  logm "Done with traversal"
  parsed' <- applyTP (stop_tdTP (failTP `adhocTP` stopCon `adhocTP` comp)) parsed
  putRefactParsed parsed' emptyAnns
    where
      stopCon :: GHC.HsBind GHC.RdrName -> RefactGhc ParsedBind
#if __GLASGOW_HASKELL__ <= 710
      stopCon b@(GHC.FunBind (GHC.L _ id) _ _ _ _ _) = if id == nm
#else
      stopCon b@(GHC.FunBind (GHC.L _ id) _ _ _ _) = if id == nm                                                   
#endif
                                                     then do
--If the bindings name is the function we are looking for then we succeed and the traversal should stop
                                                       return b
                                                     else do
                                                       mzero
      stopCon b = do
         logm "Other binding constructor matched"
         mzero
      comp :: ParsedLExpr -> RefactGhc ParsedLExpr
      comp lEx = if searchExpr nm (GHC.unLoc lEx)
                 then do
                    f lEx                   
                 else do
                    mzero 

searchExpr :: GHC.RdrName -> ParsedExpr -> Bool
searchExpr funNm (GHC.HsApp (GHC.L _ (GHC.HsVar rdr)) _) = rdr == funNm
searchExpr funNm (GHC.HsApp lhs _) = searchExpr funNm (GHC.unLoc lhs)
searchExpr funNm (GHC.OpApp _ (GHC.L _ (GHC.HsVar rdr)) _ _) = rdr == funNm
searchExpr funNm (GHC.OpApp _ op _ _) = searchExpr funNm (GHC.unLoc op)
searchExpr _ _ = False

modifyNthParam :: Int -> Int -> (ParsedLExpr -> RefactGhc ParsedLExpr) -> ParsedLExpr -> RefactGhc ParsedLExpr
modifyNthParam paramNums argIndx f app = comp (paramNums - argIndx) app
  where comp i (GHC.L l (GHC.HsApp lhs rhs))
          | i == 1 = do
              newRhs <- f rhs
              return (GHC.L l (GHC.HsApp lhs newRhs))
          | otherwise = do
              newLhs <- comp (i-1) lhs
              return (GHC.L l (GHC.HsApp newLhs rhs))

wrapExpr :: GHC.RdrName -> ParsedLExpr -> RefactGhc ParsedLExpr
wrapExpr nm e = do
  lNmE <- locate nmE
  addAnnVal lNmE
  zeroDP lNmE
  let expr = (GHC.HsApp lNmE e)
  lE <- locate expr
  wrapInPars lE
    where nmE = (GHC.HsVar nm)

resultTypeToDList :: GHC.TyCon -> GHC.Type -> GHC.Type
resultTypeToDList tc = modResultType f
  where f (GHC.TyConApp _ tys) = GHC.TyConApp tc tys

modResultType :: (GHC.Type -> GHC.Type) -> GHC.Type -> GHC.Type
modResultType f (GHC.ForAllTy v ty) = let newTy = modResultType f ty in
                                        (GHC.ForAllTy v newTy)
modResultType f (GHC.FunTy t1 t2) = let newT2 = comp t2 in
                                      (GHC.FunTy t1 newT2)
  where comp (GHC.FunTy t1 t2) = let newT2 = comp t2 in
                                   (GHC.FunTy t1 newT2)
        comp ty = f ty
modResultType f ty = f ty

--This function inserts a definition and grabs the DList type constructor
--From that definition's type then deletes the definition from the module
getDListTy :: Maybe String -> RefactGhc GHC.Type
getDListTy mqual = do
  let prefix = case mqual of
        (Just pre) -> pre ++ "."
        Nothing -> ""
  --Should probably work on generating a unique name somehow
  decl <- insertNewDecl $ "emdl = " ++ prefix ++ "empty"  
  typeCheckModule
  renamed <- getRefactRenamed
  parsed <- getRefactParsed
  typed <- getRefactTyped
  let nm = gfromJust "Getting emdl's name" $ getFunName "emdl" renamed
  let mBind = getTypedHsBind (getOcc decl) typed
  ty <- case mBind of
          (Just (GHC.FunBind lid _ _ _ _ _)) ->
            do let id = GHC.unLoc lid
               return $ GHC.idType id               
          Nothing -> error "Could not retrieve DList type"
  rmFun (GHC.mkRdrUnqual (GHC.occName nm))
  return ty
    where
      getOcc :: ParsedLDecl -> GHC.OccName
      getOcc (GHC.L _ (GHC.ValD (GHC.FunBind nm _ _ _ _ _))) = GHC.rdrNameOcc $ GHC.unLoc nm      

getInitState :: Maybe String -> GHC.Type -> RefactGhc IsoRefactState
getInitState mqual ty = do
  iDecl <- dlistImportDecl mqual
  funcs <- mkFuncs iDecl "toList" "fromList" full_strs mqual
  return $ IsoState funcs [Just ty]

{-
hListFuncs :: Maybe String -> RefactGhc IsomorphicFuncs
hListFuncs mqual = do
  fs <- funs
  return $ IF {
    projFun = mkRdr (GHC.mkVarOcc "toList"),
    absFun = mkRdr (GHC.mkVarOcc "fromList"),
    eqFuns = fs
    }
  where
    mkRdr = case mqual of
      Nothing -> GHC.mkRdrUnqual
      (Just q) -> (\nm -> GHC.mkRdrQual (GHC.mkModuleName q) nm)
    funs :: RefactGhc (M.Map String (GHC.RdrName, GHC.Type))
    funs = do
      kvs <- mkLst
      return $ M.fromList kvs
    mkLst = mapM f full_strs
    f :: (String,String) -> RefactGhc (String,(GHC.RdrName, GHC.Type))
    f (s1, s2) = do
      let o2 = GHC.mkVarOcc s2
          rdr = mkRdr o2
      dec <- dlistImportDecl mqual
      lExpr <- locate (GHC.HsVar rdr)
      ((wrns, errs), mty) <- tcExprInTargetMod dec lExpr
      case mty of
        Nothing -> error $ "TypeChecking failed: " ++ GHC.foldBag (++) (\e -> show e ++ "\n") "" errs
        (Just ty) -> return (s1,(rdr,ty))
-}

full_strs = [("[]","empty"),(":","cons"),("++","append"),("concat", "concat"),("replicate","replicate"), ("head","head"),("tail","tail"),("foldr","foldr"),("map","map"), ("unfoldr", "unfoldr")]

dlistImportDecl :: Maybe String -> RefactGhc ParsedLImportDecl
dlistImportDecl mqual = do
  dflags <- GHC.getSessionDynFlags
  let pres = case mqual of
               Nothing -> parseImport dflags "HaRe" "import Data.DList"
               (Just q) -> parseImport dflags "HaRe" ("import qualified Data.DList as " ++ q)
  (_, dec) <- handleParseResult "dlistImportDecl" pres
  return dec

tcExprInTargetMod :: GHC.LImportDecl GHC.RdrName -> ParsedLExpr -> RefactGhc (GHC.Messages, Maybe GHC.Type)
tcExprInTargetMod idecl ex = do
  pm <- getRefactParsedMod
  oldCntx <- GHC.getContext
  let
    nm = GHC.unLoc . GHC.ideclName $ (GHC.unLoc idecl)
    lst = (GHC.IIDecl (GHC.unLoc idecl)):oldCntx --(GHC.IIModule nm):oldCntx
  GHC.setContext lst
  env <- GHC.getSession
  liftIO $ GHC.tcRnExpr env ex
    where addImps decs ms = let old = GHC.ms_textual_imps ms in
            ms {GHC.ms_textual_imps = old ++ [decs]}


