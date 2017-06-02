{-# LANGUAGE CPP #-}
{-# LANGUAGE ImpredicativeTypes #-}
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
import Language.Haskell.GHC.ExactPrint.Types
import Language.Haskell.GHC.ExactPrint.Parsers
import qualified Unique as Unique (mkUniqueGrimily)
import Data.Generics.Strafunski.StrategyLib.StrategyLib
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

import Outputable

import Control.Monad.State
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
  --Eventually should extract the qualifier as an argument so that people can choose their own.
  logm "Adding importDecl"
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
  newBind <- fixFunBind argNum rdr funBind
  bind' <- isoRefact argNum mqual rdr funBind
  replaceFunBind pos newBind
  newTySig <- fixTypeSig argNum tySig
  replaceTypeSig pos newTySig
  let modQual = case mqual of
                  (Just s) -> s ++ "."
                  Nothing -> ""
  fixClientFunctions modQual (numTypesOfBind funBind) argNum rdr
  addConstructorImport


--Going to assume it's only the result type that will be modified right now
isoRefact :: Int -> Maybe String -> GHC.RdrName -> ParsedBind -> RefactGhc ParsedBind
isoRefact _ mqual funNm bnd = do
  tca <- getDListTy mqual

  typedS <- getRefactTyped
  let m_fTy = getTypeFromRdr funNm typedS
      dlistCon = getTyCon tca
      fTy = gfromJust "isoRefact: getting function type" m_fTy
      newFTy = resultTypeToDList dlistCon fTy
      newResTy = getResultType newFTy
      paramTys = breakType newFTy
  logm $ "breakType: " ++ show (map (printType 3) paramTys)
  isoF <- hListFuncs mqual
  error "isoRefact isn't done yet"

modMGAltsRHS :: (ParsedLExpr -> RefactGhc ParsedLExpr) -> ParsedBind -> RefactGhc ParsedBind
modMGAltsRHS f = SYB.everywhereM (SYB.mkM comp)
  where comp :: GHC.GRHS GHC.RdrName ParsedLExpr -> RefactGhc (GHC.GRHS GHC.RdrName ParsedLExpr)
        comp (GHC.GRHS lst expr) = do
          newExpr <- f expr
          return (GHC.GRHS lst newExpr) 

-- Breaks up a function type into a list of the types of the parameters
breakType :: GHC.Type -> [GHC.Type]
breakType ty = breakType' (consumeOuterForAlls ty)
  where breakType' (GHC.FunTy lTy rTy) = breakType' lTy ++ breakType' rTy
        breakType' ty = [ty]

--The removes the for all types that are on the outside of a type with type variables
consumeOuterForAlls :: GHC.Type -> GHC.Type
consumeOuterForAlls (GHC.ForAllTy _ ty) = consumeOuterForAlls ty
consumeOuterForAlls ty = ty

getTypeFromRdr :: (Data a) => GHC.RdrName -> a -> Maybe GHC.Type
getTypeFromRdr nm a = SYB.something (Nothing `SYB.mkQ` comp) a
  where comp :: GHC.HsBind GHC.Id -> Maybe GHC.Type
        comp (GHC.FunBind (GHC.L _ id) _ _ _ _ _)
          | occNm == (GHC.occName (GHC.idName id)) = Just (GHC.idType id)
          | otherwise = Nothing
        comp _ = Nothing
        occNm = (GHC.occName nm)

getTyCon :: GHC.Type -> GHC.TyCon
getTyCon (GHC.TyConApp tc _) = tc

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
         

fixFunBind :: Int -> GHC.RdrName -> ParsedBind -> RefactGhc ParsedBind
fixFunBind argNum funRdr bind = do
  let numArgs = numTypesOfBind bind
  if argNum < numArgs
    then wrapBindParamWithToLst argNum bind
    else outputParameterBecomesDList bind

wrapBindParamWithToLst :: Int -> ParsedBind -> RefactGhc ParsedBind
wrapBindParamWithToLst = wrapBindParamWithFun (mkRdrName "toList")

wrapBindParamWithFun :: GHC.RdrName -> Int -> ParsedBind -> RefactGhc ParsedBind
wrapBindParamWithFun funNm argNum bind = do
  let argNames = getArgRdrNms argNum bind
  logm $ "Arg names: " ++ show (SYB.showData SYB.Parser 3 argNames)
  modifyMatchGroup argNames bind
  where
    modifyMatchGroup :: [Maybe GHC.RdrName] -> ParsedBind -> RefactGhc ParsedBind
    modifyMatchGroup aNms bind = do
          let mg = GHC.fun_matches bind
          newAlts <- mapM handleLMatch (zip aNms (GHC.mg_alts mg))
          let newMG = mg {GHC.mg_alts = newAlts}
          return $ bind {GHC.fun_matches = newMG}
    handleLMatch :: (Maybe GHC.RdrName, ParsedLMatch) -> RefactGhc ParsedLMatch
    handleLMatch (Nothing, m ) = return m
    handleLMatch ((Just rdr), m) = SYB.everywhereM (SYB.mkM (wrapRdr funNm rdr)) m


wrapRdr :: GHC.RdrName -> GHC.RdrName -> ParsedLExpr -> RefactGhc ParsedLExpr
wrapRdr funNm rdr e@(GHC.L _ (GHC.HsVar nm))
  | rdr /= nm = return e
  | otherwise = do
      let toLstExpr = GHC.HsVar funNm
      lToLst <- locate toLstExpr
      addAnnVal lToLst
      zeroDP lToLst
      app <- locate (GHC.HsApp lToLst e)
      pe <- wrapInPars app
      return pe

wrapRdr _ _ e = return e

numTypesOfBind :: ParsedBind -> Int
numTypesOfBind bnd = let mg = GHC.fun_matches bnd
                         ((GHC.L _ match):_) = GHC.mg_alts mg                         
                     in (length (GHC.m_pats match)) + 1
                      
                 

getArgRdrNms :: Int -> GHC.HsBind GHC.RdrName -> [Maybe GHC.RdrName]
getArgRdrNms argNum bind = let mg = GHC.fun_matches bind
                               matches = GHC.mg_alts mg
  in map (\(GHC.L _ match) -> comp match) matches
  where
    comp :: ParsedMatch -> Maybe GHC.RdrName
    comp (GHC.Match _ pats _ _) = findRdr (pats !! (argNum-1))
    findRdr (GHC.L _ (GHC.VarPat rdr)) = Just rdr
    findRdr (GHC.L _ (GHC.AsPat (GHC.L _ rdr) _)) = Just rdr
    findRdr _ = Nothing

outputParameterBecomesDList :: GHC.HsBind GHC.RdrName -> RefactGhc (GHC.HsBind GHC.RdrName)
outputParameterBecomesDList bind = do
  SYB.everywhereM (SYB.mkM comp) bind
  where comp :: ParsedLExpr -> RefactGhc ParsedLExpr
#if __GLASGOW_HASKELL__ <= 710
        comp lVar@(GHC.L l (GHC.HsVar vNm))
#else
        comp lVar@(GHC.L l (GHC.HsVar (GHC.L _ vNm)))
#endif
          | (GHC.isExact vNm) && (GHC.occNameString (GHC.rdrNameOcc vNm)) == "[]" =
            do
              let emptyRdr = GHC.mkVarUnqual (GHC.fsLit "empty")
              newVar <- constructHsVar emptyRdr
              return newVar
          | (GHC.occNameString (GHC.rdrNameOcc vNm)) == "++" =
            do              
              newVar <- constructHsVar appendRdr
              addBackquotes newVar
              return newVar
          | otherwise = return lVar
        comp lit@(GHC.L _ (GHC.ExplicitList _ _ exprs)) = do
          expr <- if (length exprs) == 1
                  then do
                     singleton <- constructHsVar singletonRdr
                     addAnnVal singleton
                     zeroDP singleton
                     let right = (exprs !! 0)
                     setDP (DP (0,1)) right
                     return (GHC.HsApp singleton right)
                  else do
                     fList <- constructHsVar fromListRdr
                     return (GHC.HsApp fList lit)
          lExpr <- locate expr
          zeroDP lExpr
          pE <- wrapInPars lExpr
          zeroDP pE
          return pE
        comp x = return x
        singletonRdr = mkRdrName "singleton"
        fromListRdr = mkRdrName "fromList"
        appendRdr = mkRdrName "append"                     


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


printTypeDebug :: RefactGhc ()
printTypeDebug = do
  ts <- getRefactTyped  
  SYB.everywhereM (SYB.mkM comp) ts
  return ()
    where
      mapRdr = mkRdrName "replicate"
      comp :: GHC.HsExpr GHC.Id -> RefactGhc (GHC.HsExpr GHC.Id)
      comp e@(GHC.HsVar id)
        | (GHC.getOccName id) == (GHC.rdrNameOcc mapRdr) = do
            logm "==========Found replicate========"
            let ty = GHC.idType id
            logm $ SYB.showData SYB.TypeChecker 3 ty
            return e
        | otherwise = return e
      comp e = return e

--This takes in a type and returns its result type
getResultType :: GHC.Type -> GHC.Type
--This case is here because below top level bindings any types with type variables will be
--explicitly polymorphic once we get past all of the polymorphic types we will either find
--some other constructor and in that case we've found the result type
--if we find a FunTy constructor we continue to descent the type down the RHS
--until we find a non-FunTy constructor 
getResultType (GHC.ForAllTy _ ty) = getResultType ty
getResultType (GHC.FunTy _ ty) = comp ty
  where comp :: GHC.Type -> GHC.Type
        comp (GHC.FunTy _ ty) = comp ty
        comp ty = ty
getResultType ty = ty

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

--NOTE: May want to change this to use GHC.Name
data IsomorphicFuncs = IF {
  projFun :: GHC.OccName,
  absFun :: GHC.OccName,
  eqFuns :: M.Map GHC.OccName (GHC.OccName, GHC.Type)
  }        

data IsoRefactState = IsoState {
  funcs :: IsomorphicFuncs,
  typeQueue :: [GHC.Type]
                               }

type IsoRefact = StateT IsoRefactState RefactGhc
                     
hListFuncs :: Maybe String -> RefactGhc IsomorphicFuncs
hListFuncs mqual = do
  fs <- funs
  return $ IF {
    projFun = GHC.mkVarOcc $ qual ++ "toList",
    absFun = GHC.mkVarOcc $ qual ++ "fromList",
    eqFuns = fs
    }
  where
    qual = case mqual of
      Nothing -> ""
      (Just q) -> q ++  "."
    funs :: RefactGhc (M.Map GHC.OccName (GHC.OccName, GHC.Type))
    funs = do
      kvs <- mkLst
      return $ M.fromList kvs
    mkLst = mapM f strs
    f :: (String,String) -> RefactGhc (GHC.OccName,(GHC.OccName, GHC.Type))
    f (s1, s2) = do
      let o1 = GHC.mkVarOcc s1
          o2 = GHC.mkVarOcc s2
          rdr = case mqual of
                  Nothing -> GHC.mkRdrUnqual o2
                  (Just mdNm) -> GHC.mkRdrQual (GHC.mkModuleName mdNm) o2
      dec <- dlistImportDecl mqual
      lExpr <- locate (GHC.HsVar rdr)
      ((wrns, errs), mty) <- tcExprInTargetMod dec lExpr
      case mty of
        Nothing -> error $ "TypeChecking failed: " ++ GHC.foldBag (++) (\e -> show e ++ "\n") "" errs
        (Just ty) -> return (o1,(o2,ty))
    strs = [("[]","empty"),("(:)","cons"),("(++)","append"),("concat", "concat"),("replicate","replicate"), ("head","head"),("tail","tail"),("foldr","foldr"),("map","map"), ("unfoldr", "unfoldr")]

dlistImportDecl :: Maybe String -> RefactGhc (GHC.LImportDecl GHC.RdrName)
dlistImportDecl mqual = do
  dflags <- GHC.getSessionDynFlags
  let pres = case mqual of
               Nothing -> parseImport dflags "HaRe" "import Data.DList"
               (Just q) -> parseImport dflags "HaRe" ("import qualified Data.DList as " ++ q)
  (_, dec) <- handleParseResult "dlistImportDecl" pres
  return dec

{-
tcPExpr :: ParsedLExpr -> RefactGhc (GHC.Messages, Maybe GHC.Type)
tcPExpr ex = do
  hsc_env <- GHC.getSession
  tcPExprWithEnv hsc_env ex
  -}
tcPExprWithEnv :: GHC.HscEnv -> ParsedLExpr -> RefactGhc (GHC.Messages, Maybe GHC.Type)
tcPExprWithEnv env ex = liftIO $ GHC.tcRnExpr env ex


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

  

printType :: Int -> GHC.Type -> String
printType n (GHC.TyVarTy v) = indent n ++ "(TyVarTy " ++ SYB.showData SYB.TypeChecker (n+1) v ++ ")"
printType n (GHC.AppTy t1 t2) = indent n ++ "(AppTy\n" ++ (printType (n+1) t1) ++ "\n" ++ (printType (n+1) t2) ++ "\n)"
printType n (GHC.TyConApp tc lst) = indent n ++ "(TyConApp: " ++ (printCon tc) ++
                                (foldl (\rst ty -> rst ++ "\n" ++ (printType (n+1) ty)) "" lst) ++ ")"
printType n (GHC.FunTy t1 t2) = indent n ++ "(FunTy " ++ (printType (n+1) t1) ++ indent n ++ "->" ++ (printType (n+1) t2) ++ ")"
printType n (GHC.ForAllTy v ty) = indent n ++ "(ForAllTy: " ++ (SYB.showData SYB.TypeChecker (n+1) v) ++ "\n" ++ (printType (n+1) ty) ++ "\n)"
printType n (GHC.LitTy tl) = indent n ++ "(LitTy: " ++ showTyLit tl ++ ")"


showTyLit :: GHC.TyLit -> String
showTyLit (GHC.NumTyLit i) = show i
showTyLit (GHC.StrTyLit fs) = show fs


printCon :: GHC.TyCon -> String
printCon tc
  | GHC.isFunTyCon tc = "FunTyCon: " ++ shwTc tc
  | GHC.isAlgTyCon tc = "AlgTyCon: " ++ shwTc tc
  | otherwise = "TyCon: " ++ (show $ toConstr tc) ++ "|" ++ shwTc tc

shwTc = SYB.showSDoc_ . ppr
indent i = "\n" ++ replicate i ' '

