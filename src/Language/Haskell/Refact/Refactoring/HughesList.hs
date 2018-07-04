{-# LANGUAGE CPP #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.Refact.Refactoring.HughesList
       (hughesList, compHughesList, fastHughesList, compFastHughesList) where

-- import Control.Applicative
-- import Data.Generics as SYB
import Data.Generics.Strafunski.StrategyLib.StrategyLib
-- import qualified Data.Map as M
-- import Data.Maybe (fromMaybe)
-- import Exception
import qualified GhcModCore as GM (Options(..))
import Language.Haskell.GHC.ExactPrint.Parsers
import Language.Haskell.GHC.ExactPrint.Types
import Language.Haskell.GHC.ExactPrint.Utils
import Language.Haskell.Refact.API
import System.Directory

import qualified FastString as GHC
import qualified GHC        as GHC
import qualified Name       as GHC
import qualified RdrName    as GHC

#if __GLASGOW_HASKELL__ >= 800
import qualified TyCoRep as GHC
#else
import qualified TypeRep as GHC
#endif

-- ---------------------------------------------------------------------
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
  absFileName <- normaliseFilePath fileName
  runRefacSession settings cradle (compHughesList absFileName funNm pos argNum)

compHughesList :: FilePath -> String -> SimpPos -> Int -> RefactGhc [ApplyRefacResult]
compHughesList fileName funNm pos argNum = do
  (refRes@((_fp,ismod),_), ()) <- applyRefac (doHughesList fileName funNm pos argNum fullStrs) (RSFile fileName)
  case ismod of
    RefacUnmodifed -> error "Introducing Hughes lists failed"
    RefacModified -> return ()
  return [refRes]

fastHughesList :: RefactSettings -> GM.Options -> FilePath -> String -> SimpPos -> Int -> IO [FilePath]
fastHughesList settings cradle fileName funNm pos argNum = do
  absFileName <- normaliseFilePath fileName
  runRefacSession settings cradle (compFastHughesList absFileName funNm pos argNum)

compFastHughesList :: FilePath -> String -> SimpPos -> Int -> RefactGhc [ApplyRefacResult]
compFastHughesList fileName funNm pos argNum = do
  (refRes@((_fp,ismod),_), ()) <- applyRefac (doHughesList fileName funNm pos argNum fastStrs) (RSFile fileName)
  case ismod of
    RefacUnmodifed -> error "Introducing Hughes lists failed"
    RefacModified -> return ()
  return [refRes]


doHughesList :: FilePath -> String -> SimpPos -> Int -> IsoFuncStrings -> RefactGhc ()
doHughesList fileName funNm pos argNum fStrs = do
  logm $ "doHughesList:entered"
  let mqual = Just "DList"
  loadHList
  addSimpleImportDecl "HughesList.DList" mqual
  ty <- getDListTy mqual
  parsed <- getRefactParsed
  let
    (Just lrdr) = locToRdrName pos parsed
    rdr = GHC.unLoc lrdr
    dlistCon = getTyCon ty
    newFType = resultTypeToDList dlistCon
    (Just funBind) = getHsBind pos parsed
    (Just tySig)   = getTypeSig pos funNm parsed
    newResTy = getResultType ty
  logDataWithAnns "doHughesList:newResTy" newResTy
  iDecl <- dlistImportDecl mqual
  logm "doHughesList:got iDecl"
  iSt   <- getInitState iDecl fStrs "toList" "fromList" mqual newResTy
  logm "doHughesList:got iSt"
  bind' <- isoRefact argNum mqual rdr ty iSt funBind
  logm "doHughesList:got bind'"
  replaceFunBind pos bind'
  newTySig <- fixTypeSig argNum tySig
  replaceTypeSig pos newTySig
  let modQual = case mqual of
                  (Just s) -> s ++ "."
                  Nothing -> ""
  fixClientFunctions modQual (numTypesOfBind funBind) argNum rdr
  addConstructorImport

loadHList :: RefactGhc ()
loadHList = do
  let
    modStr = "HughesList.DList"
    modNm = GHC.mkModuleName modStr
  newTarget <- GHC.guessTarget "HughesList/DList.hs" Nothing
  GHC.addTarget newTarget
  GHC.load (GHC.LoadUpTo modNm)
  logm "Done loading dlist"
  return ()


fixTypeSig :: Int -> GHC.Sig GhcPs -> RefactGhc (GHC.Sig GhcPs)
fixTypeSig argNum =  traverseTypeSig argNum replaceList
  where
    replaceList :: GHC.LHsType GhcPs -> RefactGhc (GHC.LHsType GhcPs)
#if __GLASGOW_HASKELL__ >= 806
    replaceList (GHC.L l (GHC.HsListTy _ innerTy)) = do
#else
    replaceList (GHC.L l (GHC.HsListTy innerTy)) = do
#endif
      let dlistFS = GHC.fsLit "DList"
          dlistUq = GHC.mkVarUnqual dlistFS
      dlistTy <- constructLHsTy dlistUq
#if __GLASGOW_HASKELL__ >= 806
      lTy <- locate (GHC.HsAppTy GHC.noExt dlistTy innerTy)
#else
      lTy <- locate (GHC.HsAppTy dlistTy innerTy)
#endif
      setDP (DP (0,1)) innerTy
      setDP (DP (0,1)) lTy
      return lTy
    replaceList x = return x

addConstructorImport :: RefactGhc ()
addConstructorImport = do
  let modNm = GHC.mkModuleName "HughesList.DList"
      rdr = mkRdrName "DList"
  parsed <- getRefactParsed
  newP <- addImportDecl parsed modNm Nothing False False False Nothing False [rdr]
  putRefactParsed newP mempty

numTypesOfBind :: ParsedBind -> Int
numTypesOfBind bnd = let mg = GHC.fun_matches bnd
#if __GLASGOW_HASKELL__ >= 800
                         ((GHC.L _ match):_) = GHC.unLoc $ GHC.mg_alts mg
#else
                         ((GHC.L _ match):_) = GHC.mg_alts mg
#endif
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
fixClientFunctions modNm totalParams argNum name = if totalParams == argNum
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
          logm $ "ToList being inserted: " ++ showAnnData mempty 3 lLhs
#if __GLASGOW_HASKELL__ >= 806
          locate $ (GHC.HsApp GHC.noExt lLhs parE)
#else
          locate $ (GHC.HsApp lLhs parE)
#endif

#if __GLASGOW_HASKELL__ >= 806
        toListVar' = do
           lNm <- locate (mkRdrName (modNm ++ "toList"))
           return (GHC.HsVar GHC.noExt lNm)
#elif __GLASGOW_HASKELL__ > 710
        toListVar' = do
           lNm <- locate (mkRdrName (modNm ++ "toList"))
           return (GHC.HsVar lNm)
#else
        toListVar = GHC.HsVar (mkRdrName (modNm ++ "toList"))
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
      stopCon :: GHC.HsBind GhcPs -> RefactGhc ParsedBind
      stopCon b@(GHC.FunBind { GHC.fun_id = (GHC.L _ id) }) = if id == nm
--If the bindings name is the function we are looking for then we succeed and the traversal should stop
                                                     then return b
                                                     else mzero
      stopCon b = do
         logm "Other binding constructor matched"
         mzero
      comp :: ParsedLExpr -> RefactGhc ParsedLExpr
      comp lEx = if searchExpr nm (GHC.unLoc lEx)
                 then f lEx
                 else mzero

searchExpr :: GHC.RdrName -> ParsedExpr -> Bool
#if __GLASGOW_HASKELL__ >= 806
searchExpr funNm (GHC.HsApp _ (GHC.L _ (GHC.HsVar _ (GHC.L _ rdr))) _) = rdr == funNm
searchExpr funNm (GHC.HsApp _ lhs _) = searchExpr funNm (GHC.unLoc lhs)
searchExpr funNm (GHC.OpApp _ _ (GHC.L _ (GHC.HsVar _ (GHC.L _ rdr))) _) = rdr == funNm
searchExpr funNm (GHC.OpApp _ _ op _) = searchExpr funNm (GHC.unLoc op)
#elif __GLASGOW_HASKELL__ >= 800
searchExpr funNm (GHC.HsApp (GHC.L _ (GHC.HsVar (GHC.L _ rdr))) _) = rdr == funNm
searchExpr funNm (GHC.HsApp lhs _) = searchExpr funNm (GHC.unLoc lhs)
searchExpr funNm (GHC.OpApp _ (GHC.L _ (GHC.HsVar (GHC.L _ rdr))) _ _) = rdr == funNm
searchExpr funNm (GHC.OpApp _ op _ _) = searchExpr funNm (GHC.unLoc op)
#else
searchExpr funNm (GHC.HsApp (GHC.L _ (GHC.HsVar rdr)) _) = rdr == funNm
searchExpr funNm (GHC.HsApp lhs _) = searchExpr funNm (GHC.unLoc lhs)
searchExpr funNm (GHC.OpApp _ (GHC.L _ (GHC.HsVar rdr)) _ _) = rdr == funNm
searchExpr funNm (GHC.OpApp _ op _ _) = searchExpr funNm (GHC.unLoc op)
#endif
searchExpr _ _ = False

modifyNthParam :: Int -> Int -> (ParsedLExpr -> RefactGhc ParsedLExpr) -> ParsedLExpr -> RefactGhc ParsedLExpr
modifyNthParam paramNums argIndx f app = comp (paramNums - argIndx) app
#if __GLASGOW_HASKELL__ >= 806
  where comp i (GHC.L l (GHC.HsApp x lhs rhs))
          | i == 1 = do
              newRhs <- f rhs
              return (GHC.L l (GHC.HsApp x lhs newRhs))
          | otherwise = do
              newLhs <- comp (i-1) lhs
              return (GHC.L l (GHC.HsApp x newLhs rhs))
#else
  where comp i (GHC.L l (GHC.HsApp lhs rhs))
          | i == 1 = do
              newRhs <- f rhs
              return (GHC.L l (GHC.HsApp lhs newRhs))
          | otherwise = do
              newLhs <- comp (i-1) lhs
              return (GHC.L l (GHC.HsApp newLhs rhs))
#endif

wrapExpr :: GHC.RdrName -> ParsedLExpr -> RefactGhc ParsedLExpr
wrapExpr nm e = do
#if __GLASGOW_HASKELL__ >= 806
  nmL <- locate nm
  let nmE = (GHC.HsVar GHC.noExt nmL)
#elif __GLASGOW_HASKELL__ >= 800
  nmL <- locate nm
  let nmE = (GHC.HsVar nmL)
#else
  let nmE = (GHC.HsVar nm)
#endif
  lNmE <- locate nmE
  addAnnVal lNmE
  zeroDP lNmE
#if __GLASGOW_HASKELL__ >= 806
  let expr = (GHC.HsApp GHC.noExt lNmE e)
#else
  let expr = (GHC.HsApp lNmE e)
#endif
  lE <- locate expr
  wrapInPars lE

resultTypeToDList :: GHC.TyCon -> GHC.Type -> GHC.Type
resultTypeToDList tc = modResultType f
  where f (GHC.TyConApp _ tys) = GHC.TyConApp tc tys

modResultType :: (GHC.Type -> GHC.Type) -> GHC.Type -> GHC.Type
modResultType f (GHC.ForAllTy v ty) = let newTy = modResultType f ty in
                                        (GHC.ForAllTy v newTy)
#if __GLASGOW_HASKELL__ >= 800
#else
modResultType f (GHC.FunTy t1 t2) = let newT2 = comp t2 in
                                      (GHC.FunTy t1 newT2)
  where comp (GHC.FunTy t1 t2) = let newT2 = comp t2 in
                                   (GHC.FunTy t1 newT2)
        comp ty = f ty
#endif
modResultType f ty = f ty

-- | This function inserts a definition and grabs the DList type constructor
--  from that definition's type then deletes the definition from the module
getDListTy :: Maybe String -> RefactGhc GHC.Type
getDListTy mqual = do
  let prefix = case mqual of
        (Just pre) -> pre ++ "."
        Nothing -> ""
  --Should probably work on generating a unique name somehow
  decl <- insertNewDecl $ "emdl = " ++ prefix ++ "empty"
  typeCheckModule
  renamed <- getRefactRenamed
  -- parsed  <- getRefactParsed
  typed   <- getRefactTyped
  let nm = gfromJust "Getting emdl's name" $ getFunName "emdl" renamed
  let mBind = getTypedHsBind (getOcc decl) typed
  ty <- case mBind of
          (Just (GHC.FunBind { GHC.fun_id = lid })) ->
            do let id = GHC.unLoc lid
               return $ GHC.idType id
          Nothing -> error "Could not retrieve DList type"
  rmFun (GHC.mkRdrUnqual (GHC.occName nm))
  return ty
    where
      getOcc :: ParsedLDecl -> GHC.OccName
#if __GLASGOW_HASKELL__ >= 806
      getOcc (GHC.L _ (GHC.ValD _ (GHC.FunBind { GHC.fun_id = nm }))) = GHC.rdrNameOcc $ GHC.unLoc nm
#else
      getOcc (GHC.L _ (GHC.ValD (GHC.FunBind { GHC.fun_id = nm }))) = GHC.rdrNameOcc $ GHC.unLoc nm
#endif

fullStrs :: [(String,String)]
fullStrs = [("[]","empty"),(":","cons"),("++","append"),("concat", "concat"),("replicate","replicate"), ("head","head"),("tail","tail"),("foldr","foldr"),("map","map"), ("unfoldr", "unfoldr")]

fastStrs :: [(String,String)]
fastStrs = [("[]","empty"), (":","cons"),("++", "append")]

dlistImportDecl :: Maybe String -> RefactGhc ParsedLImportDecl
dlistImportDecl mqual = do
  dflags <- GHC.getSessionDynFlags
  let pres = case mqual of
               Nothing -> parseImport dflags "HaRe" "import HughesList.DList"
               (Just q) -> parseImport dflags "HaRe" ("import qualified HughesList.DList as " ++ q)
  (_, dec) <- handleParseResult "dlistImportDecl" pres
  return dec
