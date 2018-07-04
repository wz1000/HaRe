{-#LANGUAGE CPP #-}
module Language.Haskell.Refact.Utils.Isomorphic
  (isoRefact
 , IsomorphicFuncs(..)
 , IsoRefactState(..)
 , IsoRefact
 , runIsoRefact
 , getTyCon
 , getResultType
 , mkFuncs
 , IsoFuncStrings
 , getInitState) where

import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.MonadFunctions
import Language.Haskell.Refact.Utils.Transform
import Language.Haskell.Refact.Utils.ExactPrint
import Language.Haskell.Refact.Utils.Synonyms
import Language.Haskell.Refact.Utils.TypeUtils
-- import Language.Haskell.Refact.Utils.Types
import Language.Haskell.Refact.Utils.Query
import qualified GHC as GHC
import qualified RdrName as GHC
import qualified OccName as GHC
import qualified Id as GHC
#if __GLASGOW_HASKELL__ <= 710
import qualified TypeRep as GHC
#else
import qualified TyCoRep as GHC
#endif
import qualified TyCon as GHC
import qualified TcRnDriver as GHC
import qualified ErrUtils as GHC
import qualified Bag as GHC
import qualified Unique as GHC
import Data.Generics as SYB
import qualified Data.Map as M
import Control.Monad.State
import Language.Haskell.GHC.ExactPrint.Types
import Language.Haskell.GHC.ExactPrint.Utils
import Outputable
import Data.Generics.Strafunski.StrategyLib.StrategyLib


-- Going to assume it's only the result type that will be modified right now
isoRefact :: Int -> Maybe String -> GHC.RdrName -> GHC.Type -> IsoRefactState
          -> GHC.HsBind GhcPs -> RefactGhc (GHC.HsBind GhcPs)
isoRefact argNum mqual funNm newFTy iST bnd = do
  -- typedS <- getRefactTyped
  -- let m_fTy = getTypeFromRdr funNm typedS
  --     fTy = gfromJust "isoRefact: getting function type" m_fTy
  --     newResTy = getResultType newFTy
  --     paramTys = breakType newFTy
  newBnd <- modMGAltsRHS (\e -> runIsoRefact (doIsoRefact e) iST) bnd
  return newBnd

isoDone :: IsoRefact Bool
isoDone = do
  st <- get
  case (typeQueue st) of
    [] -> return True
    _  -> return False

skipCurrent :: IsoRefact Bool
skipCurrent = do
  st <- get
  let currType = head (typeQueue st)
  case currType of
    Nothing -> do
      popTQ
      return True
    Just _ -> return False

doIsoRefact :: GHC.LHsExpr GhcPs -> IsoRefact (GHC.LHsExpr GhcPs)
doIsoRefact expr = do
  lift $ logDataWithAnns "doIsoRefact" expr
  b1 <- isoDone
  b2 <- skipCurrent
  if b1 || b2
    then do
      lift $ logm "Skipping this expr: "
      lift $ logm (showAnnData mempty 3 expr)
      return expr
    else doIsoRefact' expr
  where doIsoRefact' :: GHC.LHsExpr GhcPs -> IsoRefact (GHC.LHsExpr GhcPs)
#if __GLASGOW_HASKELL__ >= 806
        doIsoRefact' (GHC.L l (GHC.HsApp x le re)) = do
#else
        doIsoRefact' (GHC.L l (GHC.HsApp le re)) = do
#endif
          le' <- doIsoRefact le
          wrapWithAbs <- shouldInsertAbs
          re' <- doIsoRefact re
          lift $ logm "POST RHS REFACT IN APP CASE"
#if __GLASGOW_HASKELL__ >= 806
          let newApp = (GHC.L l (GHC.HsApp x le' re'))
#else
          let newApp = (GHC.L l (GHC.HsApp le' re'))
#endif
          if wrapWithAbs
            then do
            absRdr <- getAbsFun
#if __GLASGOW_HASKELL__ >= 806
            absRdrL <- lift $ locate absRdr
            let var = GHC.HsVar GHC.noExt absRdrL
#elif __GLASGOW_HASKELL__ >= 800
            absRdrL <- lift $ locate absRdr
            let var = GHC.HsVar absRdrL
#else
            let var = GHC.HsVar absRdr
#endif
            pApp <- lift $ wrapInPars newApp
            lVar <- lift $ locate var
            lift $ addAnnVal lVar
#if __GLASGOW_HASKELL__ >= 806
            let fullApp = GHC.HsApp x lVar pApp
#else
            let fullApp = GHC.HsApp lVar pApp
#endif
            lift $ locate fullApp
            else return newApp
#if __GLASGOW_HASKELL__ >= 806
        doIsoRefact' (GHC.L l (GHC.OpApp x le op re)) = do
#else
        doIsoRefact' (GHC.L l (GHC.OpApp le op rn re)) = do
#endif
          op' <- doIsoRefact op
          lift $ addBackquotes op'
          le' <- doIsoRefact le
          re' <- doIsoRefact re
#if __GLASGOW_HASKELL__ >= 806
          return (GHC.L l (GHC.OpApp x le' op' re'))
#else
          return (GHC.L l (GHC.OpApp le' op' rn re'))
#endif
        doIsoRefact' lam@(GHC.L _ (GHC.HsLam {})) = do
          lift $ logm "Found lambda"
          lift $ logm (showAnnData mempty 3 lam)
          return lam
#if __GLASGOW_HASKELL__ >= 806
        doIsoRefact' var@(GHC.L l (GHC.HsVar _ (GHC.L lr rdr))) = do
#elif __GLASGOW_HASKELL__ >= 800
        doIsoRefact' var@(GHC.L l (GHC.HsVar (GHC.L lr rdr))) = do
#else
        doIsoRefact' var@(GHC.L l (GHC.HsVar rdr)) = do
#endif
          st <- get
          let tq = typeQueue st
              fs = funcs st
          -- typed <- lift getRefactTyped
          mId <- lift (getIdFromVar var)
          lift $ logDataWithAnns "doIsoRefact'mId" mId
          let id' = gfromJust ("Tried to get id for: " ++ showAnnData mempty 3 rdr) mId
              goalType = gfromJust "Getting goal type" $ head tq
              currTy = GHC.idType id'
              -- currRes = getResultType currTy
              keyOcc = GHC.rdrNameOcc rdr
              mVal = (GHC.occNameString keyOcc) `M.lookup` (eqFuns fs)
          case mVal of
            Nothing -> do
              -- If this happens we have a problem and need to insert a fromList higher up the tree
              -- Need to figure out how to handle this case
              lift $ logm $ "No map on var: " ++ (showAnnData mempty 3 keyOcc) ++ ": " ++ show (GHC.getUnique keyOcc)
              --pop the current goal type
              popTQ
              --Since we aren't changing the function we don't have to modify any of the right sub-trees
              dontSearchSubTrees currTy
              --Then wrap the whole application with the abstraction function
              lift $ logm "Nothing case of mVal"
              printQueue
              insertAbsToT
              return var
            (Just (oNm, ty)) -> do
              if compType (getResultType ty) goalType
                then do
                let changedTypes = typeDifference ty currTy
#if __GLASGOW_HASKELL__ >= 806
                    newE = (GHC.L l (GHC.HsVar GHC.noExt (GHC.L lr oNm)))
#elif __GLASGOW_HASKELL__ >= 800
                    newE = (GHC.L l (GHC.HsVar (GHC.L lr oNm)))
#else
                    newE = (GHC.L l (GHC.HsVar oNm))
#endif
                lift $ logm $ "Swapping " ++  (showAnnData mempty 3 keyOcc)
                lift $ logm $ "CURRENT TYPE: \n" ++ showType 3 currTy
                lift $ logm $ "NEW VAR TYPE: \n" ++ showType 3 ty
--                mapM_ (\t -> lift $ logm (SYB.showData SYB.TypeChecker 3 t)) changedTypes
                oldAnns <- lift fetchAnnsFinal
                case M.lookup (mkAnnKey var) oldAnns of
                  Nothing -> lift (mergeRefactAnns $ copyAnn var newE oldAnns)
                  Just v -> do
                    let dp = annEntryDelta v
                    lift $ addAnnValWithDP newE dp
                popTQ
                addToTQ changedTypes
                return newE
                else do
                lift $ logm $ "The goal type of " ++ (showOutputable oNm) ++ "didn't match."
                lift $ logm (showType 3 (getResultType ty))
                lift $ logm (showType 3 (getResultType goalType))
                return var
--- TODO: This case is still specific to the hughes list. Need to figure out how to extend this function dynamically.
        doIsoRefact' eLst@(GHC.L _ (GHC.ExplicitList _ty _mSyn lst)) = do
          if (length lst) == 1
            then do
            -- st <- get
            let -- fs = funcs st
                singletonRdr = mkQualifiedRdrName (GHC.mkModuleName "DList") "singleton"
#if __GLASGOW_HASKELL__ >= 806
            singletonRdrL <- lift $ locate singletonRdr
            let singletonVar = (GHC.HsVar GHC.noExt singletonRdrL)
#elif __GLASGOW_HASKELL__ >= 800
            singletonRdrL <- lift $ locate singletonRdr
            let singletonVar = (GHC.HsVar singletonRdrL)
#else
                singletonVar = (GHC.HsVar singletonRdr)
#endif
            lVar <- lift $ locate singletonVar
            lift $ addAnnVal lVar
            lift $ zeroDP lVar
            let rhs = head lst
            lift $ setDP (DP (0,1)) rhs
#if __GLASGOW_HASKELL__ >= 806
            lApp <- lift $ locate (GHC.HsApp GHC.noExt lVar rhs)
#else
            lApp <- lift $ locate (GHC.HsApp lVar rhs)
#endif
            parApp <- lift $ wrapInPars lApp
            return parApp
            else do
            st <- get
            let fs = funcs st
                absRdr = absFun fs
#if __GLASGOW_HASKELL__ >= 806
            absRdrL <- lift $ locate absRdr
            lVar <- lift $ locate (GHC.HsVar GHC.noExt absRdrL)
#elif __GLASGOW_HASKELL__ >= 800
            absRdrL <- lift $ locate absRdr
            lVar <- lift $ locate (GHC.HsVar absRdrL)
#else
            lVar <- lift $ locate (GHC.HsVar absRdr)
#endif
#if __GLASGOW_HASKELL__ >= 806
            lApp <- lift $ locate (GHC.HsApp GHC.noExt lVar eLst)
#else
            lApp <- lift $ locate (GHC.HsApp lVar eLst)
#endif
            _ <- lift $ wrapInPars lApp
            return lApp
        doIsoRefact' ex = gmapM (SYB.mkM doIsoRefact) ex

typeDifference :: GHC.Type -> GHC.Type -> [Maybe GHC.Type]
typeDifference new old = let lst1 = tail $ breakType new
                             lst2 = tail $ breakType old in
  zipWith (\x y -> if (x `compType` y)
                   then Nothing
                   else (Just x)) lst1 lst2

dontSearchSubTrees :: GHC.Type -> IsoRefact ()
dontSearchSubTrees ty = let argNums = (length (breakType ty)) - 1 in
  addToTQ (replicate argNums Nothing)

popTQ :: IsoRefact ()
popTQ = do
  st <- get
  put $ st {typeQueue = tail (typeQueue st)}

addToTQ :: [Maybe GHC.Type] -> IsoRefact ()
addToTQ lst = do
  st <- get
  let tq = typeQueue st
  put $ st {typeQueue = lst ++ tq}

-- Breaks up a function type into a list of the types of the parameters
breakType :: GHC.Type -> [GHC.Type]
breakType ty = breakType' (consumeOuterForAlls ty)
  where
#if __GLASGOW_HASKELL__ >= 800
    breakType' (GHC.ForAllTy _lTy rTy) = breakType' rTy
#else
    breakType' (GHC.FunTy lTy rTy) = breakType' lTy ++ breakType' rTy
#endif
    breakType' t = [t]

{-
NOTE: When do we catch if the goal type is nothing??? Does this happen when we find a var or when
we descend subtrees?

From here we need to figure out if the var has a possible match from the map,
if it does then we need to see if the result type of the dlist function is the goalType
if it is then we can do the swap, we need to check which of the parameters of the new function changes type
from left to right those types are added to the type queue
-}

compType :: GHC.Type -> GHC.Type -> Bool
compType (GHC.TyVarTy _v1) (GHC.TyVarTy _v2) = True --v1 == v2
compType (GHC.TyVarTy _) _ = True
compType _ (GHC.TyVarTy _) = True --v1 == v2
compType (GHC.AppTy l1 l2) (GHC.AppTy r1 r2) = compType l1 r1 && compType l2 r2
compType (GHC.TyConApp tc1 lst1) (GHC.TyConApp tc2 lst2) = tc1 == tc2 && (and (zipWith compType lst1 lst2))
#if __GLASGOW_HASKELL__ >= 800
#else
compType (GHC.FunTy l1 l2) (GHC.FunTy r1 r2) = compType l1 r1 && compType l2 r2
#endif
compType (GHC.ForAllTy _v1 lTy) (GHC.ForAllTy _v2 rTy) = compType lTy rTy
compType (GHC.LitTy l) (GHC.LitTy r) = l == r
compType _ _ = False

--The removes the for all types that are on the outside of a type with type variables
consumeOuterForAlls :: GHC.Type -> GHC.Type
consumeOuterForAlls (GHC.ForAllTy _ ty) = consumeOuterForAlls ty
consumeOuterForAlls ty = ty

--NOTE: May want to change this to use GHC.Name
data IsomorphicFuncs = IF {
  projFun :: GHC.RdrName,
  absFun  :: GHC.RdrName,
  eqFuns  :: M.Map String (GHC.RdrName, GHC.Type)
  }

data IsoRefactState = IsoState {
  funcs     :: IsomorphicFuncs,
  typeQueue :: [Maybe GHC.Type],
  insertAbs :: Bool
  }

instance Show IsoRefactState where
  show (IsoState _fs tq _) = "There are currently " ++ show (length tq) ++ " types in the queue"

printQueue :: IsoRefact ()
printQueue = do
  st <- get
  let tq = typeQueue st
  lift $ logm "Current Type queue: "
  mapM_ (\t -> lift $ logm (showAnnData mempty 3 t)) tq
    where printType :: Maybe GHC.Type -> IsoRefact ()
          printType mTy = do
            case mTy of
              Nothing -> lift $ logm "NOTHING"
              Just ty -> lift $ logm (showType 3 ty)
            lift $ logm "---------------"

getAbsFun :: IsoRefact GHC.RdrName
getAbsFun = do
  st <- get
  let fs = funcs st
  return $ absFun fs

insertAbsToT :: IsoRefact ()
insertAbsToT = do
  st <- get
  put (st {insertAbs = True})

shouldInsertAbs :: IsoRefact Bool
shouldInsertAbs = do
  st <- get
  let insAbs = insertAbs st
  put $ st {insertAbs = False}
  return insAbs

type IsoRefact = StateT IsoRefactState RefactGhc

runIsoRefact :: IsoRefact a -> IsoRefactState -> RefactGhc a
runIsoRefact m initSt = evalStateT m initSt

showType :: Int -> GHC.Type -> String
showType n (GHC.TyVarTy v) = indent n ++ "(TyVarTy " ++ showAnnData mempty (n+1) v ++ ")"
showType n (GHC.AppTy t1 t2) = indent n ++ "(AppTy\n" ++ (showType (n+1) t1) ++ "\n" ++ (showType (n+1) t2) ++ "\n)"
showType n (GHC.TyConApp tc lst) = indent n ++ "(TyConApp: " ++ (printCon tc) ++
                                (foldl (\rst ty -> rst ++ "\n" ++ (showType (n+1) ty)) "" lst) ++ ")"
#if __GLASGOW_HASKELL__ >= 800
#else
showType n (GHC.FunTy t1 t2) = indent n ++ "(FunTy " ++ (showType (n+1) t1) ++ indent n ++ "->" ++ (showType (n+1) t2) ++ ")"
#endif
showType n (GHC.ForAllTy v ty) = indent n ++ "(ForAllTy: " ++ (showAnnData mempty (n+1) v) ++ "\n" ++ (showType (n+1) ty) ++ "\n)"
showType n (GHC.LitTy tl) = indent n ++ "(LitTy: " ++ showTyLit tl ++ ")"


showTyLit :: GHC.TyLit -> String
showTyLit (GHC.NumTyLit i) = show i
showTyLit (GHC.StrTyLit fs) = show fs

printCon :: GHC.TyCon -> String
printCon tc
  | GHC.isFunTyCon tc = "FunTyCon: " ++ shwTc tc
  | GHC.isAlgTyCon tc = "AlgTyCon: " ++ shwTc tc
  | otherwise = "TyCon: " ++ (show $ toConstr tc) ++ "|" ++ shwTc tc

shwTc :: GHC.TyCon -> String
shwTc = showSDoc_ . ppr

indent :: Int -> String
indent i = "\n" ++ replicate i ' '

--This takes in a type and returns its result type
getResultType :: GHC.Type -> GHC.Type
--This case is here because below top level bindings any types with type variables will be
--explicitly polymorphic once we get past all of the polymorphic types we will either find
--some other constructor and in that case we've found the result type
--if we find a FunTy constructor we continue to descent the type down the RHS
--until we find a non-FunTy constructor
getResultType (GHC.ForAllTy _ ty) = getResultType ty
#if __GLASGOW_HASKELL__ >= 800
#else
getResultType (GHC.FunTy _ ty) = comp ty
  where comp :: GHC.Type -> GHC.Type
        comp (GHC.FunTy _ ty) = comp ty
        comp ty = ty
#endif
getResultType ty = ty

modMGAltsRHS :: (ParsedLExpr -> RefactGhc ParsedLExpr) -> ParsedBind -> RefactGhc ParsedBind
modMGAltsRHS f bnd = do
  applyTP (stop_tdTP (failTP `adhocTP` comp)) bnd
  where
    comp :: GHC.GRHS GhcPs ParsedLExpr -> RefactGhc (GHC.GRHS GhcPs ParsedLExpr)
#if __GLASGOW_HASKELL__ >= 806
    comp (GHC.GRHS x lst expr) = do
      newExpr <- f expr
      return (GHC.GRHS x lst newExpr)
#else
    comp (GHC.GRHS lst expr) = do
      newExpr <- f expr
      return (GHC.GRHS lst newExpr)
#endif

getTyCon :: GHC.Type -> GHC.TyCon
getTyCon (GHC.TyConApp tc _) = tc

getTypeFromRdr :: (Data a) => GHC.RdrName -> a -> Maybe GHC.Type
getTypeFromRdr nm a = SYB.something (Nothing `SYB.mkQ` comp) a
  where comp :: GHC.HsBind GhcTc -> Maybe GHC.Type
        comp (GHC.FunBind { GHC.fun_id = (GHC.L _ n) } )
          | occNm == (GHC.occName (GHC.idName n)) = Just (GHC.idType n)
          | otherwise = Nothing
        comp _ = Nothing
        occNm = (GHC.occName nm)

getInitState :: ParsedLImportDecl -> IsoFuncStrings -> String -> String -> Maybe String -> GHC.Type -> RefactGhc IsoRefactState
getInitState iDecl fStrs absStr projStr mqual fstResTy = do
  fns <- mkFuncs iDecl absStr projStr fStrs mqual
  return $ IsoState fns [Just fstResTy] False

type IsoFuncStrings = [(String,String)]

mkFuncs :: ParsedLImportDecl -> String -> String -> [(String,String)] -> Maybe String -> RefactGhc IsomorphicFuncs
mkFuncs iDecl projStr absStr fStrings mqual = do
  fs <- funs
  return $ IF {
    projFun = mkRdr (GHC.mkVarOcc projStr),
    absFun = mkRdr (GHC.mkVarOcc absStr),
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
    mkLst = mapM f fStrings
    f :: (String,String) -> RefactGhc (String,(GHC.RdrName, GHC.Type))
    f (s1, s2) = do
      let o2 = GHC.mkVarOcc s2
          rdr = mkRdr o2
#if __GLASGOW_HASKELL__ >= 806
      rdrL <- locate rdr
      lExpr <- locate (GHC.HsVar GHC.noExt rdrL)
#elif __GLASGOW_HASKELL__ >= 800
      rdrL <- locate rdr
      lExpr <- locate (GHC.HsVar rdrL)
#else
      lExpr <- locate (GHC.HsVar rdr)
#endif
      ((_wrns, errs), mty) <- tcExprInTargetMod iDecl lExpr
      case mty of
        Nothing -> error $ "TypeChecking failed: " ++ GHC.foldBag (++) (\e -> show e ++ "\n") "" errs
        (Just ty) -> return (s1,(rdr,ty))


tcExprInTargetMod :: GHC.LImportDecl GhcPs -> ParsedLExpr -> RefactGhc (GHC.Messages, Maybe GHC.Type)
tcExprInTargetMod idecl ex = do
  -- pm <- getRefactParsedMod
  oldCntx <- GHC.getContext
  let
    lst = (GHC.IIDecl (GHC.unLoc idecl)):oldCntx
  GHC.setContext lst
  env <- GHC.getSession
#if __GLASGOW_HASKELL__ >= 802
  liftIO $ GHC.tcRnExpr env GHC.TM_Default ex
#else
  liftIO $ GHC.tcRnExpr env ex
#endif
    -- where addImps decs ms = let old = GHC.ms_textual_imps ms in
    --         ms {GHC.ms_textual_imps = old ++ [decs]}
