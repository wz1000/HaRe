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
import Language.Haskell.Refact.Utils.Types
import Language.Haskell.Refact.Utils.Query
import qualified GHC as GHC
import qualified RdrName as GHC
import qualified OccName as GHC
import qualified Id as GHC
import qualified TypeRep as GHC
import qualified TyCon as GHC
import qualified TcRnDriver as GHC
import qualified ErrUtils as GHC
import qualified Bag as GHC
import qualified Unique as GHC
import qualified GHC.SYB.Utils as SYB
import Data.Generics as SYB
import qualified Data.Map as M
import Control.Monad.State
import Language.Haskell.GHC.ExactPrint.Types
import Language.Haskell.GHC.ExactPrint.Utils
import Outputable
import Data.Generics.Strafunski.StrategyLib.StrategyLib


--Going to assume it's only the result type that will be modified right now
isoRefact :: Int -> Maybe String -> GHC.RdrName -> GHC.Type -> IsoRefactState -> ParsedBind -> RefactGhc ParsedBind
isoRefact _ mqual funNm newFTy iST bnd = do
  typedS <- getRefactTyped
  let m_fTy = getTypeFromRdr funNm typedS
      fTy = gfromJust "isoRefact: getting function type" m_fTy
      newResTy = getResultType newFTy
      paramTys = breakType newFTy
  newBnd <- modMGAltsRHS (\e -> runIsoRefact (doIsoRefact e) iST) bnd
  return newBnd

isoDone :: IsoRefact Bool
isoDone = do
  st <- get
  return $ (typeQueue st) == []

skipCurrent :: IsoRefact Bool
skipCurrent = do
  st <- get
  let currType = head (typeQueue st)
  case currType of
    Nothing -> do
      popTQ
      return True
    Just _ -> return False

doIsoRefact :: ParsedLExpr -> IsoRefact ParsedLExpr
doIsoRefact expr = do
  st <- get
  b1 <- isoDone
  b2 <- skipCurrent
  if b1 || b2
    then return expr
    else doIsoRefact' expr
  where doIsoRefact' :: ParsedLExpr -> IsoRefact ParsedLExpr
        doIsoRefact' (GHC.L l (GHC.HsApp le re)) = do
          le' <- doIsoRefact le
          re' <- doIsoRefact re
          return (GHC.L l (GHC.HsApp le' re'))
        doIsoRefact' (GHC.L l (GHC.OpApp le op rn re)) = do
          op' <- doIsoRefact op
          lift $ addBackquotes op'
          le' <- doIsoRefact le
          re' <- doIsoRefact re
          return (GHC.L l (GHC.OpApp le' op' rn re'))
        doIsoRefact' var@(GHC.L l (GHC.HsVar rdr)) = do
          st <- get          
          let tq = typeQueue st
              fs = funcs st              
          typed <- lift getRefactTyped
          mId <- lift (getIdFromVar var)
          let id = gfromJust ("Trying to get id for: " ++ SYB.showData SYB.Parser 3 rdr) mId
              goalType = gfromJust "Getting goal type" $ head tq
              currTy = GHC.idType id
              currRes = getResultType currTy
              keyOcc = GHC.rdrNameOcc rdr
              mVal = (GHC.occNameString keyOcc) `M.lookup` (eqFuns fs)          
          case mVal of
            Nothing -> do
              -- If this happens we have a problem and need to insert a fromList higher up the tree
              -- Need to figure out how to handle this case
              lift $ logm $ "No map on var: " ++ (SYB.showData SYB.Parser 3 keyOcc) ++ ": " ++ show (GHC.getUnique keyOcc)
              return var
            (Just (oNm, ty)) -> do
              if compType (getResultType ty) goalType
                then do
                let changedTypes = typeDifference ty currTy
                    newE = (GHC.L l (GHC.HsVar oNm))
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
        doIsoRefact' eLst@(GHC.L l (GHC.ExplicitList ty mSyn lst)) = do
          if (length lst) == 1
            then do
            st <- get
            let fs = funcs st
                singletonRdr = mkQualifiedRdrName (GHC.mkModuleName "DList") "singleton"
                singletonVar = (GHC.HsVar singletonRdr)
            lVar <- lift $ locate singletonVar
            lift $ addAnnVal lVar
            lift $ zeroDP lVar
            let rhs = head lst
            lift $ setDP (DP (0,1)) rhs
            lApp <- lift $ locate (GHC.HsApp lVar rhs)
            parApp <- lift $ wrapInPars lApp
            return parApp
            else do
            st <- get
            let fs = funcs st
                absRdr = absFun fs
            lVar <- lift $ locate (GHC.HsVar absRdr)
            lApp <- lift $ locate (GHC.HsApp lVar eLst)
            lift $ wrapInPars lApp
            return lApp
        doIsoRefact' ex = gmapM (SYB.mkM doIsoRefact) ex

typeDifference :: GHC.Type -> GHC.Type -> [Maybe GHC.Type]
typeDifference new old = let lst1 = tail $ breakType new
                             lst2 = tail $ breakType old in
  zipWith (\x y -> if (x `compType` y)
                   then Nothing
                   else (Just x)) lst1 lst2

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
  where breakType' (GHC.FunTy lTy rTy) = breakType' lTy ++ breakType' rTy
        breakType' ty = [ty]

{-
NOTE: When do we catch if the goal type is nothing??? Does this happen when we find a var or when
we descend subtrees?

From here we need to figure out if the var has a possible match from the map,
if it does then we need to see if the result type of the dlist function is the goalType
if it is then we can do the swap, we need to check which of the parameters of the new function changes type
from left to right those types are added to the type queue
-}
            
compType :: GHC.Type -> GHC.Type -> Bool
compType (GHC.TyVarTy v1) (GHC.TyVarTy v2) = True --v1 == v2
compType (GHC.TyVarTy _) _ = True
compType _ (GHC.TyVarTy _) = True --v1 == v2
compType (GHC.AppTy l1 l2) (GHC.AppTy r1 r2) = compType l1 r1 && compType l2 r2
compType (GHC.TyConApp tc1 lst1) (GHC.TyConApp tc2 lst2) = tc1 == tc2 && (and (zipWith compType lst1 lst2))
compType (GHC.FunTy l1 l2) (GHC.FunTy r1 r2) = compType l1 r1 && compType l2 r2
compType (GHC.ForAllTy v1 lTy) (GHC.ForAllTy v2 rTy) = compType lTy rTy
compType (GHC.LitTy l) (GHC.LitTy r) = l == r
compType _ _ = False

--The removes the for all types that are on the outside of a type with type variables
consumeOuterForAlls :: GHC.Type -> GHC.Type
consumeOuterForAlls (GHC.ForAllTy _ ty) = consumeOuterForAlls ty
consumeOuterForAlls ty = ty

--NOTE: May want to change this to use GHC.Name
data IsomorphicFuncs = IF {
  projFun :: GHC.RdrName,
  absFun :: GHC.RdrName,
  eqFuns :: M.Map String (GHC.RdrName, GHC.Type)
  }        

data IsoRefactState = IsoState {
  funcs :: IsomorphicFuncs,
  typeQueue :: [Maybe GHC.Type]
                               }

instance Show IsoRefactState where
  show (IsoState fs tq) = "There are currently " ++ show (length tq) ++ " types in the queue"

type IsoRefact = StateT IsoRefactState RefactGhc

runIsoRefact :: IsoRefact a -> IsoRefactState -> RefactGhc a
runIsoRefact m initSt = evalStateT m initSt

showType :: Int -> GHC.Type -> String
showType n (GHC.TyVarTy v) = indent n ++ "(TyVarTy " ++ SYB.showData SYB.TypeChecker (n+1) v ++ ")"
showType n (GHC.AppTy t1 t2) = indent n ++ "(AppTy\n" ++ (showType (n+1) t1) ++ "\n" ++ (showType (n+1) t2) ++ "\n)"
showType n (GHC.TyConApp tc lst) = indent n ++ "(TyConApp: " ++ (printCon tc) ++
                                (foldl (\rst ty -> rst ++ "\n" ++ (showType (n+1) ty)) "" lst) ++ ")"
showType n (GHC.FunTy t1 t2) = indent n ++ "(FunTy " ++ (showType (n+1) t1) ++ indent n ++ "->" ++ (showType (n+1) t2) ++ ")"
showType n (GHC.ForAllTy v ty) = indent n ++ "(ForAllTy: " ++ (SYB.showData SYB.TypeChecker (n+1) v) ++ "\n" ++ (showType (n+1) ty) ++ "\n)"
showType n (GHC.LitTy tl) = indent n ++ "(LitTy: " ++ showTyLit tl ++ ")"


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

modMGAltsRHS :: (ParsedLExpr -> RefactGhc ParsedLExpr) -> ParsedBind -> RefactGhc ParsedBind
modMGAltsRHS f bnd = do
  applyTP (full_tdTP (idTP `adhocTP` comp)) bnd --SYB.everywhereM (SYB.mkM comp)
  where 
    comp :: GHC.GRHS GHC.RdrName ParsedLExpr -> RefactGhc (GHC.GRHS GHC.RdrName ParsedLExpr)
    comp (GHC.GRHS lst expr) = do
      logm "Inside comp"
      newExpr <- f expr
      return (GHC.GRHS lst newExpr)

getTyCon :: GHC.Type -> GHC.TyCon
getTyCon (GHC.TyConApp tc _) = tc

getTypeFromRdr :: (Data a) => GHC.RdrName -> a -> Maybe GHC.Type
getTypeFromRdr nm a = SYB.something (Nothing `SYB.mkQ` comp) a
  where comp :: GHC.HsBind GHC.Id -> Maybe GHC.Type
        comp (GHC.FunBind (GHC.L _ id) _ _ _ _ _)
          | occNm == (GHC.occName (GHC.idName id)) = Just (GHC.idType id)
          | otherwise = Nothing
        comp _ = Nothing
        occNm = (GHC.occName nm)

getInitState :: ParsedLImportDecl -> IsoFuncStrings -> Maybe String -> GHC.Type -> RefactGhc IsoRefactState
getInitState iDecl fStrs mqual fstResTy = do
  funcs <- mkFuncs iDecl "toList" "fromList" fStrs mqual
  return $ IsoState funcs [Just fstResTy]

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
      lExpr <- locate (GHC.HsVar rdr)
      ((wrns, errs), mty) <- tcExprInTargetMod iDecl lExpr
      case mty of
        Nothing -> error $ "TypeChecking failed: " ++ GHC.foldBag (++) (\e -> show e ++ "\n") "" errs
        (Just ty) -> return (s1,(rdr,ty))


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
