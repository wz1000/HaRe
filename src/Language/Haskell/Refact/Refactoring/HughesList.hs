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
import qualified Unique as Unique (mkUniqueGrimily)
import Data.Generics.Strafunski.StrategyLib.StrategyLib
import Control.Applicative

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
  parsed <- getRefactParsed
  let (Just funBind) = getHsBind pos funNm parsed
      (Just tySig) = getTypeSig pos funNm parsed
      (Just (GHC.L _ funRdr)) = locToRdrName pos parsed
  newBind <- fixFunBind argNum funRdr funBind
  replaceFunBind pos newBind
  newTySig <- fixTypeSig argNum tySig
  logDataWithAnns "New type sig: " newTySig
  replaceTypeSig pos newTySig
  --Eventually should extract the qualifier as an argument so that people can choose their own.
  addSimpleImportDecl "Data.DList" (Just "DList")
  fixClientFunctions (numTypesOfBind funBind) argNum funRdr

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
fixClientFunctions :: Int -> Int -> GHC.RdrName -> RefactGhc ()
fixClientFunctions totalParams argNum name = if (totalParams == argNum)
                                    then wrapCallsWithToList name
                                    else applyAtCallPoint name (modifyNthParam totalParams argNum (wrapExpr fromLstRdr))
  where fromLstRdr = mkRdrName "fromList"

--This function handles the case where callsites need to be wrapped with toList
wrapCallsWithToList :: GHC.RdrName -> RefactGhc ()
wrapCallsWithToList name = applyAtCallPoint name comp
  where comp :: ParsedLExpr -> RefactGhc ParsedLExpr
        comp e = do
          zeroDP e
          parE <- wrapInPars e
#if __GLASGOW_HASKELL__ > 710
          toListVar <- toListVar'
#endif
          lLhs <- locate toListVar
          addAnnVal lLhs
          res <- locate $ (GHC.HsApp lLhs parE)
          return res
#if __GLASGOW_HASKELL__ <= 710          
        toListVar = GHC.HsVar (mkRdrName "toList")
#else
        toListVar' = do
           lNm <- locate (mkRdrName "toList")
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
