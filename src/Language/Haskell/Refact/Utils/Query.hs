{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
module Language.Haskell.Refact.Utils.Query where
--This module contains functions that retrieve sections of the ast. It is fairly high level.

import qualified GHC as GHC
import qualified SrcLoc as GHC
import qualified Id as GHC
import qualified OccName as GHC
import qualified Name as GHC
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.Synonyms
import Language.Haskell.Refact.Utils.Types
import Language.Haskell.Refact.Utils.TypeUtils
import Data.Generics as SYB
import GHC.SYB.Utils as SYB
import Control.Applicative
import FastString
import RdrName

--Takes a single match and returns a tuple containing the grhs and the pattern
--Assumptions:
  -- Only a single pattern will be returned. Which pattern is returned depends on the behaviour of SYB.something. 
getVarAndRHS :: GHC.Match GHC.RdrName (GHC.LHsExpr GHC.RdrName) -> RefactGhc (GHC.LPat GHC.RdrName, ParsedGRHSs)
getVarAndRHS match = do
  let (Just pat) = SYB.something (Nothing `SYB.mkQ` varPat) (GHC.m_pats match)
  return (pat , GHC.m_grhss match)
    where varPat lPat@(GHC.L _ (GHC.VarPat _ )) = Just lPat
          varPat _ = Nothing

--Looks up the function binding at the given position. Returns nothing if the position does not contain a binding.
getHsBind :: (Data a) => SimpPos -> a -> Maybe (GHC.HsBind GHC.RdrName)
getHsBind pos a = getLHsBind pos a >>= (\a -> return $ GHC.unLoc a)


getLHsBind :: (Data a) => SimpPos -> a -> Maybe (GHC.LHsBind GHC.RdrName)
getLHsBind pos a =
  let rdrNm = locToRdrName pos a in
  case rdrNm of
  Nothing -> Nothing
  (Just (GHC.L _ rNm)) -> SYB.everythingStaged SYB.Parser (<|>) Nothing (Nothing `SYB.mkQ` isBind) a
    where
#if __GLASGOW_HASKELL__ <= 710
        isBind (bnd@(GHC.L _ (GHC.FunBind (GHC.L _ name) _ _ _ _ _)) :: GHC.LHsBind GHC.RdrName)
#else
        isBind (bnd@(GHC.L _ (GHC.FunBind (GHC.L _ name) _ _ _ _)) :: GHC.LHsBind GHC.RdrName)
#endif
            | name == rNm = (Just bnd)
        isBind _ = Nothing

--Get the name of a function from a string
getFunName :: (SYB.Data t) => String -> t -> Maybe GHC.Name
getFunName str = SYB.something (Nothing `SYB.mkQ` comp)
  where
    comp :: GHC.HsBind GHC.Name -> Maybe GHC.Name
    comp (GHC.FunBind lid _ _ _ _ _)
      | (GHC.unLoc lid) `isNameString` str = Just (GHC.unLoc lid)
      | otherwise = Nothing
    comp _ = Nothing
        --This seems pretty dangerous but it'll do in a pinch
    isNameString :: GHC.Name -> String -> Bool
    isNameString nm str = (GHC.nameOccName nm) == (GHC.mkVarOcc str)
          

getTypedHsBind :: (Data a) => GHC.OccName -> a -> Maybe (GHC.HsBind GHC.Id)
getTypedHsBind occ = SYB.something (Nothing `SYB.mkQ` isBind)
  where
#if __GLASGOW_HASKELL__ <= 710
        isBind (bnd@(GHC.FunBind (GHC.L _ nm) _ _ _ _ _) :: GHC.HsBind GHC.Id)
#else
        isBind (bnd@(GHC.FunBind (GHC.L _ nm) _ _ _ _) :: GHC.HsBind GHC.Id)
#endif
            |  (GHC.occName (GHC.idName nm)) == occ = (Just bnd)
        isBind _ = Nothing
  

--This looks up the type signature of the given identifier.
--The given position is assumed to be the location of where the identifier is defined
--NOT the location of the type signature 
getTypeSig :: (Data a) => SimpPos -> String -> a -> Maybe (GHC.Sig GHC.RdrName)
getTypeSig pos funNm a =
  let rdrNm = locToRdrName pos a in
  case rdrNm of
    Nothing -> Nothing
    (Just (GHC.L _ rNm)) -> SYB.everything (<|>) (Nothing `SYB.mkQ` isSig) a
      where
#if __GLASGOW_HASKELL__ <= 710
        isSig ty@(GHC.TypeSig [(GHC.L _ nm)] _ _) = if nm == rNm
#else
        isSig ty@(GHC.TypeSig [(GHC.L _ nm)] _) = if nm == rNm
#endif
                                                    then (Just ty)
                                                    else Nothing
        isSig _ = Nothing

--It's common to want to know if an expression is just a certain var
--This function takes a String of the var and returns true of the given expression represents that var
isHsVar :: String -> ParsedExpr -> Bool
#if __GLASGOW_HASKELL__ <= 710
isHsVar str (GHC.HsVar rNm) =
#else
isHsVar str (GHC.HsVar (GHC.L _ rNm)) =
#endif
  let nm = mkVarUnqual (fsLit str) in
    rNm == nm
isHsVar _ _ = False

astCompare :: (Data a) => a -> a -> Bool
astCompare = geq `extTwinQ` rdrComp
  where rdrComp :: GHC.RdrName -> GHC.RdrName -> Bool
        rdrComp = (==)

extTwinQ :: (Typeable a, Typeable b) => (a -> a -> r) -> (b -> b -> r) -> a -> a -> r
extTwinQ f g a1 a2 =
  case mr of
    Nothing -> f a1 a2
    (Just r) -> r
  where mr = cast a1 >>= (\b1 -> cast a2 >>= (\b2 -> Just $ g b1 b2))                        


lookupByLoc :: (SYB.Data a,  SYB.Data b) => GHC.SrcSpan -> GHC.Located a -> Maybe (GHC.Located b)
lookupByLoc loc = SYB.something (Nothing `SYB.mkQ` comp)
  where comp :: (SYB.Data a) => GHC.Located a -> Maybe (GHC.Located a)
        comp a@(GHC.L l _)
          | l == loc = Just a
          | otherwise = Nothing
