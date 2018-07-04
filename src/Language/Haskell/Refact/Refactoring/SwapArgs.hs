{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Language.Haskell.Refact.Refactoring.SwapArgs (swapArgs) where

import qualified Data.Generics.Aliases as SYB

import qualified Name                  as GHC
import qualified GHC

import qualified GhcModCore as GM (Options(..))
import Language.Haskell.Refact.API

import Data.Generics.Schemes

import Language.Haskell.GHC.ExactPrint.Types
import Language.Haskell.GHC.ExactPrint.Utils
import System.Directory



-- TODO: replace args with specific parameters
swapArgs :: RefactSettings -> GM.Options -> [String] -> IO [FilePath]
swapArgs settings opts args
  = do let fileName = args!!0
           row = (read (args!!1)::Int)
           col = (read (args!!2)::Int)
       absFileName <- normaliseFilePath fileName
       runRefacSession settings opts (comp absFileName (row,col))


comp :: String -> SimpPos
     -> RefactGhc [ApplyRefacResult]
comp fileName (row, col) = do
       parseSourceFileGhc fileName
       parsed  <- getRefactParsed
       nm      <- getRefactNameMap

       let name = locToNamePure nm (row, col) parsed

       case name of
            -- (Just pn) -> do refactoredMod@(_, (_t, s)) <- applyRefac (doSwap pnt pn) (Just modInfo) fileName
            (Just pn) -> do
                            (refactoredMod,_) <- applyRefac (doSwap pn) (RSFile fileName)
                            return [refactoredMod]
            Nothing   -> error "Incorrect identifier selected!"
       --if isFunPNT pnt mod    -- Add this back in ++ CMB +++
       -- then do
              --        rs <-if isExported pnt exps
       --               then  applyRefacToClientMods (doSwap pnt) fileName
       --               else  return []
       -- writeRefactoredFiles False (r:rs)
       -- else error "\nInvalid cursor position!"

       -- putStrLn (showToks t)
       -- writeRefactoredFiles False [refactoredMod]
       -- putStrLn ("here" ++ (showAnnData mempty 0 mod))  -- $ show [fileName, beginPos, endPos]
       -- putStrLn "Completd"


doSwap :: GHC.Name -> RefactGhc ()
doSwap n1 = do
    parsed <- getRefactParsed
    logm $ "doSwap:parsed=" ++ showAnnData mempty 0 parsed
    nm <- getRefactNameMap
    parsed' <- everywhereM (SYB.mkM (inMod nm)
                           `SYB.extM` (inExp nm)
                           `SYB.extM` (inType nm)
                           `SYB.extM` (inTypeDecl nm)
                           ) parsed
    -- this needs to be bottom up +++ CMB +++
    putRefactParsed parsed' emptyAnns
    return ()

    where
         -- 1. The definition is at top level...
#if __GLASGOW_HASKELL__ >= 806
         inMod nm ((GHC.FunBind x ln2 (GHC.MG y (GHC.L lm matches) p ) a tick)::GHC.HsBind GhcPs)
#elif __GLASGOW_HASKELL__ > 710
         inMod nm ((GHC.FunBind ln2 (GHC.MG (GHC.L lm matches) p m1 m2) a locals tick)::GHC.HsBind GhcPs)
#else
         inMod nm ((GHC.FunBind ln2 infixity (GHC.MG matches p m1 m2) a locals tick)::GHC.HsBind GhcPs)
#endif
            | GHC.nameUnique n1 == GHC.nameUnique (rdrName2NamePure nm ln2)
                    = do logm ("inMatch>" ++ showAnnData mempty 0 ln2 ++ "<")
                         newMatches <- updateMatches matches
#if __GLASGOW_HASKELL__ >= 806
                         return (GHC.FunBind x ln2 (GHC.MG y (GHC.L lm newMatches) p ) a tick)
#elif __GLASGOW_HASKELL__ > 710
                         return (GHC.FunBind ln2 (GHC.MG (GHC.L lm newMatches) p m1 m2) a locals tick)
#else
                         return (GHC.FunBind ln2 infixity (GHC.MG newMatches p m1 m2) a locals tick)
#endif
         inMod _ func = return func

         -- 2. All call sites of the function...
#if __GLASGOW_HASKELL__ >= 806
         inExp nm ((GHC.L l (GHC.HsApp x (GHC.L e0 (GHC.HsApp x2 e e1)) e2))::GHC.LHsExpr GhcPs)
#else
         inExp nm ((GHC.L l (GHC.HsApp (GHC.L e0 (GHC.HsApp e e1)) e2))::GHC.LHsExpr GhcPs)
#endif
            | cond
                   -- =  update e2 e1 =<< update e1 e2 expr
                   = do
                       -- expr1 <- update e1 e2 expr
                       -- expr2 <- update e2 e1 expr1
                       -- return expr2
#if __GLASGOW_HASKELL__ >= 806
                       return (GHC.L l (GHC.HsApp x (GHC.L e0 (GHC.HsApp x2 e e2)) e1))
#else
                       return (GHC.L l (GHC.HsApp (GHC.L e0 (GHC.HsApp e e2)) e1))
#endif
            where
              cond = case (expToNameRdr nm e) of
                Nothing -> False
                Just n2 -> GHC.nameUnique n2 == GHC.nameUnique n1
         inExp _ e = return e

         -- 3. Type signature...
#if __GLASGOW_HASKELL__ >= 806
         inType nm (GHC.L x (GHC.TypeSig y [lname] (GHC.HsWC wcs (GHC.HsIB vars types)))::GHC.LSig GhcPs)
#elif __GLASGOW_HASKELL__ > 800
         inType nm (GHC.L x (GHC.TypeSig [lname] (GHC.HsWC wcs (GHC.HsIB vars types cl)))::GHC.LSig GhcPs)
#elif __GLASGOW_HASKELL__ > 710
         inType nm (GHC.L x (GHC.TypeSig [lname] (GHC.HsIB ivs (GHC.HsWC wcs mwc types)))::GHC.LSig GhcPs)
#else
         inType nm (GHC.L x (GHC.TypeSig [lname] types pns)::GHC.LSig GhcPs)
#endif
           | GHC.nameUnique (rdrName2NamePure nm lname) == GHC.nameUnique n1
                = do
                     logm $ "doSwap.inType"
                     let (t1:t2:ts) = tyFunToList types
                     let t1' = t2
                     let t2' = t1
#if __GLASGOW_HASKELL__ >= 806
                     return (GHC.L x (GHC.TypeSig y [lname] (GHC.HsWC wcs (GHC.HsIB vars (tyListToFun (t1':t2':ts)) ))))
#elif __GLASGOW_HASKELL__ > 800
                     return (GHC.L x (GHC.TypeSig [lname] (GHC.HsWC wcs (GHC.HsIB vars (tyListToFun (t1':t2':ts)) cl))))
#elif __GLASGOW_HASKELL__ > 710
                     return (GHC.L x (GHC.TypeSig [lname] (GHC.HsIB ivs (GHC.HsWC wcs mwc (tyListToFun (t1':t2':ts))))))
#else
                     return (GHC.L x (GHC.TypeSig [lname] (tyListToFun (t1':t2':ts)) pns))
#endif

#if __GLASGOW_HASKELL__ >= 806
         inType nm (GHC.L _ (GHC.TypeSig _ (n:ns) _types )::GHC.LSig GhcPs)
#elif __GLASGOW_HASKELL__ > 710
         inType nm (GHC.L _x (GHC.TypeSig (n:ns) _types )::GHC.LSig GhcPs)
#else
         inType nm (GHC.L _x (GHC.TypeSig (n:ns) _types _)::GHC.LSig GhcPs)
#endif
           | GHC.nameUnique n1 `elem` (map (\n' -> GHC.nameUnique (rdrName2NamePure nm n')) (n:ns))
            = error "Error in swapping arguments in type signature: signature bound to muliple entities!"

         inType _ ty = return ty

#if __GLASGOW_HASKELL__ >= 806
         inTypeDecl nm (GHC.L l (GHC.SigD x s)) = do
           (GHC.L _ s') <- inType nm (GHC.L l s)
           return (GHC.L l (GHC.SigD x s'))
#else
         inTypeDecl nm (GHC.L l (GHC.SigD s)) = do
           (GHC.L _ s') <- inType nm (GHC.L l s)
           return (GHC.L l (GHC.SigD s'))
#endif
         inTypeDecl _ x = return x

#if __GLASGOW_HASKELL__ >= 806
         tyFunToList (GHC.L _ (GHC.HsForAllTy _ _ (GHC.L _ (GHC.HsFunTy _ t1 t2)))) = t1 : (tyFunToList t2)
#elif __GLASGOW_HASKELL__ > 710
         tyFunToList (GHC.L _ (GHC.HsForAllTy _ (GHC.L _ (GHC.HsFunTy t1 t2)))) = t1 : (tyFunToList t2)
#else
         tyFunToList (GHC.L _ (GHC.HsForAllTy _ _ _ _ (GHC.L _ (GHC.HsFunTy t1 t2)))) = t1 : (tyFunToList t2)
#endif
#if __GLASGOW_HASKELL__ >= 806
         tyFunToList (GHC.L _ (GHC.HsFunTy _ t1 t2)) = t1 : (tyFunToList t2)
#else
         tyFunToList (GHC.L _ (GHC.HsFunTy t1 t2)) = t1 : (tyFunToList t2)
#endif
         tyFunToList t = [t]

         tyListToFun []   = error "SwapArgs.tyListToFun" -- Keep the exhaustiveness checker happy
         tyListToFun [t1] = t1
#if __GLASGOW_HASKELL__ >= 806
         tyListToFun (t1:ts) = GHC.noLoc (GHC.HsFunTy GHC.noExt t1 (tyListToFun ts))
#else
         tyListToFun (t1:ts) = GHC.noLoc (GHC.HsFunTy t1 (tyListToFun ts))
#endif

         updateMatches [] = return []
#if __GLASGOW_HASKELL__ >= 806
         updateMatches ((GHC.L x (GHC.Match y mfn pats         rhs)::GHC.LMatch GhcPs (GHC.LHsExpr GhcPs)):matches)
#elif __GLASGOW_HASKELL__ >= 804
         updateMatches ((GHC.L x (GHC.Match   mfn pats         rhs)::GHC.LMatch GhcPs (GHC.LHsExpr GhcPs)):matches)
#else
         updateMatches ((GHC.L x (GHC.Match   mfn pats nothing rhs)::GHC.LMatch GhcPs (GHC.LHsExpr GhcPs)):matches)
#endif
           = case pats of
               (p1:p2:ps) -> do
                                -- p1' <- update p1 p2 p1
                                -- p2' <- update p2 p1 p2
                                let p1' = p2
                                let p2' = p1
                                matches' <- updateMatches matches
#if __GLASGOW_HASKELL__ >= 806
                                return ((GHC.L x (GHC.Match y mfn (p1':p2':ps) rhs)):matches')
               [p] -> return [GHC.L x (GHC.Match y mfn [p] rhs)]
               []  -> return [GHC.L x (GHC.Match y mfn [] rhs)]
#elif __GLASGOW_HASKELL__ >= 804
                                return ((GHC.L x (GHC.Match mfn (p1':p2':ps) rhs)):matches')
               [p] -> return [GHC.L x (GHC.Match mfn [p] rhs)]
               []  -> return [GHC.L x (GHC.Match mfn [] rhs)]
#else
                                return ((GHC.L x (GHC.Match mfn (p1':p2':ps) nothing rhs)):matches')
               [p] -> return [GHC.L x (GHC.Match mfn [p] nothing rhs)]
               []  -> return [GHC.L x (GHC.Match mfn [] nothing rhs)]
#endif


