{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.Refact.Refactoring.DeleteDef
  (deleteDef, compDeleteDef) where

import qualified Data.Generics as SYB
import qualified GHC
import Control.Monad
-- import Control.Monad.State
import Language.Haskell.Refact.API
import Data.Generics.Strafunski.StrategyLib.StrategyLib
import qualified Haskell.Ide.Engine.PluginApi as HIE (Options(..),ModulePath(..))
-- import System.Directory
import Language.Haskell.GHC.ExactPrint
import Language.Haskell.GHC.ExactPrint.Types

deleteDef :: RefactSettings -> HIE.Options -> FilePath -> SimpPos -> IO [FilePath]
deleteDef settings cradle fileName (row,col) = do
  absFileName <- normaliseFilePath fileName
  runRefacSession settings cradle (compDeleteDef absFileName (row,col))

compDeleteDef ::FilePath -> SimpPos -> RefactGhc [ApplyRefacResult]
compDeleteDef fileName (row,col) = do
  parseSourceFileGhc fileName
  -- renamed <- getRefactRenamed
  parsed <- getRefactParsed
  targetModule <- getRefactTargetModule
  -- m <- getModule
  let
      -- (Just (modName,_)) = getModuleName parsed
      maybeRdrPn = locToRdrName (row,col) parsed
  case maybeRdrPn of
    Just (GHC.L _ _n) ->
      do
        logm $ "DeleteDef.comp: before isPNUsed"
        Just ghcn <- locToName (row,col) parsed
        pnIsUsedLocal <- isPNUsed ghcn
        clients <- clientModsAndFiles targetModule
        pnUsedClients <- isPNUsedInClients ghcn targetModule
        if (pnIsUsedLocal || pnUsedClients)
           then error "The def to be deleted is still being used"
          else do
          logm $ "Result of is used: " ++ (show pnIsUsedLocal) ++ " pnUsedClients: " ++ (show pnUsedClients)
          (refRes@((_fp,ismod), (anns,ps)),()) <- applyRefac (doDeletion ghcn) RSAlreadyLoaded
          case (ismod) of
            RefacUnmodifed -> do
              error "The def deletion failed"
            RefacModified -> return ()
          logm $ "Res after delete === " ++ (exactPrint ps anns)
          return [refRes]
    Nothing -> error "Invalid cursor position!"


isPNUsed :: GHC.Name -> RefactGhc Bool
isPNUsed pn = do
  renamed <- getRefactRenamed
  pnUsedInScope pn renamed


pnUsedInScope :: (SYB.Data t) => GHC.Name -> t -> RefactGhc Bool
pnUsedInScope pn t' = do
  logm $ "Start of pnUsedInScope"
  res <- applyTU (stop_tdTU (failTU `adhocTU` bind `adhocTU` var)) t'
  return $ (length res) > 0
    where
      bind ((GHC.FunBind { GHC.fun_id = (GHC.L l name) }) :: GHC.HsBindLR GhcRn GhcRn)
      -- bind ((GHC.FunBind (GHC.L l name)  match _ _ _) :: GHC.HsBindLR GhcRn GhcRn)
        | name == pn = do
            logm $ "Found Binding at: " ++ (showGhc l)
            return []
      bind _other = do
        mzero
#if __GLASGOW_HASKELL__ >= 806
      var ((GHC.HsVar _ (GHC.L _ name)) :: GHC.HsExpr GhcRn)
#elif __GLASGOW_HASKELL__ > 710
      var ((GHC.HsVar (GHC.L _ name)) :: GHC.HsExpr GhcRn)
#else
      var ((GHC.HsVar name) :: GHC.HsExpr GhcRn)
#endif
        | name == pn = do
            logm $ "Found var"
            return [pn]
      var _other = do
        mzero


isPNUsedInClients :: GHC.Name -> HIE.ModulePath -> RefactGhc Bool
isPNUsedInClients pn modPath = do
        pnIsExported <- isExported pn
        if pnIsExported
          then do clients <- clientModsAndFiles modPath
                  logm $ "DeleteDef : clients: " ++ (showGhc clients)
                  res <- foldM (pnUsedInClientScope pn) False clients
                  return res
          else do return False

pnUsedInClientScope :: GHC.Name -> Bool -> TargetModule -> RefactGhc Bool
pnUsedInClientScope name b modu = do
  getTargetGhc modu
  isInScope <- isInScopeAndUnqualifiedGhc (nameToString name) Nothing
  logm $ "The module file path: " ++ (show (HIE.mpPath modu)) ++ "\n is pn in scope: " ++ (show isInScope)
  return (b || isInScope)

doDeletion :: GHC.Name -> RefactGhc ()
doDeletion n = do
  parsed <- getRefactParsed
  (res, _decl, _mSig) <- rmDecl n True parsed
  putRefactParsed res emptyAnns
  return ()
