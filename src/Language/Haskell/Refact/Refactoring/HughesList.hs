{-# LANGUAGE CPP #-}
module Language.Haskell.Refact.Refactoring.HughesList
       (hughesList, compHughesList) where

import Language.Haskell.Refact.API
import qualified Language.Haskell.GhcMod as GM
import System.Directory
import qualified GHC.SYB.Utils as SYB
import Data.Generics as SYB
import qualified GHC as GHC
import qualified FastString as GHC
import qualified RdrName as GHC
import qualified OccName as GHC
import qualified Name as GHC
import Language.Haskell.GHC.ExactPrint.Types
import qualified Unique as Unique (mkUniqueGrimily)

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

hughesList :: RefactSettings -> GM.Options -> FilePath -> String -> SimpPos -> IO [FilePath]
hughesList settings cradle fileName funNm pos = do
  absFileName <- canonicalizePath fileName
  runRefacSession settings cradle (compHughesList fileName funNm pos)

compHughesList :: FilePath -> String -> SimpPos -> RefactGhc [ApplyRefacResult]
compHughesList fileName funNm pos = do
  (refRes@((_fp,ismod),_), ()) <- applyRefac (doHughesList fileName funNm pos) (RSFile fileName)
  case ismod of
    RefacUnmodifed -> error "Introducing Hughes lists failed"
    RefacModified -> return ()
  return [refRes]

doHughesList :: FilePath -> String -> SimpPos -> RefactGhc ()
doHughesList fileName funNm pos = do
  parsed <- getRefactParsed
  let (Just funBind) = getHsBind pos funNm parsed
      (Just tySig) = getTypeSig pos funNm parsed
      (Just (GHC.L _ funRdr)) = locToRdrName pos parsed
  newBind <- fixFunBind funRdr funBind
  replaceFunBind pos newBind
  newTySig <- fixTypeSig tySig
  replaceTypeSig pos newTySig
  addSimpleImportDecl "Data.DList"
  return ()

fixTypeSig :: GHC.Sig GHC.RdrName -> RefactGhc (GHC.Sig GHC.RdrName)
fixTypeSig = SYB.everywhereM (SYB.mkM replaceList)
  where replaceList :: GHC.LHsType GHC.RdrName -> RefactGhc (GHC.LHsType GHC.RdrName)
        replaceList (GHC.L l (GHC.HsListTy innerTy)) = do
          let dlistFS = GHC.fsLit "DList"
              dlistUq = GHC.mkVarUnqual dlistFS
          dlistTy <- constructLHsTy dlistUq          
          setDP (DP (0,1)) innerTy
          lTy <- locate (GHC.HsAppTy dlistTy innerTy)
#if __GLASGOW_HASKELL__ <= 710
          addAnnVal lTy
#else
          zeroDP lTy
#endif          
          return lTy
        replaceList x = return x


fixFunBind :: GHC.RdrName -> GHC.HsBind GHC.RdrName -> RefactGhc (GHC.HsBind GHC.RdrName)
fixFunBind funRdr bind = do
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
        singletonRdr = GHC.mkVarUnqual (GHC.fsLit "singleton")
        fromListRdr = GHC.mkVarUnqual (GHC.fsLit "fromList")
        appendRdr = GHC.mkVarUnqual (GHC.fsLit "append")                        
