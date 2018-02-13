module Language.Haskell.Refact.Utils.Synonyms where

import GHC
import Bag

import qualified Language.Haskell.GHC.ExactPrint.Types as G

{-
This file has synonyms for commonly used AST parser types.
-}
-- TODO:AZ get rid of these
type UnlocParsedHsBind = HsBindLR G.GhcPs G.GhcPs
type ParsedGRHSs       = GRHSs G.GhcPs (LHsExpr G.GhcPs)
type ParsedGRHS        = GRHS G.GhcPs (LHsExpr G.GhcPs)
type ParsedMatchGroup  = MatchGroup G.GhcPs (LHsExpr G.GhcPs)
type ParsedMatch       = Match G.GhcPs (LHsExpr G.GhcPs)
type ParsedLMatch      = LMatch G.GhcPs (LHsExpr G.GhcPs)
type ParsedExpr        = HsExpr G.GhcPs
type ParsedLExpr       = LHsExpr G.GhcPs
type ParsedLStmt       = LStmt G.GhcPs (LHsExpr G.GhcPs)
type ParsedBind        = HsBind G.GhcPs
type ParsedLBind       = LHsBind G.GhcPs
type ParsedLDecl       = LHsDecl G.GhcPs
type ParsedLImportDecl = LImportDecl G.GhcPs
type ParsedBindBag     = Bag (LHsBindLR G.GhcPs G.GhcPs)
