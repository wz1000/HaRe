module Language.Haskell.Refact.Utils.Synonyms where
import GHC
import Bag

{-
This file has synonyms for commonly used AST parser types.
-}

type UnlocParsedHsBind = HsBindLR RdrName RdrName
type ParsedGRHSs       = GRHSs RdrName (LHsExpr RdrName)
type ParsedGRHS        = GRHS RdrName (LHsExpr RdrName)
type ParsedMatchGroup  = MatchGroup RdrName (LHsExpr RdrName)
type ParsedMatch       = Match RdrName (LHsExpr RdrName)
type ParsedLMatch      = LMatch RdrName (LHsExpr RdrName)
type ParsedExpr        = HsExpr RdrName
type ParsedLExpr       = LHsExpr RdrName
type ParsedLStmt       = LStmt RdrName (LHsExpr RdrName)
type ParsedBind        = HsBind RdrName
type ParsedLBind       = LHsBind RdrName
type ParsedLDecl       = LHsDecl RdrName
type ParsedLImportDecl = LImportDecl RdrName
type ParsedBindBag    = Bag (LHsBindLR RdrName RdrName)
