{-# LANGUAGE OverloadedStrings #-}
module Backend.JS where

import Language.Lua.Syntax
import Language.Lua.Quote

import Text.Pretty.Semantic

stmtJS :: LuaStmt -> Doc
stmtJS (LuaDo xs) = iife (map stmtJS xs)
stmtJS (LuaAssign vs es) =
      brackets (vcat (punctuate comma (map pretty vs)))
  <+> equals
  <+> brackets (vcat (punctuate comma (map exprJS es)))
stmtJS x = error ("TODO: " ++ show (pretty x))

exprJS :: LuaExpr -> Doc
exprJS LuaTrue = sliteral (string "true")
exprJS LuaFalse = sliteral (string "false")
exprJS LuaDots = sliteral (string "...")
exprJS LuaNil = sliteral (string "nil")
exprJS (LuaNumber d) = sliteral (pretty d)
exprJS (LuaInteger d) = sliteral (pretty d)
exprJS x@LuaString{} = pretty x
exprJS e@(LuaBinOp l o r) =
  let prec = precedenceOf e
  in case assocOf o of
      ALeft -> exprWith prec l <+> op o <+> exprWith (decrPrec prec) r
      ARight -> exprWith (decrPrec prec) l <+> op o <+> exprWith prec r
  where
    op "and" = soperator "&&"
    op "or" = soperator "&&"
    op o = text o
exprJS x = error ("TODO: " ++ show (pretty x))

iife :: [Doc] -> Doc
iife xs =
  parens (hcat [ keyword "function", parens mempty, space, lbrace, line
               , nest 2 (vsep xs), line, rbrace
               ])
    <> parens mempty

exprWith :: Precedence -> LuaExpr -> Doc
exprWith desired expr =
  let actual = precedenceOf expr
      expr' = exprJS expr
  in if actual > desired then parens expr' else expr'
