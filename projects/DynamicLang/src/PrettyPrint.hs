{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
module PrettyPrint where

import DataDynamic
import DataTypeable
import Text.PrettyPrint.HughesPJClass
import StaticLang as SL

-- =======================================================================================
-- | Pretty printer instace for our StaticExp terms. Takes care of indentation
-- | and spaces when necessary.
instance Pretty (StaticExp t) where
  pPrint (Lam str exp)   = if length (render short) <= 10 then short else long
    where short = parens $ text ("\\ " ++ str ++ ".") <+> pPrint exp
          long  = parens $ text ("\\ " ++ str ++ ".") $$  pPrint exp
  pPrint (f :@ exp)      = parens $ pPrint f <+> pPrint exp

  pPrint (BinInt op e1 e2)      = parens $ pPrint e1 <+> intTextOp op     <+> pPrint e2
  pPrint (BinBool op e1 e2)     = pPrint e1 <+> boolTextOp op    <+> pPrint e2
  pPrint (BinIntBool op e1 e2)  = pPrint e1 <+> intBoolTextOp op <+> pPrint e2
  pPrint (BinEq e1 e2)          = pPrint e1 <+> text "==" <+> pPrint e2
  pPrint (UniNot e) = text "not" <+> pPrint e
  pPrint (UniFst e) = text "fst" <+> parens (pPrint e)
  pPrint (UniSnd e) = text "snd" <+> parens (pPrint e)
  pPrint (Lit x)         = text (show x)
  pPrint (Var s)         = text s
  pPrint (If cond e1 e2) = text "if" <+> nest 1 (pPrint cond) $$
                                         nest 1 (pPrint e1)   $$
                                         nest 1 (pPrint e2)
  pPrint (To exp)        = text "to" <+> pPrint exp
  pPrint (From exp)      = text "from" <+> pPrint exp

intTextOp :: IntIntOp -> Doc
intTextOp Plus  = text "+"
intTextOp Minus = text "-"
intTextOp Mult  = text "*"

boolTextOp :: BoolBoolOp -> Doc
boolTextOp Or  = text "||"
boolTextOp And  = text "&&"

intBoolTextOp Gte  = text ">="
intBoolTextOp Lte  = text "<="
intBoolTextOp Lt  = text "<"
intBoolTextOp Gt  = text ">"

-- TODO
--textOp SL.EQ  = text "=="
--textOp NEQ  = text "/="

-- | Instance to our pretty printer.
instance Show (StaticExp t) where
  show exp = render $ pPrint exp

printAST :: StaticExp t -> IO()
printAST exp = putStrLn (show (pPrint exp))

-- =======================================================================================
