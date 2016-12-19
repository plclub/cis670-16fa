module Parser where

import Control.Applicative((<*))
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Token
import Text.Parsec.Language
-- Our language definition and operators.
import Lang
import Common

-- | Generate our Lang definition from emptyDef.
langDef = emptyDef
          { commentLine    = "--"
          , nestedComments = False
          , identStart     = letter <|> char '_'
          , identLetter    = alphaNum <|> oneOf "_'"
          , opStart        = opLetter emptyDef
          , opLetter       = oneOf "+-*|&<>=~"
          , reservedOpNames= []
          , reservedNames  = ["fun", "if", "true", "false", "head", "not",
                              "tail", "fst", "snd"]
          , caseSensitive  = True
          }

-- | Get token parsers from langauge definition.
TokenParser{ parens = parensP
           , identifier = identifierP
           , reserved = reservedP
           , operator = operatorP
           , semiSep1 = semiSep1P
           , whiteSpace = whiteSpaceP
           , charLiteral = charLiteralP
           , stringLiteral = stringLiteralP
           , natural = naturalP
           , brackets = bracketsP
           , comma = commaP
           , commaSep = commaSepP
           , dot = dotP
           } = makeTokenParser langDef

-- | Main parser for Lang. TODO whitespace at the front and eof and the end.
expressionParser :: Parser Exp
expressionParser =
  try funParser <|>
  try litParser <|>
  try varParser <|>
  try appParser <|>
  try binParser <|>
  try uniParser <|>
  try ifParser

funParser :: Parser Exp
funParser =
  parensP $ do
    reservedP "fun"
    boundVar <- identifierP
    dotP
    body <- expressionParser
    return (Lam boundVar body)

appParser :: Parser Exp
appParser =
  parensP $ do
    fun <- expressionParser
    arg <- expressionParser
    return (fun :@ arg)

-- TODO forgot "Cons"
binParser :: Parser Exp
binParser =
  parensP $ do
    op <- operatorP
    case mapBinOp op of
      Just myOp -> do
        e1 <- expressionParser
        e2 <- expressionParser
        return (Bin myOp e1 e2)
      Nothing -> unexpected $ "Bin: Unkown operator: '" ++ op ++ "'"

mapBinOp :: String -> Maybe BinOp
mapBinOp "+" = Just Plus
mapBinOp "-" = Just Minus
mapBinOp "*" = Just Mult
mapBinOp "||" = Just Or
mapBinOp "&&" = Just And
mapBinOp "<=" = Just Lte
mapBinOp ">=" = Just Gte
mapBinOp "<" = Just Lt
mapBinOp ">" = Just Gt
mapBinOp "==" = Just Eq
mapBinOp _ = Nothing

uniParser :: Parser Exp
uniParser =
  parensP $
  (reservedP "not" >> expressionParser >>= return . (Uni Not)) <|>
  (reservedP "fst" >> expressionParser >>= return . (Uni Fst)) <|>
  (reservedP "snd" >> expressionParser >>= return . (Uni Snd)) <|>
  (reservedP "head" >> expressionParser >>= return . (Uni Head)) <|>
  (reservedP "tail" >> expressionParser >>= return . (Uni Tail))


-- I'm sure there is a better way to write these parsers. I'm just not good enough
-- with applicative functors X(
litParser :: Parser Exp
litParser =
  (naturalP >>= return . Lit) <|>
  (reservedP "true" >> return (Lit True)) <|>
  (reservedP "false" >> return (Lit False)) <|>
  (charLiteralP >>= return . Lit) <|>
  (stringLiteralP >>= return . Lit) <|>
  listParser <|>
  tupleParser

listParser :: Parser Exp
listParser = bracketsP (commaSepP expressionParser >>= return . makeList)

-- Given a list of expressions representing the parse of a list literal, return
-- it as a single list using our List data.
makeList :: [Exp] -> Exp
makeList [] = Nill
makeList (x : xs) = Bin Cons x (makeList xs)

tupleParser :: Parser Exp
tupleParser = parensP $ do
  t1 <- expressionParser
  commaP
  t2 <- expressionParser
  return (Bin Tup t1 t2)

varParser :: Parser Exp
varParser = identifierP >>= return . Var

ifParser :: Parser Exp
ifParser = parensP $ do
  reservedP "if"
  cond <- expressionParser
  e1 <- expressionParser
  e2 <- expressionParser
  return (If cond e1 e2)

-- Fix parser to take 
tryParse :: String -> Exp
tryParse input = case parse expressionParser "" input of
                            Left err -> error (show err)
                            Right exp  -> exp
