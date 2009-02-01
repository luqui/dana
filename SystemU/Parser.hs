module SystemU.Parser where

import qualified Text.ParserCombinators.ReadP as P
import Control.Applicative
import Control.Monad
import qualified Data.Char as Char
import Prelude hiding (lex)

type Var = String
data FancyAST
    = Var Var
    | Type
    | Pi Var FancyAST FancyAST
    | Lam Var FancyAST FancyAST
    | App FancyAST FancyAST
    deriving Show

type Parser = P.ReadP

instance Applicative P.ReadP where
    pure = return
    (<*>) = ap

lex p = do
    ret <- p
    P.skipSpaces
    return ret

reservedWords = ["Type", "_"]

word = lex $ do
    c0 <- P.satisfy (\c -> Char.isAlpha c || c == '_')
    cs <- P.munch (\c -> Char.isAlphaNum c || c == '_')
    return (c0:cs)

char = lex . P.char
string = lex . P.string

identifier = do
    w <- word
    guard . not $ w `elem` reservedWords
    return w

parenExpr = char '(' *> expr <* char ')'

termExpr = P.choice [ var, typeType, parenExpr ]

appExpr = P.chainl1 termExpr (pure App)

expr = P.choice [ piExpr, lambda ]

var = Var <$> identifier

typeType = do
    w <- word
    guard (w == "Type")
    return Type

piExpr = P.choice [ dep, arrow, appExpr ]
    where
    dep = Pi <$> (char '(' *> identifier)
             <*> (char ':' *> expr)
             <*> (char ')' *> string "->" *> piExpr)
    arrow = Pi "_" <$> appExpr
                   <*> (string "->" *> piExpr)

lambda = Lam <$> (char '\\' *> identifier)
             <*> (char ':' *> expr)
             <*> (char '.' *> expr)

parse s = [ r | (r,"") <- P.readP_to_S expr s ]

