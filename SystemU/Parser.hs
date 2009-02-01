module SystemU.Parser 
    ( parses )
where

import qualified Text.ParserCombinators.ReadP as P
import Control.Applicative
import Control.Monad
import qualified Data.Char as Char
import Prelude hiding (lex)
import qualified SystemU.AST as AST
import Control.Monad.Reader
import qualified Data.Map as Map

type Var = String
data FancyAST
    = Var Var
    | Type
    | Pi Var FancyAST FancyAST
    | Lam Var FancyAST FancyAST
    | App FancyAST FancyAST
    deriving Show


convertFancy :: FancyAST -> Reader (Map.Map Var Int) AST.AST
convertFancy (Var n) = do
    env <- ask
    return $ case Map.lookup n env of
        Nothing -> error $ "Undeclared variable: '" ++ n ++ "'"
        Just ix -> AST.Var ix
convertFancy Type = return AST.Type
convertFancy (Pi v dom rngf) = do
    dom' <- convertFancy dom
    rngf' <- local (Map.insert v 0 . Map.map (+1)) $ convertFancy rngf
    return $ AST.Pi dom' rngf'
convertFancy (Lam v dom body) = do
    dom' <- convertFancy dom
    body' <- local (Map.insert v 0 . Map.map (+1)) $ convertFancy body
    return $ AST.Lam dom' body'
convertFancy (App f x) = do
    f' <- convertFancy f
    x' <- convertFancy x
    return $ AST.App f' x'

toAST :: FancyAST -> AST.AST
toAST fancy = runReader (convertFancy fancy) Map.empty


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

program = P.skipSpaces *> expr

parses s = [ toAST r | (r,"") <- P.readP_to_S program s ]

