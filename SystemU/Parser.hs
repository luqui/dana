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
import Control.Monad.Fix
import Data.List (sort, sortBy)
import Data.Ord (comparing)

type Var = String
data FancyAST
    = Var Var
    | Type
    | Pi Var FancyAST FancyAST
    | Lam Var FancyAST FancyAST
    | App FancyAST FancyAST
    | Finite Int
    | Label Int Int
    | Case FancyAST FancyAST [FancyAST]
    | LetRec [(Var, FancyAST, FancyAST)] FancyAST
    | Partial FancyAST
    | Box FancyAST
    | Unbox FancyAST
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
convertFancy (Finite n) = return $ AST.Finite n
convertFancy (Label l n) = return $ AST.Label l n
convertFancy (Case scrutinee ret cases) = do
    scrutinee' <- convertFancy scrutinee
    ret' <- convertFancy ret
    cases' <- mapM convertFancy cases
    return $ AST.Case scrutinee' ret' cases'

-- lame, no mutual recursion!
convertFancy (LetRec [] body) = convertFancy body
convertFancy (LetRec defs body) = go [] defs
    where
    go accum [] = AST.LetRec (reverse accum) <$> convertFancy body
    go accum ((name,typ,def):defs) = do
        typ' <- convertFancy typ
        local (Map.insert name 0 . Map.map (+1)) $ do
            def' <- convertFancy def
            go ((typ',def'):accum) defs
convertFancy (Partial sub) = fmap AST.Partial (convertFancy sub)
convertFancy (Box sub) = fmap AST.Box (convertFancy sub)
convertFancy (Unbox sub) = fmap AST.Unbox (convertFancy sub)

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

list sep p = P.chainr ((:[]) <$> p) (string sep *> pure (++)) [] 
              <* P.optional (string sep)

reservedWords = ["Type", "_", "let", "in", "case", "of"]

word = lex $ do
    c0 <- P.satisfy (\c -> Char.isAlpha c || c == '_')
    cs <- P.munch (\c -> Char.isAlphaNum c || c == '_')
    return (c0:cs)

char = lex . P.char
string = lex . P.string
keyword s = do
    w <- word
    guard (w == s)
    return w

identifier = do
    w <- word
    guard . not $ w `elem` reservedWords
    return w

parenExpr = char '(' *> expr <* char ')'

boxExpr = char '[' *> (Box <$> expr) <* char ']'

termExpr = P.choice [ var, typeType, parenExpr, boxExpr, unboxExpr, 
                      partialExpr, finiteType, label, caseExpr ]

unboxExpr = char '!' *> (Unbox <$> termExpr)

partialExpr = char '$' *> (Partial <$> termExpr)

appExpr = P.chainl1 termExpr (pure App)

expr = P.choice [ piExpr, lambda, letrec ]

var = Var <$> identifier

typeType = keyword "Type" *> pure Type

int = lex $ read <$> P.munch1 Char.isDigit

finiteType = Finite <$> int

label = char '(' *> (Label <$> int <*> (char ':' *> int)) <* char ')'

caseExpr = Case <$> (string "case" *> expr) 
                <*> (string "=>" *> expr <* string "of")
                <*> (char '{' *> list ";" expr <* char '}')

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

letrec = keyword "let" *> 
         (LetRec <$> list ";" def
                 <*> (keyword "in" *> expr))
    where
    def = (,,) <$> identifier 
               <*> (char ':' *> expr)
               <*> (char '=' *> expr)

program = P.skipSpaces *> expr

parses s = [ toAST r | (r,"") <- P.readP_to_S program s ]

sortOn f = sortBy (comparing f)
