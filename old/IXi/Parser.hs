module IXi.Parser (parseTerm, showTerm, showDTerm, needsParens) where

import IXi.Term
import IXi.TermZipper
import Text.ParserCombinators.ReadP
import Control.Applicative
import Control.Monad (ap, guard)
import qualified Data.Char as Char

instance Applicative ReadP where
    pure = return
    (<*>) = ap


tok p = p <* skipSpaces

ident = tok (munch1 Char.isAlphaNum)

p `suchThat` pred = do
    x <- p
    guard (pred x)
    return x

varName = ident `suchThat` (\x -> x /= "X" && x /= "H")
var = Var <$> varName

parseX = (ident `suchThat` (== "X")) *> pure Xi
parseH = (ident `suchThat` (== "H")) *> pure H

atom = choice [ var
              , parseX
              , parseH
              , tok (char '(') *> expr <* tok (char ')')
              ]

lambda = Lam <$> (tok (char '\\') *> varName) <*> (tok (char '.') *> expr)

expr = lambda +++ (foldl1 (:%) <$> many1 atom)

parseTerm s = 
    case [ x | (x,"") <- readP_to_S expr s ] of
        [] -> Nothing
        [x] -> Just x
        _ -> error "Ambiguous parse"


showTerm = go False False
    where
    go pa pl (Lam v t) = parens pl $ "\\" ++ v ++ ". " ++ go False False t
    go pa pl (Var v) = v
    go pa pl (t :% u) = parens pa $ go False True t ++ " " ++ go True True u
    go pa pl H = "H"
    go pa pl Xi = "X"

    parens True = \x -> "(" ++ x ++ ")"
    parens False = id


showDTerm :: DTerm -> String -> String
showDTerm DTop s = s
showDTerm (DLam v cx) s = showDTerm cx $
    case cx of
        DLam {} -> w
        DTop {} -> w
        DAppL {} -> "(" ++ w ++ ")"
        DAppR {} -> "(" ++ w ++ ")"
    where w = "\\" ++ v ++ ". " ++ s
showDTerm (DAppL cx r) s = showDTerm cx $
    case cx of
        DAppR {} -> "(" ++ w ++ ")"
        _ -> w
    where w = s ++ " " ++ showTerm r
showDTerm (DAppR l cx) s = showDTerm cx (showTerm l ++ " " ++ s)


needsParens :: DTerm -> Term -> Bool
needsParens (DAppL {}) (Lam {}) = True
needsParens (DAppR {}) (Lam {}) = True
needsParens (DAppR {}) ((:%) {}) = True
needsParens _ _ = False
