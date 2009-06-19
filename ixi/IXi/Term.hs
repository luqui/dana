module IXi.Term 
    ( Term(..)
    , showTermWith, showTerm
    , quote, subst, substNamed
    , unfree, free, freeNames, nameFree
    , swapVars, abstract

    , Name, safeName, safeName'
    )
where

import Control.Applicative
import Data.Maybe (isNothing)
import Data.Monoid (Monoid(..))
import Control.Monad ((>=>))
import qualified Data.Set as Set

newtype Name = Name Integer
    deriving (Eq,Ord)

instance Enum Name where
    fromEnum (Name n) = fromEnum n
    toEnum = Name . toEnum

instance Show Name where
    show (Name z) = "?" ++ show z

infixl 9 :%
data Term
    = Lambda Term
    | Term :% Term
    | Var Int
    | NameVar Name
    | Xi | H
    deriving (Eq,Ord)

instance Show Term where
    show = showTerm

showTermWith :: (Name -> String) -> Term -> String
showTermWith nameRender = go False False
    where
    go ap lp (Lambda t) = parens lp $ "\\. " ++ go False False t
    go ap lp (t :% u) = parens ap $ go False True t ++ " " ++ go True True u
    go ap lp (Var z) = show z
    go ap lp (NameVar n) = nameRender n
    go ap lp Xi = "Xi"
    go ap lp H = "H"

    parens True = \x -> "(" ++ x ++ ")"
    parens False = id

showTerm :: Term -> String
showTerm = showTermWith show

-- returns the least name such that it and all its successors
-- are unused in the term
safeName :: Term -> Name
safeName (Lambda t) = safeName t
safeName (t :% u) = Name (max a b)
    where Name a = safeName t
          Name b = safeName u
safeName (NameVar n) = succ n
safeName _ = Name 0

safeName' :: [Term] -> Name
safeName' = foldr max' (Name 0) . map safeName
    where
    max' (Name a) (Name b) = Name (max a b)

quote :: Int -> Term -> Term
quote n (Lambda t) = Lambda (quote (n+1) t)
quote n (a :% b) = quote n a :% quote n b
quote n (Var v) | v < n     = Var v
                | otherwise = Var (v+1)
quote n other = other


subst :: Int -> Term -> Term -> Term
subst n with (Lambda t) = Lambda (subst (n+1) (quote 0 with) t)
subst n with (t :% u) = subst n with t :% subst n with u
subst n with (Var v) =
    case v `compare` n of
        LT -> Var v
        EQ -> with
        GT -> Var (v-1)
subst n with other = other
        
substNamed :: Name -> Term -> Term -> Term
substNamed m with (Lambda t) = Lambda (substNamed m (quote 0 with) t)
substNamed m with (a :% b) = substNamed m with a :% substNamed m with b
substNamed m with (NameVar n) | m == n    = with
                              | otherwise = NameVar n
substNamed m with other = other

unfree :: Int -> Term -> Maybe Term
unfree n (Lambda t) = Lambda <$> unfree (n+1) t
unfree n (t :% u) = liftA2 (:%) (unfree n t) (unfree n u)
unfree n (Var v)
    = case v `compare` n of
        LT -> Just (Var v)
        EQ -> Nothing
        GT -> Just (Var (v-1))
unfree n z = Just z

free :: Int -> Term -> Bool
free n t = isNothing (unfree n t)

freeNames :: Term -> Set.Set Name
freeNames (Lambda t) = freeNames t
freeNames (t :% u) = freeNames t `Set.union` freeNames u
freeNames (NameVar n) = Set.singleton n
freeNames _ = Set.empty

nameFree :: Name -> Term -> Bool
nameFree n t = n `Set.member` freeNames t

-- swaps indices 0 and 1
swapVars :: Term -> Term
swapVars = subst 0 (Var 1) . quote 2

abstract :: Name -> Term -> Term
abstract name = go 0
    where
    go n (Lambda t) = Lambda (go (n+1) t)
    go n (t :% u) = go n t :% go n u
    go n (Var z) | z < n = Var z
                 | otherwise = Var (z+1)
    go n (NameVar nm) | nm == name = Var n
                      | otherwise = NameVar nm
    go n Xi = Xi
    go n H = H
