module IXi.Term 
    ( Name(..), Term(..)
    , quote, subst, substNamed
    , unfree, free, freeNames
    , Conversion, convFrom, convTo
    , convId, convSym, convTrans
    , convBeta, convEta
    )
where

import Control.Applicative
import Data.Maybe (isNothing)
import qualified Data.Set as Set

newtype Name = Name Integer
    deriving (Eq,Ord)

infixl 9 :%
data Term
    = Lambda Term
    | Term :% Term
    | Var Int
    | NameVar Name
    | Xi | H
    deriving (Eq,Ord)


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


data Conversion = Term :<-> Term

convFrom (a :<-> b) = a
convTo (a :<-> b) = b

convId t = t :<-> t

convSym (a :<-> b) = b :<-> a

convTrans (a :<-> b) (b' :<-> c)
    | b == b'   = Just (a :<-> c)
    | otherwise = Nothing

convBeta term@(Lambda t :% u) = Just (term :<-> subst 0 u t)
convBeta _ = Nothing

convEta term = term :<-> Lambda (quote 0 term :% Var 0)
