module IXi.Term 
    ( Term(..)
    , showTerm
    , quote, subst, substNamed
    , unfree, free, freeNames

    , Name, safeName

    , Conversion, convert
    , convId, convTrans
    , convInLambda, convInAppL, convInAppR
    , convEtaContract, convEtaExpand
    , convBetaReduce

    , convExpandId, convExpandConst
    , convExpandProj, convExpandLeft, convExpandRight
    , convExpandLambda
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

showTerm :: Term -> String
showTerm = go False False
    where
    go ap lp (Lambda t) = parens lp $ "\\. " ++ go False False t
    go ap lp (t :% u) = parens ap $ go False True t ++ " " ++ go True True u
    go ap lp (Var z) = show z
    go ap lp (NameVar n) = show n
    go ap lp Xi = "Xi"
    go ap lp H = "H"

    parens True = \x -> "(" ++ x ++ ")"
    parens False = id

-- returns the least name such that it and all its successors
-- are unused in the term
safeName :: Term -> Name
safeName (Lambda t) = safeName t
safeName (t :% u) = Name (max a b)
    where Name a = safeName t
          Name b = safeName u
safeName (NameVar n) = succ n
safeName _ = Name 0

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


newtype Conversion = Conversion { convert :: Term -> Maybe Term }

instance Monoid Conversion where
    mempty = convId
    mappend = convTrans

convId = Conversion Just
convTrans f g = Conversion (convert f >=> convert g)

convInLambda conv = Conversion $ \t ->
    case t of
        Lambda t' -> Lambda <$> convert conv t'
        _ -> Nothing

convInAppL conv = Conversion $ \t ->
    case t of
        a :% b -> (:% b) <$> convert conv a
        _ -> Nothing

convInAppR conv = Conversion $ \t ->
    case t of
        a :% b -> (a :%) <$> convert conv b
        _ -> Nothing

convEtaContract = Conversion $ \t ->
    case t of
        Lambda (a :% Var 0) -> unfree 0 a
        _ -> Nothing

convEtaExpand = Conversion $ \t -> Just (Lambda (quote 0 t :% Var 0))

convBetaReduce = Conversion $ \t ->
    case t of
        Lambda a :% b -> Just (subst 0 b a)
        _ -> Nothing

-- X -> (\x. x) X
convExpandId = Conversion $ \t -> Just (Lambda (Var 0) :% t)
-- X -> (\x. X) Y
convExpandConst y = Conversion $ \t -> Just (Lambda (quote 0 t) :% y)

-- (\x. A) Z ((\x. B) Z) -> (\x. A B) Z
convExpandProj = Conversion $ \t -> 
    case t of
        Lambda a :% z :% (Lambda b :% z') | z == z' -> 
            Just (Lambda (a :% b) :% z)
        _ -> Nothing

-- (\x. A) C B -> (\x. A B) C
convExpandLeft = Conversion $ \t ->
    case t of
        Lambda a :% c :% b -> Just (Lambda (a :% quote 0 b) :% c)
        _ -> Nothing

-- A ((\x. B) C) -> (\x. A B) C
convExpandRight = Conversion $ \t ->
    case t of
        a :% (Lambda b :% c) -> Just (Lambda (quote 0 a :% b) :% c)
        _ -> Nothing

-- \y. (\x. A) C -> (\x. \y. A) C      (y not free in C)
convExpandLambda = Conversion $ \t ->
    case t of
        Lambda (Lambda a :% c) ->
            (Lambda (Lambda (subst 0 (Var 1) a)) :%) <$> (unfree 0 c)
        _ -> Nothing
