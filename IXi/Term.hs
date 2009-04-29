module IXi.Term 
    ( Term(..)
    , showTerm
    , quote, subst, substNamed
    , unfree, free, freeNames

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

infixl 9 :%
data Term name
    = Lambda (Term name)
    | Term name :% Term name
    | Var Int
    | NameVar name
    | Xi | H
    deriving (Eq,Ord)

instance (Show name) => Show (Term name) where
    show = showTerm show

showTerm :: (name -> String) -> Term name -> String
showTerm namefunc = go False False
    where
    go ap lp (Lambda t) = parens lp $ "\\. " ++ go False False t
    go ap lp (t :% u) = parens ap $ go False True t ++ " " ++ go True True u
    go ap lp (Var z) = show z
    go ap lp (NameVar n) = namefunc n
    go ap lp Xi = "Xi"
    go ap lp H = "H"

    parens True = \x -> "(" ++ x ++ ")"
    parens False = id


quote :: Int -> Term n -> Term n
quote n (Lambda t) = Lambda (quote (n+1) t)
quote n (a :% b) = quote n a :% quote n b
quote n (Var v) | v < n     = Var v
                | otherwise = Var (v+1)
quote n other = other


subst :: Int -> Term n -> Term n -> Term n
subst n with (Lambda t) = Lambda (subst (n+1) (quote 0 with) t)
subst n with (t :% u) = subst n with t :% subst n with u
subst n with (Var v) =
    case v `compare` n of
        LT -> Var v
        EQ -> with
        GT -> Var (v-1)
subst n with other = other
        
substNamed :: (Eq n) => n -> Term n -> Term n -> Term n
substNamed m with (Lambda t) = Lambda (substNamed m (quote 0 with) t)
substNamed m with (a :% b) = substNamed m with a :% substNamed m with b
substNamed m with (NameVar n) | m == n    = with
                              | otherwise = NameVar n
substNamed m with other = other

unfree :: Int -> Term n -> Maybe (Term n)
unfree n (Lambda t) = Lambda <$> unfree (n+1) t
unfree n (t :% u) = liftA2 (:%) (unfree n t) (unfree n u)
unfree n (Var v)
    = case v `compare` n of
        LT -> Just (Var v)
        EQ -> Nothing
        GT -> Just (Var (v-1))
unfree n z = Just z

free :: Int -> Term n -> Bool
free n t = isNothing (unfree n t)

freeNames :: (Ord n) => Term n -> Set.Set n
freeNames (Lambda t) = freeNames t
freeNames (t :% u) = freeNames t `Set.union` freeNames u
freeNames (NameVar n) = Set.singleton n
freeNames _ = Set.empty


newtype Conversion n = Conversion { convert :: Term n -> Maybe (Term n) }

instance Monoid (Conversion n) where
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

-- (\x. A) Z ((\x. B) Z) -> (\x. A x (B x)) Z
convExpandProj :: Eq n => Conversion n
convExpandProj = Conversion $ \t -> 
    case t of
        Lambda a :% z :% (Lambda b :% z') | z == z' -> 
            Just (Lambda (a :% Var 0 :% (b :% Var 0)) :% z)
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
        Lambda (Lambda a :% c) | Just c' <- unfree 0 c -> 
            Just (Lambda (Lambda (subst 0 (Var 1) a)) :% c')
        _ -> Nothing
