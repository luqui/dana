-- System IG, from the paper _Systems of Illative Combinatory Logic
-- complete for first-order propositional and predicate calculus_,
-- Barendregt, Bunder, Dekkers 1993

module SystemIG.Calculus 
    ( Term(..)
    , subst
    , Neutral(..)
    
    , Conversion
    , convTerms, convId, convCompose, convFlip
    , convBeta, convEta, convAppL, convAppR
    , convChain
    
    , Sequent
    , hypotheses, conclusion
    , hypothesis, conversion, apply, piType, piWF
    )
where

import Control.Applicative
import Data.List (sort, intercalate)

newtype Neutral = MkNeutral Integer
    deriving (Eq, Ord)

infixl 9 :*
data Term
    = Lam Term
    | Term :* Term
    | Var Int
    | Neutral Neutral
    | G | L
    deriving (Eq, Ord)

instance Show Term where
    show = show' False False
        where
        show' ap lp (Lam t) = parens lp $ "\\." ++ show' False False t
        show' ap lp (t :* u) = parens ap $ show' False True t ++ " " ++ show' True True u
        show' ap lp (Var z) = show z
        show' ap lp (Neutral (MkNeutral n)) = "@" ++ show n
        show' ap lp G = "G"
        show' ap lp L = "L"

        parens True e = "(" ++ e ++ ")"
        parens False e = e


incr :: Int -> Term -> Term
incr n (Lam t) = Lam (incr (n+1) t)
incr n (t :* u) = incr n t :* incr n u
incr n (Var k) | n <= k    = Var (k+1)
               | otherwise = Var k
incr n x = x

subst :: Int -> Term -> Term -> Term
subst n with (Lam t) = Lam (subst (n+1) (incr 0 with) t)
subst n with (t :* u) = subst n with t :* subst n with u
subst n with (Var z) | z == n = with
                     | z < n  = Var z
                     | z > n  = Var (z-1)
subst n with x = x

decr :: Int -> Term -> Maybe Term
decr n (Lam t) = Lam <$> decr (n+1) t
decr n (t :* u) = liftA2 (:*) (decr n t) (decr n u)
decr n (Var z) | z == n = Nothing
               | z < n  = Just (Var z)
               | z > n  = Just (Var (z-1))
decr n t = Just t

neutralFree :: Neutral -> Term -> Bool
neutralFree n (Lam t) = neutralFree n t
neutralFree n (t :* u) = neutralFree n t || neutralFree n u
neutralFree n (Neutral n') = n == n'
neutralFree n _ = False


data Conversion = Term :<-> Term

instance Show Conversion where
    show (a :<-> b) = show a ++ " <-> " ++ show b


convTerms :: Conversion -> (Term,Term)
convTerms (a :<-> b) = (a,b)

convId :: Term -> Conversion
convId t = t :<-> t

convCompose :: Conversion -> Conversion -> Maybe Conversion
convCompose (a :<-> b) (b' :<-> c) | b == b' = Just (a :<-> c)
                                   | otherwise = Nothing

convChain :: [Conversion] -> Maybe Conversion
convChain [] = Nothing
convChain [x] = Just x
convChain (x:xs) = convCompose x =<< convChain xs

convFlip :: Conversion -> Conversion
convFlip (a :<-> b) = b :<-> a

convBeta :: Term -> Maybe Conversion
convBeta (Lam t :* x) = Just $ (Lam t :* x) :<-> subst 0 x t
convBeta _ = Nothing

convEta :: Term -> Maybe Conversion
convEta (Lam (t :* Var 0)) = (Lam (t :* Var 0) :<->) <$> decr 0 t
convEta _ = Nothing

convAppL :: Conversion -> Term -> Conversion
convAppL (a :<-> b) t = (a :* t) :<-> (b :* t)

convAppR :: Term -> Conversion -> Conversion
convAppR t (a :<-> b) = (t :* a) :<-> (t :* b)


-- The rules follow:
-- (Ai)   X in Δ                                          =>  Δ |- X
-- (Aβη)  Δ |- X; X =βη Y                                 =>  Δ |- Y
-- (Ge)   Δ |- GXYZ; Δ |- XV                              =>  Δ |- YV(ZV)
-- (Gi)   Δ |- Lx; Δ,Xx |- Yx(Zx); x not in FV(Δ,X,Y,Z)   =>  Δ |- GXYZ
-- (GL)   Δ |- Lx; Δ,Xx |- L(Yx); x not in FV(Δ,X,Y)      =>  Δ |- L(GXY)


-- invariant: hypotheses are sorted, and the sequent is valid
data Sequent = [Term] :|- Term

instance Show Sequent where
    show (hs :|- t) = intercalate ", " (map show hs) ++ " |- " ++ show t

hypotheses :: Sequent -> [Term]
hypotheses (hs :|- t) = sort hs

conclusion :: Sequent -> Term
conclusion (hs :|- t) = t


-- (Ai)   X in Δ => Δ |- X
hypothesis :: [Term] -> Int -> Sequent
hypothesis hs n = sort hs :|- (hs !! n)

-- (Aβη)  Δ |- X; X =βη Y   => Δ |- Y
conversion :: Conversion -> Sequent -> Maybe Sequent
conversion (a :<-> b) (hs :|- t) | t == a = Just (hs :|- b)
                                 | otherwise = Nothing

-- (Ge)   Δ |- GXYZ; Δ |- XV    => Δ |- YV(ZV)
apply :: Sequent -> Sequent -> Maybe Sequent
apply (hs :|- (G :* x :* y :* z)) (hs' :|- (x' :* v))
    | hs == hs' && x == x'  = Just (hs :|- (y :* v :* (z :* v)))
    | otherwise = Nothing

-- (Gi)   Δ |- Lx; Δ,Xx |- Yx(Zx); x not in FV(Δ,X,Y,Z)   =>  Δ |- GXYZ
piType :: Term -> Sequent -> Sequent -> Maybe Sequent
piType x (hs :|- (L :* Neutral n)) (hs' :|- (y :* Neutral n' :* (z :* Neutral n'')))
    | n == n' && n' == n'' 
    && all (not . neutralFree n) (x : y : z : hs')
    && hs' == sort ((x :* Neutral n) : hs)
                = Just (hs :|- (G :* x :* y :* z))
    | otherwise = Nothing

-- (GL)   Δ |- Lx; Δ,Xx |- L(Yx); x not in FV(Δ,X,Y)      =>  Δ |- L(GXY)
piWF :: Term -> Sequent -> Sequent -> Maybe Sequent
piWF x (hs :|- (L :* Neutral n)) (hs' :|- (L :* (y :* Neutral n')))
    | n == n'
    && all (not . neutralFree n) (x : y : hs')
    && hs' == sort ((x :* Neutral n) : hs)
                = Just (hs :|- (L :* (G :* x :* y)))
    | otherwise = Nothing
