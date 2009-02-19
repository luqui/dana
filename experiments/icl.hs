-- System IG, from the paper _Systems of Illative Combinatory Logic
-- complete for first-order propositional and predicate calculus_,
-- Barendregt, Bunder, Dekkers 1993
--
-- The rules follow:
-- (Ai)   X in Δ                                          =>  Δ |- X
-- (Aβη)  Δ |- X; X =βη Y                                 =>  Δ |- Y
-- (Ge)   Δ |- GXYZ; Δ |- XV                              =>  Δ |- YV(ZV)
-- (Gi)   Δ |- Lx; Δ,Xx |- Yx(Zx); x not in FV(Δ,X,Y,Z)   =>  Δ |- GXYZ
-- (GL)   Δ |- Lx; Δ,Xx |- L(Yx); x not in FV(Δ,X,Y)      =>  Δ |- L(GXY)

import qualified Data.Map as Map
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Error
import Debug.Trace

infixl 9 :%
data Term
    = Lam Term
    | Var Int
    | Neutral Int
    | Term :% Term
    | L
    | G
    deriving (Show)

-- This first section implements Aβη.  (==) is β-equality.
instance Eq Term where
    t == u = go (rwhnf t) (rwhnf u)
        where
        go (Lam t) (Lam u) = t == u
        go (Var i) (Var j) = i == j
        go (Neutral i) (Neutral j) = i == j
        go (t :% u) (t' :% u') = go t t' && u == u'
        go L L = True
        go G G = True
        go _ _ = False

-- Reduce a term to weak head normal form.
rwhnf :: Term -> Term
rwhnf (t :% u) =
    case rwhnf t of
        Lam z -> rwhnf (subst 0 u z)
        t'    -> t' :% u
rwhnf x = x

quote n (Lam t) = Lam (quote (n+1) t)
quote n (Var z) | n <= z = Var (z+1)
quote n (t :% u) = quote n t :% quote n u
quote n x = x

subst n with (Lam t) = Lam (subst (n+1) (quote 0 with) t)
subst n with (Var n') =
    case n' `compare` n of
        LT -> Var n'
        EQ -> with
        GT -> Var (n'-1)
subst n with (t :% u) = subst n with t :% subst n with u
subst n with x = x

-- This second section implements the proof search algorithm.
type Proof = ErrorT String (ReaderT (Map.Map Int Term) (State Int))

runProof :: Proof a -> Either String a
runProof p = evalState (runReaderT (runErrorT p) Map.empty) 0

onFailure e m = catchError m (const (fail e))

neutral :: Term -> Maybe (Proof Term)
neutral = go
    where
    go (Neutral n) = return . lift $ asks (Map.! n)
    go (f :% x) = do
        fty <- neutral f
        return $ onFailure ("Cannot apply non-function type in " ++ show (f :% x)) $ do
            G :% dom :% cod <- fty
            prove (dom :% x) >> return (cod :% x)
    go _ = Nothing

unify :: Term -> Term -> Proof ()
unify t u = unless (t == u) . fail $ 
                "Could not unify: " ++ show t ++ " = " ++ show u

withNeutral :: Term -> (Term -> Proof a) -> Proof a
withNeutral rng f = do
    n <- get
    put $! n+1
    local (Map.insert n rng) $ f (Neutral n)

prove :: Term -> Proof ()
prove (L :% L) = return ()  -- inconsistent impredicativity axiom
prove (f :% x) = do
    prove (L :% f)
    proveWF f x

-- proveWF f x  proves the application f x, under the
-- assumption that L f has already been proven.
proveWF f n | Just typeof <- neutral n = 
    unify f =<< typeof
proveWF (G :% x :% y) (Lam z) = withNeutral x $ \n -> 
    prove . rwhnf $ y :% n :% subst 0 n z
proveWF L (G :% x :% y) = do
    prove (L :% x)
    proveWF (G :% x :% Lam L) y
proveWF t u = fail $ "Couldn't prove " ++ show (t :% u)
