-- System IG, from the paper _Systems of Illative Combinatory Logic
-- complete for first-order propositional and predicate calculus_,
-- Barendregt, Bunder, Dekkers 1993

import qualified Data.Map as Map
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Error

infixl 9 :%
data Term
    = Lam Term
    | Var Int
    | Neutral Int
    | Term :% Term
    | L
    | G
    deriving Show

-- Beta equality
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

type Proof = ErrorT String (ReaderT (Map.Map Int Term) (State Int))

runProof :: Proof a -> Either String a
runProof p = evalState (runReaderT (runErrorT p) Map.empty) 0

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

onFailure e m = catchError m (const (fail e))

-- returns Just if the term given is a neutral normal form 
-- (and thus has a type in the envt), Nothing otherwise
typeOf :: Term -> Maybe (Proof Term)
typeOf = go . rwhnf
    where
    go (Neutral n) = return . lift $ asks (Map.! n)
    go (f :% x) = do
        fty <- typeOf f
        return $ onFailure ("Cannot apply nonfunction type in " ++ show (f :% x)) $ do
            G :% dom :% cod <- rwhnf `fmap` fty
            prove (dom :% x) >> return (cod :% x)
    go _ = Nothing

unify :: Term -> Term -> Proof ()
unify t u = unless (t == u) . fail $ "Could not unify: " ++ show t ++ " = " ++ show u

withNeutral :: Term -> (Term -> Proof a) -> Proof a
withNeutral rng f = do
    n <- get
    put $! n+1
    local (Map.insert n rng) $ f (Neutral n)

prove :: Term -> Proof ()
prove = go . rwhnf
    where
    go (G :% x :% y :% z) = do  -- rule Gi
        prove (L :% x)
        withNeutral x $ \n -> prove . rwhnf $ y :% n :% (z :% n)
    go (fin :% xin) = do
        case (fin, rwhnf xin) of
            -- first rule (X in ? => ? |- X)
            (f, Neutral n) -> unify f =<< asks (Map.! n)
            -- rule Ge
            (f, z :% v) | Just typeof <- typeOf z -> 
                onFailure ("Couldn't apply non-function type: " ++ show z) $ do
                    G :% x :% y <- typeof
                    unify f (y :% v)
            -- Type:Type, my own contribution.  Causes inconsistency by Girard.
            -- Remove to make consistent, but you need explicit external "L a"
            -- assumptions to do anything useful.
            (L, L) -> return ()
            -- rule GL
            (L, G :% x :% y) -> do
                prove (L :% x)
                withNeutral x $ \z -> prove (L :% (y :% z))
            t -> fail $ "Don't know how to prove: " ++ show (fin :% xin)
    go t = fail $ "Couldn't prove " ++ show t ++ ": no applicable rule"
