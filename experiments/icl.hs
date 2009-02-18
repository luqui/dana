-- System IG, from the paper _Systems of Illative Combinatory Logic
-- complete for first-order propositional and predicate calculus_,
-- Barendregt, Bunder, Dekkers 1993

import qualified Data.Map as Map
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Maybe
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

type Proof = ErrorT String (ReaderT (Map.Map Int Term) (State Int))

runProof :: Proof a -> Either String a
runProof p = evalState (runReaderT (runErrorT p) Map.empty) 0

newNeutral :: Proof Int
newNeutral = do
    n <- get
    put $! n+1
    return n

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

subst n for (Lam t) = Lam (subst (n+1) (quote 0 for) t)
subst n for (Var n') =
    case n' `compare` n of
        LT -> Var n'
        EQ -> for
        GT -> Var (n'-1)
subst n for (t :% u) = subst n for t :% subst n for u
subst n for x = x

onFailure e m = catchError m (const (fail e))

-- returns Just if the term given is a neutral normal form 
-- (and thus has a type in the envt), Nothing otherwise
typeOf :: Term -> Maybe (Proof Term)
typeOf = go . rwhnf
    where
    go (Neutral n) = return . lift $ asks (Map.! n)
    go (f :% x) = do
        fty <- (fmap.fmap) rwhnf (typeOf f)
        return $ onFailure "Cannot apply nonfunction type" $ do
            G :% dom :% cod <- fty
            prove (dom :% x) >> return (cod :% x)
    go _ = Nothing

unify :: Term -> Term -> Proof ()
unify t u = unless (betaEq t u) . fail $ "Could not unify: " ++ show t ++ " = " ++ show u

prove :: Term -> Proof ()
prove = go . rwhnf
    where
    go (G :% x :% y :% z) = do                -- rule Gi
        prove (L :% x)
        var <- newNeutral
        let n = Neutral var
        local (Map.insert var x) . prove . rwhnf $ y :% n :% (z :% n)
    go (f :% x) = do
        case (f, rwhnf x) of
            (f, Neutral n) -> do              -- first universal rule (unnamed)
                nty <- asks (Map.lookup n)
                maybe (fail $ show n ++ " not in environment") (unify f) nty
            (f, z :% v) | Just typeof <- typeOf z -> do -- rule Ge
                zty <- typeof
                case zty of
                    G :% x' :% y' -> unify f (y' :% v)
                    t -> fail $ "Couldn't apply non-function type: " ++ show t
            (L, L) -> return ()               -- Type:Type, my own inconsistency
            (L, G :% t :% u) -> do            -- rule GL
                prove (L :% t)
                var <- newNeutral
                local (Map.insert var t) $ prove (L :% (u :% Neutral var))
            t -> fail $ "Don't know how to prove: " ++ show (f :% x)
    go t = fail $ "Couldn't prove " ++ show t ++ ": no applicable rule"

betaEq :: Term -> Term -> Bool
betaEq t u = go (rwhnf t) (rwhnf u)
    where
    go (Lam t) (Lam u) = betaEq t u
    go (Var i) (Var j) = i == j
    go (Neutral i) (Neutral j) = i == j
    go (t :% u) (t' :% u') = go t t' && betaEq u u'
    go L L = True
    go G G = True
    go _ _ = False
