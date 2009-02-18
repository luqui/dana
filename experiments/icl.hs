import qualified Data.Map as Map
import Control.Monad.Reader
import Control.Monad.State

infixl 9 :%
data Term
    = Lam Term
    | Var Int
    | Neutral Int
    | Term :% Term
    | L
    | G
    deriving Show

type Proof = ReaderT (Map.Map Int Term) (State Int)

runProof :: Proof a -> a
runProof p = evalState (runReaderT p Map.empty) 0

newNeutral :: Proof Int
newNeutral = do
    n <- get
    put $! n+1
    return n

rwhnf :: Term -> Term
rwhnf (t :% u) =
    case rwhnf t of
        Lam z -> subst 0 u z
        t'    -> t' :% u
rwhnf x = x

shiftUp n (Lam t) = Lam (shiftUp (n+1) t)
shiftUp n (Var z) | n <= z = Var (z+1)
shiftUp n (t :% u) = shiftUp n t :% shiftUp n u
shiftUp n x = x

subst n for (Lam t) = Lam (subst (n+1) (shiftUp 0 for) t)
subst n for (Var n') | n == n' = for
subst n for (t :% u) = subst n for t :% subst n for u
subst n for x = x

prove :: Term -> Proof ()
prove = go . rwhnf
    where
    go (t :% y) | Neutral n <- rwhnf y = do
        ty <- asks (Map.lookup n)
        case ty of
            Nothing -> fail $ "Couldn't prove " ++ show (t :% Neutral n) ++ ": " ++ show (Neutral n) ++ " not in environment"
            Just ty' -> unless (betaEq ty' t) . fail $ "Could not unify " ++ show t ++ " and " ++ show ty'
    go (G :% x :% y :% z) = do
        prove (L :% x)
        var <- newNeutral
        let n = Neutral var
        local (Map.insert var x) . prove . rwhnf $ y :% n :% (z :% n)
    go (L :% x) =
        case rwhnf x of
            L -> return ()
            G :% x :% y -> do
                prove (L :% x)
                var <- newNeutral
                local (Map.insert var x) $ prove (L :% (y :% Neutral var))
            _ -> fail $ "Couldn't prove " ++ show (L :% x)
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
