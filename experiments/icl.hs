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

typeOf :: Term -> Proof (Maybe Term)
typeOf = go . rwhnf
    where
    go (Neutral n) = do
        ty <- asks (Map.lookup n)
        case ty of
            Nothing -> fail $ show (Neutral n) ++ " not in environment"
            Just ty' -> return (Just ty')
    go (f :% x) = do
        mtf <- typeOf f
        case mtf of
            Nothing -> return Nothing
            Just tf -> case rwhnf tf of
                           G :% dom :% cod -> do
                               prove (dom :% x)
                               return (Just (cod :% x))
                           t -> fail $ "Cannot apply nonfunction type: " ++ show t
    go _ = return Nothing

unify :: Term -> Term -> Proof ()
unify t u = unless (betaEq t u) . fail $ "Could not unify: " ++ show t ++ " = " ++ show u

prove :: Term -> Proof ()
prove = go . rwhnf
    where
    go (G :% x :% y :% z) = do
        prove (L :% x)
        var <- newNeutral
        let n = Neutral var
        local (Map.insert var x) . prove . rwhnf $ y :% n :% (z :% n)
    go (f :% x) = do
        case (f, rwhnf x) of
            (f, Neutral n) -> do
                nty <- asks (Map.lookup n)
                maybe (fail $ show n ++ " not in environment") (unify f) nty
            (f, z :% v) -> do
                mzty <- typeOf z
                case mzty of
                    Just (G :% x' :% y') -> unify f (y' :% v)
                    Just t -> fail $ "Couldn't apply non-function type: " ++ show t
                    Nothing -> case (f, z :% v) of
                                   (L, G :% t :% u) -> do
                                       unify f L
                                       prove (L :% t)
                                       var <- newNeutral
                                       local (Map.insert var t) $ prove (L :% (u :% Neutral var))
                                   t -> fail $ "Don't know how to prove: " ++ show (f :% (z :% v))
            (L, L) -> return ()
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
