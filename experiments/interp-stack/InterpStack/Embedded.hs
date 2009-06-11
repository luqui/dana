module InterpStack.Embedded (embeddedInterp) where

import InterpStack.Exp
import Unsafe.Coerce
import GHC.Prim (Any)
import Control.Applicative

infixl 9 `SApp`
data AST 
    = SLam AST
    | SVar Int
    | SApp AST AST
    | SPrim Any

makeAST :: (Value a) => Exp a -> AST
makeAST = go False
    where
    go eta (Lam body) = SLam (go False body)
    go eta (t :% u) = SApp (go True t) (go False u)
    go eta (Var v) = SVar v
    go eta (Lit l)
        | eta = SPrim (unsafeCoerce (applyValue l))
        | otherwise = SPrim (unsafeCoerce l)

unfree :: Int -> AST -> Maybe AST
unfree n (SLam body) = SLam <$> unfree (n+1) body
unfree n (SVar z) =
    case compare z n of
        LT -> Just (SVar z)
        EQ -> Nothing
        GT -> Just (SVar (z-1))
unfree n (SApp t u) = liftA2 SApp (unfree n t) (unfree n u)
unfree n (SPrim p) = Just (SPrim p)

primK = mkPrim $ \x y -> x
primS = mkPrim $ \x y z -> x z (y z)
primB = mkPrim $ \x y z -> x (y z)
primC = mkPrim $ \x y z -> x z y
primI = mkPrim $ \x -> x
mkPrim = SPrim . unsafeCoerce

unlambda :: AST -> AST
unlambda (SLam t) | Just t' <- unfree 0 t = SApp primK (unlambda t')
unlambda (SLam (SVar 0)) = primI
unlambda (SLam (SApp t (SVar 0))) | Just t' <- unfree 0 t = unlambda t
unlambda (SLam (SLam t)) = unlambda (SLam (unlambda (SLam t)))
unlambda (SLam (SApp t u))
    = case (unfree 0 t, unfree 0 u) of
        (Nothing, Nothing) -> primS `SApp` unlambda t `SApp` unlambda u
        (Just t', Nothing) -> primB `SApp` t' `SApp` u
        (Nothing, Just u') -> primC `SApp` t `SApp` u'
        (Just t', Just u') -> error "Impossible!"
unlambda (SApp t u) = SApp (unlambda t) (unlambda u)
unlambda (SVar v) = SVar v
unlambda (SPrim p) = SPrim p

compile :: AST -> Any
compile (SPrim p) = p
compile (SApp t u) = unsafeCoerce (compile t) (compile u)
compile _ = error "Don't know how to compile that"

embeddedInterp = Interp {
    eval = Just . unsafeCoerce . compile . unlambda . makeAST
}
