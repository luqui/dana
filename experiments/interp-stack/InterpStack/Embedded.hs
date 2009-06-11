{-# LANGUAGE PatternGuards #-}

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
makeAST (Lam body) = SLam (makeAST body)
makeAST (t :% u) = SApp (makeAST t) (makeAST u)
makeAST (Var v) = SVar v
makeAST (Lit l) = SPrim $
    if canApply l then unsafeCoerce (applyValue l) else unsafeCoerce l

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
unlambda (SLam (SApp t (SVar 0))) | Just t' <- unfree 0 t = unlambda t'
unlambda (SLam (SLam t)) = unlambda (SLam (unlambda (SLam t)))
unlambda (SLam (SApp t u))
    = case (unfree 0 t, unfree 0 u) of
        (Nothing, Nothing) -> primS `SApp` unlambda (SLam t) `SApp` unlambda (SLam u)
        (Just t', Nothing) -> primB `SApp` unlambda t' `SApp` unlambda (SLam u)
        (Nothing, Just u') -> primC `SApp` unlambda (SLam t) `SApp` unlambda u'
        (Just t', Just u') -> error "Impossible!"
unlambda (SApp t u) = SApp (unlambda t) (unlambda u)
unlambda (SVar v) = SVar v
unlambda (SPrim p) = SPrim p

compile :: AST -> Any
compile (SPrim p) = p
compile (SApp t u) = unsafeCoerce (compile t) (compile u)
compile (SLam l) = error "Don't know how to compile lambda"
compile (SVar v) = error "Don't know how to compile free variable"

embeddedInterp = Interp {
    eval = Just . unsafeCoerce . compile . unlambda . makeAST
}
