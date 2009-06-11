{-# LANGUAGE RankNTypes #-}

module InterpStack.Exp where

infixl 9 :%
data Exp a
    = Exp a :% Exp a
    | Lam (Exp a)
    | Var Int
    | Lit a
    deriving (Show)

class Value v where
    applyValue :: v -> v -> v

data Interp = Interp {
    eval :: forall v. (Value v) => Exp v -> Maybe v
}
