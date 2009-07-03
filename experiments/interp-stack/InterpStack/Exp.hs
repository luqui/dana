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
    canApply :: v -> Bool

instance Value () where
    applyValue = undefined
    canApply _ = False

data Interp = Interp {
    eval :: forall v. (Value v) => Exp v -> Maybe v
}
