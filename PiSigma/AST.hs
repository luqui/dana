module PiSigma.AST where

type Var = String
newtype Label = Label String
    deriving (Eq,Show)

data AST
    = Var Var
    | Type    

    | Pi  Var AST AST
    | Lam Var AST
    | App AST AST
