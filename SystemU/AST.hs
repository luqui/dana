module SystemU.AST where

data AST
    = Var Int
    | Type

    | Pi  AST AST
    | Lam AST AST
    | App AST AST

    | LetRec [(AST,AST)] AST 

    | Partial AST  -- add bottom to type
    | Box AST
    | Unbox AST
    deriving Show
