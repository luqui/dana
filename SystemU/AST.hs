module SystemU.AST where

data AST
    = Var Int
    | Type    

    | Pi  AST AST
    | Lam AST AST
    | App AST AST
