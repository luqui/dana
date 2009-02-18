module SystemUBox.AST where

data AST
    = Var Int
    | Type

    | Pi  AST AST
    | Lam AST AST
    | App AST AST

    | Finite Int
    | Label Int Int
    | Case AST AST [AST]

    | LetRec AST AST AST  -- type, value, in

    | Partial AST  -- add bottom to type
    | Box AST
    | Unbox AST
    deriving Show