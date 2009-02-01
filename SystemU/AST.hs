module SystemU.AST where

data AST
    = Var Int
    | Type    

    | Pi  AST AST
    | Lam AST AST
    | App AST AST

    | LetRec [AST] AST 
        -- type, value: adds one de bruijn index per def
    deriving Show
