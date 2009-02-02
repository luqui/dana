module SystemUBox.UnsafeCompile 
    ( module SystemUBox.Any
    , Type(..), Fun(..)
    , unsafeCompile
    )
where

import qualified SystemUBox.AST as AST
import SystemUBox.Any


data Type 
    = Type
    | Pi Type (Any -> Type)

newtype Fun = Fun { app :: Any -> Any }


data TypeFree
    = Var Int
    | Lam TypeFree
    | App TypeFree TypeFree

    | Native Any


toTypeFree :: AST.AST -> TypeFree
toTypeFree (AST.Var i)  = Var i
toTypeFree AST.Type     = Native (toAny Type)
toTypeFree (AST.Pi v f) = (Native (toAny Pi) `App` (toTypeFree v)) `App` Lam (toTypeFree f)
toTypeFree (AST.Lam dom body) = Lam (toTypeFree body)
toTypeFree (AST.App f x) = App (toTypeFree f) (toTypeFree x)

infixl 9 %
(%) :: Any -> Any -> Any
f % x = fromAny f (fromAny x)

combiK = Native . toAny $ \x y -> x
combiS = Native . toAny $ \x y z -> x z (y z)
combiC = Native . toAny $ \x y z -> x z y
combiB = Native . toAny $ \x y z -> x (y z)
combiI = Native . toAny $ \x -> x

free :: Int -> TypeFree -> Bool
free z (Var x) = x == z
free z (Lam f) = free (z+1) f
free z (App f x) = free z f || free z x
free z (Native _) = False

tr :: TypeFree -> TypeFree
tr (Var i) = Var i
tr (App f x) = tr f `App` tr x
tr (Lam e) | not (free 0 e) = combiK `App` tr e
tr (Lam (Var 0)) = combiI
tr (Lam (Lam e)) | free 1 e = tr (Lam (tr (Lam e)))
tr (Lam (App e1 e2)) =
    case (free 0 e1, free 0 e2) of
        (True, True)  -> (combiS `App` tr (Lam e1)) `App` tr (Lam e2)
        (True, False) -> (combiC `App` tr (Lam e1)) `App` tr (shiftDown e2)
        (False, True) -> (combiB `App` tr (shiftDown e1)) `App` tr (Lam e2)
        (False, False) -> error "Case should have already been covered"
tr (Native n) = Native n

squish :: TypeFree -> Any
squish (App f x) = squish f % squish x
squish (Native n) = n
squish _ = error "Not squishable"

shiftDown :: TypeFree -> TypeFree
shiftDown (Var x) | x > 0 = Var (x-1)
                  | otherwise = error "Can't shift down 0"
shiftDown (Lam f) = Lam (shiftDown f)
shiftDown (App f x) = App (shiftDown f) (shiftDown x)
shiftDown (Native r) = Native r

compileTypeFree :: TypeFree -> Any
compileTypeFree = squish . tr

unsafeCompile :: AST.AST -> Any
unsafeCompile = compileTypeFree . toTypeFree
