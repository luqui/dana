{-# LANGUAGE PatternGuards #-}

module SystemUBox.UnsafeCompile 
    ( module SystemUBox.Any
    , Type(..)
    , unsafeCompile
    )
where

import qualified SystemUBox.AST as AST
import SystemUBox.Any
import qualified Data.MemoCombinators as Memo
import Data.Function (fix)
import Debug.Trace
import Control.Monad (liftM2)
import Data.Maybe (isNothing)


data Type 
    = Type
    | Pi Type (Any -> Type)
    | Finite Int
    | Partial Type


data TypeFree
    = Var Int
    | Lam TypeFree
    | App TypeFree TypeFree

    | Native String Any

instance Show TypeFree where
    show = showTF False False

showTF :: Bool -> Bool -> TypeFree -> String
showTF ap lp (Var z) = show z
showTF ap lp (Lam t) = parens lp ("\\" ++ showTF False False t)
showTF ap lp (App t u) = parens ap (showTF False True t ++ " " ++ showTF True True u)
showTF ap lp (Native s _) = s

parens :: Bool -> String -> String
parens True s = "(" ++ s ++ ")"
parens False s = s

toTypeFree :: AST.AST -> TypeFree
toTypeFree (AST.Var i)  = Var i
toTypeFree (AST.Lam dom body) = Lam (toTypeFree body)
toTypeFree (AST.App f x) = App (toTypeFree f) (toTypeFree x)

toTypeFree (AST.Label z t) = Native ("(" ++ show z ++ ":" ++ show t ++ ")") (makeLabel z t)
toTypeFree (AST.Case z _ cases) = foldl App (toTypeFree z) (map toTypeFree cases)

toTypeFree (AST.LetRec [] body) = toTypeFree body
toTypeFree (AST.LetRec ((_,d):ds) body) = 
    Lam (toTypeFree (AST.LetRec ds body)) 
        `App` (Native "Y" (toAny fix) `App` Lam (toTypeFree d))

-- not worrying about strictness yet
toTypeFree (AST.Box z) = toTypeFree z
toTypeFree (AST.Unbox z) = toTypeFree z

toTypeFree AST.Type     = Native "Type" (toAny Type)
toTypeFree (AST.Pi v f) = (Native "Pi" (toAny Pi) `App` (toTypeFree v)) `App` Lam (toTypeFree f)
toTypeFree (AST.Finite z) = Native ("(Finite " ++ show z ++ ")") (toAny (Finite z))
toTypeFree (AST.Partial t) = Native "Partial" (toAny Partial) `App` toTypeFree t


makeLabel :: Int -> Int -> Any
makeLabel = Memo.memo2 Memo.integral Memo.integral go
    where
    go x y | x < 0 || x >= y = error "Malformed label"
    go 0 1 = toAny id
    go 0 n = toAny $ \x -> const . fromAny (go 0 (n-1))
    go n m = toAny . const $ fromAny (go (n-1) (m-1))

infixl 9 %
(%) :: Any -> Any -> Any
f % x = fromAny f (fromAny x)

combiK = Native "K" . toAny $ \x y -> x
combiS = Native "S" . toAny $ \x y z -> x z (y z)
combiC = Native "C" . toAny $ \x y z -> x z y
combiB = Native "B" . toAny $ \x y z -> x (y z)
combiI = Native "I" . toAny $ \x -> x

unfree :: Int -> TypeFree -> Maybe TypeFree
unfree z (Var x) =
    case compare z x of
        EQ -> Nothing
        LT -> Just (Var (x-1))
        GT -> Just (Var x)
unfree z (Lam f) = fmap Lam (unfree (z+1) f)
unfree z (App f x) = liftM2 App (unfree z f) (unfree z x)
unfree z n@(Native _ _) = Just n

free :: Int -> TypeFree -> Bool
free z = isNothing . unfree z

tr :: TypeFree -> TypeFree
tr (Var i) = Var i
tr (App f x) = tr f `App` tr x
tr (Lam e) | Just e' <- unfree 0 e = combiK `App` tr e'
tr (Lam (Var 0)) = combiI
tr (Lam (Lam e)) | Nothing <- unfree 1 e = tr (Lam (tr (Lam e)))
tr (Lam (App e1 e2)) =
   case (unfree 0 e1, unfree 0 e2) of
       (Nothing, Nothing)  -> (combiS `App` tr (Lam e1)) `App` tr (Lam e2)
       (Nothing, Just e2') -> (combiC `App` tr (Lam e1)) `App` tr e2'
       (Just e1', Nothing) -> (combiB `App` tr e1') `App` tr (Lam e2)
       (Just _, Just _)    -> error "Case should have already been covered"
tr (Native s n) = Native s n

squish :: TypeFree -> Any
squish (App f x) = squish f % squish x
squish (Native s n) = n
squish t = error $ "Not squishable: " ++ show t

compileTypeFree :: TypeFree -> Any
compileTypeFree = squish . traceit . tr
    where
    traceit x = trace (show x) x

unsafeCompile :: AST.AST -> Any
unsafeCompile = compileTypeFree . toTypeFree
