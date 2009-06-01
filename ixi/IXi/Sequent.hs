module IXi.Sequent 
    ( Sequent(..)
    , Err
    , hypothesis, conversion, implRule
    , xiRule, hxiRule, hhRule
    )
where

import IXi.Term
import IXi.Conversion

infix 0 :|-
data Sequent = [Term] :|- Term

type Err = Either String

valid = Right
invalid = Left


hypothesis :: Int -> Sequent -> Err ()
hypothesis z (hyps :|- goal)
    | not (0 <= z && z < length hyps)
        = invalid "Index out of range"
    | not (hyps !! z == goal)
        = invalid "Hypothesis does not match goal"
    | otherwise
        = valid ()

conversion :: Conversion -> Sequent -> Err Sequent
conversion c (hyps :|- goal) =
    case convert c goal of
        Nothing -> invalid "Goal conversion failed"
        Just goal' -> valid (hyps :|- goal')

implRule :: Term -> Sequent -> Err (Sequent, Sequent)
implRule p (hyps :|- q :% x) =
    valid (hyps :|- p :% x, hyps :|- Xi :% p :% q)
implRule _ _ = invalid "Goal is not an application"

xiRule :: Name -> Sequent -> Err (Sequent, Sequent)
xiRule name (hyps :|- Xi :% a :% b)
    | nameFree name a || nameFree name b || any (nameFree name) hyps
        = invalid "Name must not be free in environment"
    | otherwise
        = valid (hyps :|- H :% (a :% n), (a :% n):hyps :|- b :% n)
    where n = NameVar name
xiRule _ _ = invalid "Goal is not a Xi-form"

hxiRule :: Name -> Sequent -> Err (Sequent, Sequent)
hxiRule name (hyps :|- H :% (Xi :% a :% b))
    | nameFree name a || nameFree name b || any (nameFree name) hyps
        = invalid "Name must no be free in environment"
    | otherwise
        = valid (hyps :|- H :% (a :% n), (a :% n):hyps :|- H :% (b :% n))
    where n = NameVar name
hxiRule _ _ = invalid "Goal is not an H-Xi-form"

hhRule :: Sequent -> Err ()
hhRule (hyps :|- H :% (H :% x)) = valid ()
hhRule _ = invalid "Goal is not an H-H-form"
