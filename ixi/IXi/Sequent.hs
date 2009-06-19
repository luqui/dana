module IXi.Sequent 
    ( Sequent(..)
    , goal, hypotheses
    , Err
    , hypothesis, conversion, implRule
    , xiRule, hxiRule, hhRule
    , newName
    )
where

import IXi.Term
import IXi.Conversion

infix 0 :|-
data Sequent = [Term] :|- Term

goal :: Sequent -> Term
goal (h :|- g) = g

hypotheses :: Sequent -> [Term]
hypotheses (h :|- g) = h

type Err = Either String

valid = Right
invalid g x = Left (x ++ "\n|- " ++ show g)


hypothesis :: Int -> Sequent -> Err ()
hypothesis z (hyps :|- goal)
    | not (0 <= z && z < length hyps)
        = invalid goal "Index out of range"
    | not (hyps !! z == goal)
        = invalid goal $ "Hypothesis (" ++ show (hyps !! z) ++ ") does not match goal"
    | otherwise
        = valid ()

conversion :: Conversion -> Sequent -> Err Sequent
conversion c (hyps :|- goal) =
    case convert c goal of
        Nothing -> invalid goal "Goal conversion failed"
        Just goal' -> valid (hyps :|- goal')

implRule :: Term -> Sequent -> Err (Sequent, Sequent)
implRule p (hyps :|- q :% x) =
    valid (hyps :|- p :% x, hyps :|- Xi :% p :% q)
implRule _ (hyps :|- goal) = invalid goal "Goal is not an application"

xiRule :: Name -> Sequent -> Err (Sequent, Sequent)
xiRule name (hyps :|- goal@(Xi :% a :% b))
    | nameFree name a || nameFree name b || any (nameFree name) hyps
        = invalid goal "Name must not be free in environment"
    | otherwise
        = valid (hyps :|- H :% (a :% n), (a :% n):hyps :|- b :% n)
    where n = NameVar name
xiRule _ (hyps :|- goal) = invalid goal "Goal is not a Xi-form"

hxiRule :: Name -> Sequent -> Err (Sequent, Sequent)
hxiRule name (hyps :|- goal@(H :% (Xi :% a :% b)))
    | nameFree name a || nameFree name b || any (nameFree name) hyps
        = invalid goal "Name must not be free in environment"
    | otherwise
        = valid (hyps :|- H :% (a :% n), (a :% n):hyps :|- H :% (b :% n))
    where n = NameVar name
hxiRule _ (hyps :|- goal) = invalid goal "Goal is not an H-Xi-form"

hhRule :: Sequent -> Err ()
hhRule (hyps :|- H :% (H :% x)) = valid ()
hhRule (hyps :|- goal) = invalid goal "Goal is not an H-H-form"

newName :: Sequent -> Name
newName seq = safeName' (goal seq : hypotheses seq)
