module IXi.Sequent where

import qualified Data.Set as Set
import IXi.Term
import Control.Monad.Error ()

infix 1 :|-

data Sequent = [Term] :|- Term

data Proof = Proof Term [Sequent]

type Tactic = Sequent -> Either String [Sequent]


assumption :: Tactic
assumption (cx :|- goal) | goal `elem` cx = return []
                         | otherwise = fail "No such assumption"

modusPonens :: Term -> Tactic
modusPonens x (cx :|- y :% z) = return [ cx :|- x :% z, cx :|- Xi :% x :% y ]
modusPonens x seq = fail "Not an application"

abstract :: Var -> Tactic
abstract a (cx :|- Xi :% x :% y) 
    | not (a `Set.member` (Set.unions (map freeVars (x:y:cx)))) 
        = return [ cx :|- H :% (x :% Var a), ((x :% Var a) : cx) :|- y :% Var a ]
    | otherwise = fail "Variable not free in hypotheses"
abstract _ _ = fail "Must abstract over universal goal"

univWF :: Var -> Tactic
univWF a (cx :|- H :% (Xi :% x :% y))
    | not (a `Set.member` (Set.unions (map freeVars (x:y:cx))))
        = return [ cx :|- H :% (x :% Var a), ((x :% Var a) : cx) :|- H :% (y :% Var a) ]
    | otherwise = fail "Variable not free in hypotheses"
univWF _ _ = fail "Cannot univWF over a non-H.Xi goal"

wfwf :: Tactic
wfwf (cx :|- H :% (H :% x)) = return []
wfwf _ = fail "wfwf must operate on the goal H(HX)"

subSequent :: Sequent -> Sequent -> Bool
subSequent (hyps :|- g) (hyps' :|- g') = g == g' && (Set.fromList hyps' `Set.isSubsetOf` Set.fromList hyps)
