module IXi.Proof 
    ( Proof
    , hypothesis, conversion, hypConversion
    , implRule, xiRule, hxiRule, hhRule
    , theorem
    , Theorem, thmStatement, prove
    )
where

import IXi.Term
import IXi.Conversion
import Data.Monoid

data Proof
    = Hypothesis Int
    | Conversion Conversion Proof
    | HypConversion Int Conversion Proof
    | ImplRule Term Proof Proof
    | XiRule Name Proof Proof
    | HXiRule Name Proof Proof
    | HHRule
    | Theorem Theorem

hypothesis = Hypothesis
conversion = Conversion
hypConversion = HypConversion
implRule = ImplRule
xiRule = XiRule
hxiRule = HXiRule
hhRule = HHRule
theorem = Theorem

infix 1 :|-
data Sequent = [Term] :|- Term

newtype Error = Error (Maybe String)

instance Monoid Error where
    mempty = valid
    mappend (Error Nothing) u = u
    mappend (Error (Just e)) _ = Error (Just e)

valid = Error Nothing
invalid = Error . Just

-- TODO idea:  Use Tactic Identity to check proofs.
checkProof :: Proof -> Sequent -> Error
checkProof (Hypothesis z) (hyps :|- goal)
    | 0 <= z && z < length hyps && hyps !! z == goal = valid
    | otherwise = invalid "Hypothesis does not match goal"

checkProof (Conversion c p') (hyps :|- goal) = 
    case convert c goal of
        Nothing -> invalid "Goal conversion failed"
        Just goal' -> checkProof p' (hyps :|- goal')

checkProof (HypConversion z c p') (hyps :|- goal)
    | 0 <= z && z < length hyps =
        case convert c (hyps !! z) of
            Nothing -> invalid "Hypothesis conversion failed"
            Just hyp' -> checkProof p' ((take z hyps ++ [hyp'] ++ drop (z+1) hyps) :|- goal)
    | otherwise = invalid "Hypothesis out of range"

checkProof (ImplRule p pfPx pfXpq) (hyps :|- q :% x) =
    checkProof pfPx (hyps :|- p :% x) `mappend` 
    checkProof pfXpq (hyps :|- Xi :% p :% q)

checkProof (XiRule name hproof xiproof) (hyps :|- Xi :% a :% b)
    | nameFree a name && nameFree b name && all (`nameFree` name) hyps
        = checkProof hproof (hyps :|- H :% (a :% n)) `mappend`
          checkProof xiproof ((a :% n):hyps :|- b :% n)
    | otherwise = invalid "Name not free in environment"
    where
    n = NameVar name

checkProof (HXiRule name hproof hxiproof) (hyps :|- H :% (Xi :% a :% b))
    | nameFree a name && nameFree b name && all (`nameFree` name) hyps
        = checkProof hproof (hyps :|- H :% (a :% n)) `mappend`
          checkProof hxiproof ((a :% n):hyps :|- H :% (b :% n))
    | otherwise = invalid "Name not free in environment"
    where
    n = NameVar name

checkProof HHRule (hyps :|- H :% (H :% x)) = valid

checkProof (Theorem (MkTheorem t _)) (hyps :|- goal)
    | goal == t = valid
    | otherwise = invalid "Goal does not match theorem"

checkProof _ _ = invalid "Tactic does not match sequent"


data Theorem = MkTheorem Term Proof

instance Show Theorem where
    show (MkTheorem t _) = "|- " ++ show t

thmStatement :: Theorem -> Term
thmStatement (MkTheorem t _) = t


prove :: Term -> Proof -> Either String Theorem
prove stmt proof = 
    case checkProof proof ([] :|- stmt) of
        Error Nothing  -> Right (MkTheorem stmt proof)
        Error (Just e) -> Left e
