module IXi.Proof 
    ( Proof
    , hypothesis, conversion
    , implRule, xiRule, hxiRule, hhRule
    , theorem
    , Theorem, thmStatement, prove
    )
where

import IXi.Term
import IXi.Conversion
import qualified IXi.Sequent as S
import Data.Monoid
import Control.Monad.Trans.Error () -- for Monad Either

data Proof
    = Hypothesis Int
    | Conversion Conversion Proof
    | ImplRule Term Proof Proof
    | XiRule Name Proof Proof
    | HXiRule Name Proof Proof
    | HHRule
    | Theorem Theorem

hypothesis = Hypothesis
conversion = Conversion
implRule = ImplRule
xiRule = XiRule
hxiRule = HXiRule
hhRule = HHRule
theorem = Theorem


checkProof :: Proof -> S.Sequent -> S.Err ()
checkProof (Hypothesis z) seq = S.hypothesis z seq

checkProof (Conversion c p') seq = 
    checkProof p' =<< S.conversion c seq

checkProof (ImplRule p pfPx pfXpq) seq = do
    (px, xpq) <- S.implRule p seq
    checkProof pfPx px
    checkProof pfXpq xpq

checkProof (XiRule name hproof xiproof) seq = do
    (h, xi) <- S.xiRule name seq
    checkProof hproof h
    checkProof xiproof xi

checkProof (HXiRule name hproof hxiproof) seq = do
    (h, hxi) <- S.hxiRule name seq
    checkProof hproof h
    checkProof hxiproof hxi

checkProof HHRule seq = S.hhRule seq

checkProof (Theorem (MkTheorem t _)) (hyps S.:|- goal)
    | goal == t = Right ()
    | otherwise = Left "Goal does not match theorem"


data Theorem = MkTheorem Term Proof

instance Show Theorem where
    show (MkTheorem t _) = "|- " ++ show t

thmStatement :: Theorem -> Term
thmStatement (MkTheorem t _) = t


prove :: Term -> Proof -> Either String Theorem
prove stmt proof = 
    case checkProof proof ([] S.:|- stmt) of
        Right () -> Right (MkTheorem stmt proof)
        Left e -> Left e
