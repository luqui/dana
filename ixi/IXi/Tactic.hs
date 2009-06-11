module IXi.Tactic 
    ( Tactic, Hypothesis
    , hypothesis, conversion, implRule, xiRule, hxiRule, hhRule, xihRule, theorem
    , inspect, (>|<)
    , newName
    , prove
    )
where

import qualified IXi.Proof as P
import qualified IXi.Sequent as Seq
import IXi.Conversion
import IXi.Term
import Control.Applicative
import Control.Monad (ap, MonadPlus(..))

newtype Tactic = Tactic { unTactic :: Seq.Sequent -> Seq.Err P.Proof }
newtype Hypothesis = Hypothesis Int  -- index from the end

topHyp :: Seq.Sequent -> Hypothesis
topHyp seq = Hypothesis (length (Seq.hypotheses seq) - 1)

hypothesis :: Hypothesis -> Tactic
hypothesis (Hypothesis z) = Tactic $ \seq -> do
    let ix = length (Seq.hypotheses seq) - z - 1
    () <- Seq.hypothesis ix seq
    return (P.hypothesis ix)

conversion :: Conversion -> Tactic -> Tactic
conversion conv rest = Tactic $ \seq -> do
    seq' <- Seq.conversion conv seq
    p' <- unTactic rest seq'
    return (P.conversion conv p')

implRule :: Term -> Tactic -> Tactic -> Tactic
implRule p pxTac xpqTac = Tactic $ \seq -> do
    (pxSeq, xpqSeq) <- Seq.implRule p seq
    pxPf <- unTactic pxTac pxSeq
    xpqPf <- unTactic xpqTac xpqSeq
    return (P.implRule p pxPf xpqPf)

xiRule :: Name -> Tactic -> (Hypothesis -> Tactic) -> Tactic
xiRule name hTac implTac = Tactic $ \seq -> do
    (hSeq, implSeq) <- Seq.xiRule name seq
    hPf <- unTactic hTac hSeq
    implPf <- unTactic (implTac (topHyp implSeq)) implSeq
    return (P.xiRule name hPf implPf)

hxiRule :: Name -> Tactic -> (Hypothesis -> Tactic) -> Tactic
hxiRule name hTac implTac = Tactic $ \seq -> do
    (hSeq, implSeq) <- Seq.hxiRule name seq
    hPf <- unTactic hTac hSeq
    implPf <- unTactic (implTac (topHyp implSeq)) implSeq
    return (P.hxiRule name hPf implPf)

hhRule :: Tactic
hhRule = Tactic $ \seq -> do
    () <- Seq.hhRule seq
    return P.hhRule

xihRule :: Hypothesis -> Tactic
xihRule (Hypothesis z) = Tactic $ \seq -> do
    let ix = length (Seq.hypotheses seq) - z - 1
    () <- Seq.xihRule ix seq
    return (P.xihRule ix)

theorem :: P.Theorem -> Tactic
theorem thm = Tactic $ \seq -> do
    if P.thmStatement thm == Seq.goal seq
        then return (P.theorem thm)
        else fail "Theorem does not match goal"

inspect :: (Seq.Sequent -> Tactic) -> Tactic
inspect f = Tactic $ \seq -> unTactic (f seq) seq

newName :: (Name -> Tactic) -> Tactic
newName f = Tactic $ \seq -> unTactic (f (Seq.newName seq)) seq

infixr 1 >|<
(>|<) :: Tactic -> Tactic -> Tactic
t >|< u = Tactic $ liftA2 mplus (unTactic t) (unTactic u)

runTactic :: Tactic -> Seq.Sequent -> Seq.Err P.Proof
runTactic (Tactic t) = t

prove :: Term -> Tactic -> P.Theorem
prove stmt tac =
    case P.prove stmt =<< runTactic tac ([] Seq.:|- stmt) of
        Left e -> error $ "Invalid proof: " ++ e
        Right thm -> thm
