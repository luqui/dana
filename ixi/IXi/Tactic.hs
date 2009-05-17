module IXi.Tactic
    ( Tactic, Hypothesis, runTactic

    , withGoal
    , withHypStatement
    , withFreshName
    
    , hypothesis
    , conversion
    , hypConversion
    , implRule
    , xiRule
    , hxiRule
    , hhRule
    , theorem
    )
where

import Control.Applicative
import qualified IXi.Proof as P
import IXi.Term
import IXi.Conversion

-- keep track of the number, so that we can have stable indices
data Sequent = Sequent {
    seqNumHyps :: Int,
    seqHyps :: [Term],
    seqGoal :: Term
  }

newtype Hypothesis = Hypothesis Int

hypToIndex :: Sequent -> Hypothesis -> Int
hypToIndex seq (Hypothesis i) = (seqNumHyps seq - 1) - i

hypToTerm :: Sequent -> Hypothesis -> Term
hypToTerm seq hyp = seqHyps seq !! hypToIndex seq hyp

newtype TacF f a = TacF { runTacF :: Sequent -> f a }

instance Functor f => Functor (TacF f) where
    fmap f (TacF tac) = TacF (fmap f . tac)

instance Applicative f => Applicative (TacF f) where
    pure = TacF . pure . pure
    TacF f <*> TacF x = TacF (liftA2 (<*>) f x)

instance Alternative f => Alternative (TacF f) where
    empty = TacF (pure empty)
    TacF x <|> TacF y = TacF (liftA2 (<|>) x y)

newtype Tactic f = Tactic { getTacF :: TacF f P.Proof }

runTactic :: Tactic f -> Term -> f P.Proof
runTactic (Tactic tac) goal = runTacF tac seq
    where
    seq = Sequent { seqNumHyps = 0, seqHyps = [], seqGoal = goal }

withGoalF :: (Term -> TacF f a) -> TacF f a
withGoalF f = withSequent (f . seqGoal)

withHyp :: Term -> (Hypothesis -> TacF f a) -> TacF f a
withHyp hypterm f = TacF $ \seq -> 
    let hyp = Hypothesis (seqNumHyps seq) in
    runTacF (f hyp) (seq { seqNumHyps = seqNumHyps seq + 1
                         , seqHyps = hypterm : seqHyps seq })

subgoal :: Term -> TacF f a -> TacF f a
subgoal goal' tac = TacF (\seq -> runTacF tac (seq { seqGoal = goal' }))

withSequent :: (Sequent -> TacF f a) -> TacF f a
withSequent f = TacF $ \seq -> runTacF (f seq) seq


withGoal :: (Term -> Tactic f) -> Tactic f
withGoal f = Tactic . withGoalF $ getTacF . f

withHypStatement :: Hypothesis -> (Term -> Tactic f) -> Tactic f
withHypStatement hyp f = Tactic . withSequent $ \seq -> getTacF (f (hypToTerm seq hyp))

withFreshName :: [Term] -> (Name -> Tactic f) -> Tactic f
withFreshName ts f = Tactic . withSequent $ \seq -> 
    getTacF (f (safeName' (ts ++ seqGoal seq:seqHyps seq)))

hypothesis :: (Alternative f) => Hypothesis -> Tactic f
hypothesis hyp = Tactic . withSequent $ \seq -> 
    if hypToTerm seq hyp == seqGoal seq
        then pure (P.hypothesis (hypToIndex seq hyp))
        else empty

conversion :: (Alternative f) => Conversion -> Tactic f -> Tactic f
conversion conv (Tactic rest) = Tactic . withGoalF $ \goal ->
    case convert conv goal of
        Just goal' -> subgoal goal' rest
        Nothing -> empty

hypConversion :: (Alternative f) => Hypothesis -> Conversion -> Tactic f -> Tactic f
hypConversion hyp conv (Tactic rest) = Tactic . withSequent $ \seq ->
    case convert conv (hypToTerm seq hyp) of
        Just hyp' -> TacF $ \seq -> 
            let hypIx = hypToIndex seq hyp
                seq' = seq { seqHyps = replace hypIx hyp' (seqHyps seq) } in
            runTacF rest seq'
        Nothing -> empty
    where
    replace n x (a:as) = replace (n-1) x as
    replace _ _ [] = error "Invalid replacement"

implRule :: (Alternative f) => Term -> Tactic f -> Tactic f -> Tactic f
implRule p (Tactic pfPx) (Tactic pfXpq) = Tactic . withGoalF $ \goal ->
    case goal of
        q :% x -> P.implRule p <$> subgoal (p :% x) pfPx
                               <*> subgoal (Xi :% p :% q) pfXpq
        _ -> empty

xiRule :: (Alternative f) => Name -> Tactic f -> (Hypothesis -> Tactic f) -> Tactic f
xiRule n (Tactic hproof) xiproof = Tactic . withSequent $ \seq ->
    case seqGoal seq of
        Xi :% a :% b | all (flip nameFree n) (a:b:seqHyps seq)
            -> P.xiRule n <$> subgoal (H :% a) hproof
                          <*> withHyp (a :% NameVar n) 
                              (\hyp -> subgoal (b :% NameVar n) (getTacF (xiproof hyp)))
        _ -> empty

hxiRule :: (Alternative f) => Name -> Tactic f -> (Hypothesis -> Tactic f) -> Tactic f
hxiRule n (Tactic hproof) hxiproof = Tactic . withSequent $ \seq ->
    case seqGoal seq of
        Xi :% a :% b | all (flip nameFree n) (a:b:seqHyps seq)
            -> P.xiRule n <$> subgoal (H :% a) hproof
                          <*> withHyp (a :% NameVar n) 
                              (\hyp -> subgoal (H :% (b :% NameVar n)) (getTacF (hxiproof hyp)))
        _ -> empty

hhRule :: (Alternative f) => Tactic f
hhRule = Tactic . withGoalF $ \goal ->
    case goal of
        H :% (H :% x) -> pure P.hhRule
        _ -> empty

theorem :: (Alternative f) => P.Theorem -> Tactic f
theorem thm = Tactic . withGoalF $ \goal ->
    if goal == P.thmStatement thm
        then pure (P.theorem thm)
        else empty
