module IXi.Proof 
    ( Proof
    , hypothesis, conversion
    , implRule, xiRule, hxiRule, hhRule
    , theorem
    , Theorem, prove
    )
where

import IXi.Term
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Error

data Context n
    = Context { cxGoal :: Term n
              , cxHyps :: [Term n]
              }

type ProofM n = ErrorT String (StateT [n] (Reader (Context n)))
newtype Proof n = Proof { checkProof :: ProofM n () }

assert :: Bool -> String -> ProofM n ()
assert True err = return ()
assert False err = fail err

allocate :: ProofM n n
allocate = do
    x <- gets head
    modify tail
    return x

hypothesis :: (Eq n) => Int -> Proof n
hypothesis n = Proof $ do
    Context goal hyp <- ask
    assert (n < length hyp) "Hypothesis index out of range"
    assert (hyp !! n == goal) "Hypothesis does not match goal"

conversion :: (Eq n) => Conversion n -> Proof n -> Proof n
conversion conv pf = Proof $ do
    goal <- asks cxGoal
    assert (goal == convFrom conv) $ "Goal does not match source of conversion"
    subgoal [] (convTo conv) pf

subgoal :: [Term n] -> Term n -> Proof n -> ProofM n ()
subgoal hyps goal = local (\s -> s { cxGoal = goal, cxHyps = hyps ++ cxHyps s }) . checkProof

implRule :: Term n -> Proof n -> Proof n -> Proof n
implRule p pfPx pfXpq = Proof $ do
    goal <- asks cxGoal
    case goal of
        q :% x -> do
            subgoal [] (p :% x) pfPx
            subgoal [] (Xi :% p :% q) pfXpq
        _ -> fail "Goal is not in the form a b"

xiRule :: (n -> Proof n) -> (n -> Proof n) -> Proof n
xiRule hproof xiproof = Proof $ do
    goal <- asks cxGoal
    case goal of
        Xi :% a :% b -> do
            name <- allocate
            let nv = NameVar name
            subgoal [] (H :% (a :% nv)) (hproof name)
            subgoal [a :% nv] (b :% nv) (xiproof name)
        _ -> fail "Goal is not in the form Xi a b"

hxiRule :: (n -> Proof n) -> (n -> Proof n) -> Proof n
hxiRule hproof hxiproof = Proof $ do
    goal <- asks cxGoal
    case goal of
        H :% (Xi :% a :% b) -> do
            name <- allocate
            let nv = NameVar name
            subgoal [] (H :% (a :% nv)) (hproof name)
            subgoal [a :% nv] (H :% (b :% nv)) (hxiproof name)
        _ -> fail "Goal is not in the form H (Xi a b)"

hhRule :: Proof n
hhRule = Proof $ do
    goal <- asks cxGoal
    case goal of
        H :% (H :% a) -> return ()
        _ -> fail "Goal is not in the form H (H x)"

theorem :: (Eq n) => Theorem -> Proof n
theorem (Theorem t) = Proof $ do
    goal <- asks cxGoal
    assert (goal == t) "Goal does not match theorem"

newtype Theorem = Theorem (forall n. Term n)

prove :: (forall n. Term n, forall n. Eq n => Proof n) -> Either String Theorem
prove (term,pf) = right (const (Theorem term)) 
                . (`runReader` Context term [])
                . (`evalStateT` [0..])
                . runErrorT
                . checkProof $ pf

right :: (b -> c) -> Either a b -> Either a c
right f (Left x) = Left x
right f (Right x) = Right (f x)
