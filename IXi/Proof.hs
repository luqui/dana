module IXi.Proof 
    ( Proof
    , hypothesis, conversion, hypConversion
    , implRule, xiRule, hxiRule, hhRule
    , theorem
    , Theorem, thmStatement, prove
    )
where

import IXi.Term
import Control.Monad.Trans
import qualified Control.Monad.Trans.Reader as Reader
import qualified Control.Monad.Trans.State as State
import qualified Control.Monad.Trans.Error as Error

data Context
    = Context { cxGoal :: Term
              , cxHyps :: [Term]
              }

type ProofM = Reader.ReaderT Context (Error.ErrorT String (State.State [Name]))
newtype Proof = Proof { checkProof :: ProofM () }

gets = lift . lift . State.gets
modify = lift . lift . State.modify
asks = Reader.asks
ask = Reader.ask
local = Reader.local

assert :: Bool -> String -> ProofM ()
assert True err = return ()
assert False err = fail err

allocate :: ProofM Name
allocate = do
    x <- gets head
    modify tail
    return x

hypothesis :: Int -> Proof
hypothesis n = Proof $ do
    Context goal hyp <- ask
    assert (n < length hyp) "Hypothesis index out of range"
    assert (hyp !! n == goal) "Hypothesis does not match goal"

conversion :: Conversion -> Proof -> Proof
conversion conv pf = Proof $ do
    goal <- asks cxGoal
    case convert conv goal of
        Just goal' -> subgoal [] goal' pf
        Nothing -> fail $ "Conversion failed on goal " ++ showTerm goal

hypConversion :: Int -> Conversion -> Proof -> Proof
hypConversion n conv pf = Proof $ do
    hyps <- asks cxHyps
    assert (n < length hyps) $ "Hypothesis index out of range"
    case convert conv (hyps !! n) of
        Just hyp' -> local (\s -> s { cxHyps = take n hyps ++ [hyp'] ++ drop (n+1) hyps }) (checkProof pf)
        Nothing -> fail $ "Conversion failed on hypothesis " ++ showTerm (hyps !! n)

subgoal :: [Term] -> Term -> Proof -> ProofM ()
subgoal hyps goal = local (\s -> s { cxGoal = goal, cxHyps = hyps ++ cxHyps s }) . checkProof

implRule :: Term -> Proof -> Proof -> Proof
implRule p pfPx pfXpq = Proof $ do
    goal <- asks cxGoal
    case goal of
        q :% x -> do
            subgoal [] (p :% x) pfPx
            subgoal [] (Xi :% p :% q) pfXpq
        _ -> fail "Goal is not in the form a b"

xiRule :: (Name -> Proof) -> (Name -> Proof) -> Proof
xiRule hproof xiproof = Proof $ do
    goal <- asks cxGoal
    case goal of
        Xi :% a :% b -> do
            name <- allocate
            let nv = NameVar name
            subgoal [] (H :% (a :% nv)) (hproof name)
            subgoal [a :% nv] (b :% nv) (xiproof name)
        _ -> fail "Goal is not in the form Xi a b"

hxiRule :: (Name -> Proof) -> (Name -> Proof) -> Proof
hxiRule hproof hxiproof = Proof $ do
    goal <- asks cxGoal
    case goal of
        H :% (Xi :% a :% b) -> do
            name <- allocate
            let nv = NameVar name
            subgoal [] (H :% (a :% nv)) (hproof name)
            subgoal [a :% nv] (H :% (b :% nv)) (hxiproof name)
        _ -> fail "Goal is not in the form H (Xi a b)"

hhRule :: Proof
hhRule = Proof $ do
    goal <- asks cxGoal
    case goal of
        H :% (H :% a) -> return ()
        _ -> fail "Goal is not in the form H (H x)"

theorem :: Theorem -> Proof
theorem (Theorem t) = Proof $ do
    goal <- asks cxGoal
    assert (goal == t) $ "Goal does not match theorem: "
                      ++ "\nGoal:    " ++ showTerm goal
                      ++ "\nTheorem: " ++ showTerm t

newtype Theorem = Theorem Term

instance Show Theorem where
    show (Theorem t) = "|- " ++ show t

thmStatement :: Theorem -> Term
thmStatement (Theorem t) = t

prove :: Term -> Proof -> Either String Theorem
prove term pf = right (const (Theorem term)) 
              . (`State.evalState` [safeName term..])
              . Error.runErrorT
              . (`Reader.runReaderT` Context term [])
              . checkProof $ pf

right :: (b -> c) -> Either a b -> Either a c
right f (Left x) = Left x
right f (Right x) = Right (f x)
