module IXi.SingleShell where

-- non-branching proof shell

import Control.Applicative
import Control.Monad (ap)
import IXi.Tactic
import IXi.Term

data ProofState = ProofState {
    goal :: Term,
    hyps :: [(Hypothesis, Term)]
}

data Suspension a = Suspension ProofState (Tactic Shell -> a)

instance Functor Suspension where
    fmap f (Suspension ps c) = Suspension ps (f . c)

data Shell a
    = Return a
    | More (Suspension (Shell a))
    | Invalid

instance Functor Shell where
    fmap f (Return x) = Return (f x)
    fmap f (More c) = More ((fmap.fmap) f c)
    fmap f Invalid = Invalid

instance Applicative Shell where
    pure = return
    (<*>) = ap

instance Alternative Shell where
    empty = Invalid
    Return x <|> _ = Return x
    More c <|> x = More (fmap (<|> x) c)
    Invalid <|> x = x
    
instance Monad Shell where
    return = Return
    Return x >>= f = f x
    More c >>= f = More (fmap (>>= f) c)
    Invalid >>= f = Invalid

suspend :: Tactic Shell
suspend = withGoal (\goal -> mlift (More (Suspension (ProofState goal []) pure)))

addHyp :: Hypothesis -> Tactic Shell -> Tactic Shell
addHyp hyp tac = withHypStatement hyp (\hypstmt -> transform (\x -> 
    case x of
        Return a -> Return a
        More (Suspension ps c) -> More (Suspension (ps { hyps = (hyp,hypstmt):hyps ps }) c)
        Invalid -> Invalid
    ) tac)

showState :: ProofState -> String
showState ps =
    (showHyp =<< hyps ps) ++ "----\n" ++ show (goal ps) ++ "\n"
    where
    showHyp (hyp, term) = show term ++ "\n"
