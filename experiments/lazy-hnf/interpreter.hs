import LazyHNF.Exp
import LazyHNF.LazyHNF
import LazyHNF.HOAS
import Debug.Trace

data IVal
    = IInt !Int
    | IInc
    deriving Show


instance Value IVal where
    applyValue IInc (IInt z) = IInt (z+1)
    applyValue _ _ = error "type error"

id_ = fun (\x -> x)

zero_ = fun (\f -> fun (\x -> x))
succ_ = fun (\m -> fun (\f -> fun (\x -> f % (m % f % x))))
one_ = succ_ % zero_
two_ = succ_ % one_

plus_ = fun (\m -> fun (\n -> fun (\f -> fun (\x -> m % f % (n % f % x)))))
times_ = fun (\m -> fun (\n -> m % (plus_ % n) % zero_))
exp_ = fun (\base -> fun (\exp -> exp % (times_ % base) % one_))

nil_ = fun (\n -> fun (\c -> n))
cons_ = fun (\x -> fun (\xs -> fun (\n -> fun (\c -> c % x % xs))))

fix_ = fun (\f -> fun (\x -> x % x) % fun (\x -> f % (x % x)))

true_ = fun (\t -> fun (\f -> t))
false_ = fun (\t -> fun (\f -> f))

flip_ = fun (\f -> fun (\x -> fun (\y -> f % y % x)))
compose_ = fun (\f -> fun (\g -> fun (\y -> f % (g % y))))

let_ v f = f % v

head_ = fun (\list -> list % lit (error "head_: empty list") % fun (\x -> fun (\xs -> x)))
tail_ = fun (\list -> list % lit (error "tail_: empty list") % fun (\x -> fun (\xs -> xs)))
at_ = fun (\n -> fun (\xs -> head_ % (n % tail_ % xs)))

eVar_ = fun (\v' -> fun (\v -> fun (\l -> fun (\a -> fun (\p -> v % v')))))
eLam_ = fun (\body -> fun (\v -> fun (\l -> fun (\a -> fun (\p -> l % body)))))
eApp_ = fun (\left -> fun (\right -> fun (\v -> fun (\l -> fun (\a -> fun (\p -> a % left % right))))))
eLit_ = fun (\litval -> fun (\v -> fun (\l -> fun (\a -> fun (\p -> p % litval)))))


eInterp_ = fix_ % fun (\interp -> fun (\env -> fun (\ast ->
    ast % fun (\ix -> at_ % ix % env)
        % fun (\body -> fun (\x -> interp % (cons_ % x % env) % body))
        % fun (\left -> fun (\right -> interp % env % left % (interp % env % right)))
        % fun (\lt -> lt))))

--program_ = (exp_ % two_ % two_) % lit IInc % lit (IInt 0)

primify_ = fun (\n -> n % lit IInc % lit (IInt 0))

sum_ = fix_ % fun (\self -> fun (\l -> 
    l % zero_ % fun (\x -> fun (\xs -> plus_ % x % (self % xs)))))

program_ = primify_ % (exp_ % two_ % (exp_ % two_ % two_))


quoteInt :: Int -> Term a
quoteInt z = fun (\f -> fun (\x -> foldr (%) x (replicate z f)))

quote :: Exp a -> Exp a
quote = buildExp . go
    where
    go (t :% u) = eApp_ % go t % go u
    go (Lam body) = eLam_ % go body
    go (Var z) = eVar_ % quoteInt z
    go (Lit a) = eLit_ % lit a

layer :: Exp a -> Exp a
layer x = buildExp (eInterp_ % nil_) :% quote x

run :: Exp IVal -> Val IVal
run = eval
