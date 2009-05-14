{-# OPTIONS_GHC -Wall #-}

import qualified Control.Monad.Trans.State as S
import Control.Applicative

data Opcode
    = OpClosure Int Code
    | OpExec

type Code = [Opcode]

data Interp = Interp {
    iCode   :: Code,
    iStack  :: [Value]
}

data Value
        -- envt, code
    = VClosure [Value] Code

type Eval = S.State Interp


popN :: Int -> Eval [Value]
popN n = do
    i <- S.get
    let (pre,post) = splitAt n (iStack i)
    S.put (i { iStack = post })
    return pre

pop :: Eval Value
pop = (\[x] -> x) <$> popN 1


pushN :: [Value] -> Eval ()
pushN vs = S.modify (\i -> i { iStack = vs ++ iStack i })

push :: Value -> Eval ()
push = pushN . (:[])


goto :: Code -> Eval ()
goto code = S.modify (\i -> i { iCode = code })


advanceIP :: Eval Opcode
advanceIP = do
    i <- S.get
    S.put (i { iCode = tail (iCode i) })
    return (head (iCode i))

stepInterp :: Eval ()
stepInterp = go =<< advanceIP
    where
    go (OpClosure size code) = do
        envt <- popN size
        push (VClosure envt code)
    go OpExec = do
        top <- pop
        case top of
            VClosure envt code -> do    
                pushN envt
                goto code


