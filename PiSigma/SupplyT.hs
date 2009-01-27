module PiSigma.SupplyT 
    ( SupplyT, allocate, runSupplyT )
where

import Control.Monad.State

newtype SupplyT s m a = SupplyT { unSupplyT :: StateT [s] m a }
    deriving (Functor,Monad)

allocate :: (Monad m) => SupplyT s m s
allocate = SupplyT $ do
    (s:ss) <- get
    put ss
    return s

runSupplyT :: (Monad m) => [s] -> SupplyT s m a -> m a
runSupplyT ss (SupplyT m) = evalStateT m ss
