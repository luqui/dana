{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module IXi.Undo
    ( UndoT, save, undo, get, put, modify, evalUndoT )
where

import qualified Control.Monad.State as S
import Control.Monad
import Control.Monad.Trans

newtype UndoT s m a = UndoT { unUndoT :: S.StateT [s] m a }
    deriving (Functor, Monad, MonadTrans, MonadIO)

save :: (Monad m) => UndoT s m ()
save = UndoT $ S.modify (\(x:xs) -> x:x:xs)

undo :: (Monad m) => UndoT s m ()
undo = UndoT $ S.modify (\l -> case l of { [x] -> [x] ; (x:xs) -> xs })

get :: (Monad m) => UndoT s m s
get = UndoT $ liftM head S.get

put :: (Monad m) => s -> UndoT s m ()
put x' = UndoT $ S.modify (\(x:xs) -> x':xs)

modify :: (Monad m) => (s -> s) -> UndoT s m ()
modify f = UndoT $ S.modify (\(x:xs) -> f x:xs)

evalUndoT :: (Monad m) => UndoT s m a -> s -> m a
evalUndoT (UndoT m) s = S.evalStateT m [s]
