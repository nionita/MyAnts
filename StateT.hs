{-# LANGUAGE RankNTypes, MultiParamTypeClasses, FlexibleInstances #-}

module StateT (
    CPS,
    return, (>>=),
    get, put, gets, modify,
    lift, liftIO,
    runState, execState, evalState
    ) where

import Control.Monad
-- import Control.Monad.State hiding (lift, gets, modify)

newtype CPS r s m a = CPS { runCPS :: s -> (a -> s -> m r) -> m r }

instance Monad (CPS r s m) where
    return a = CPS $ \s k -> k a s
    c >>= f  = CPS $ \s0 k -> runCPS c s0 $ \a s1 -> runCPS (f a) s1 k

instance MonadState s (CPS r s m) where
    get   = CPS $ \s k -> k s  s
    put s = CPS $ \_ k -> k () s

{--
instance MonadIO m => MonadIO (CPS r s m) where
    {-# INLINE liftIO #-}
    liftIO = lift . liftIO
--}
liftIO :: IO a -> CPS r s IO a
liftIO = lift

runState :: Monad m => CPS (a, s) s m a -> s -> m (a, s)
runState c s = runCPS c s $ \a s0 -> return (a, s0)
{-# INLINE runState #-}

evalState :: Monad m => CPS a s m a -> s -> m a
evalState c s = runCPS c s $ \a _ -> return a
{-# INLINE evalState #-}

execState :: Monad m => CPS s s m a -> s -> m s
execState c s = runCPS c s $ \_ s0 -> return s0
-- execState ms s = liftM snd $ runState ms s
{-# INLINE execState #-}

{-# INLINE lift #-}
lift :: Monad m => m a -> CPS r s m a
lift m = CPS $ \s k -> m >>= \a -> k a s

{-# INLINE gets #-}
gets :: Monad m => (s -> a) -> CPS r s m a
gets f = CPS $ \s k -> case f s of fs -> k fs s
-- gets f = CPS $ \s k -> k (f s) s

{-# INLINE modify #-}
modify :: Monad m => (s -> s) -> CPS r s m ()
modify f = CPS $ \s k -> case f s of fs -> k () fs
-- modify f = CPS $ \s k -> k () (f s)

----- Here: copied from mtl & transformers, as this seems to be missing

-- class (Monad m) => MonadState s m | m -> s where
class (Monad m) => MonadState s m where
    -- | Return the state from the internals of the monad.
    get :: m s
    -- | Replace the state inside the monad.
    put :: s -> m ()
