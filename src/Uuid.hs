{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
module Uuid(UuidList(..), UuidM, UuidMonad, runUuidM, withUuid, WithUuid, uuid, val) where

import Control.Monad.IO.Class(MonadIO)
import Control.Monad.Trans.Class(MonadTrans,lift)
import qualified Data.HashTable.IO as HT
import qualified Control.Monad.Trans.Reader as ReaderM
import Data.IORef

class UuidList a where
  uuidList :: a -> [Int]

class Monad m => UuidMonad m where
  register :: UuidList a => a -> m Int

newtype UuidM a = UuidM { unwrap :: ReaderM.ReaderT (HT.BasicHashTable [Int] Int, IORef Int) IO a }
  deriving(Functor,Applicative,Monad,MonadIO)

instance UuidMonad UuidM where
  register x = do
    (ht,sizeRef) <- UuidM ReaderM.ask
    size <- UuidM $ lift $ readIORef sizeRef
    UuidM $ lift $ HT.mutateIO ht (uuidList x) (\x -> case x of {
      Just v -> return (x, v);
      Nothing -> modifyIORef sizeRef (+1) >> return (Just size, size);
    })

runUuidM :: UuidM a -> IO a
runUuidM mx = do
  ht <- HT.new
  sizeRef <- newIORef 0
  ReaderM.runReaderT (unwrap mx) (ht,sizeRef)

data WithUuid a = WithUuid { val :: a, uuid :: Int }

withUuid :: (UuidList a, UuidMonad m) => a -> m (WithUuid a)
withUuid x = register x >>= return . WithUuid x

instance Eq (WithUuid a) where { x == y = uuid x == uuid y }
