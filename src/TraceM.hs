module TraceM (TraceM, ctx, fail, log) where

import Prelude hiding(fail,log)

class Monad m => TraceM m where
  ctx :: String -> [String] -> m a -> m a
  fail :: String -> m a
  log :: String -> m ()
