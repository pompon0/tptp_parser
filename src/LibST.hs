module LibST where

import Control.Lens(makeLenses,use,to,at,non,Lens',(&),(%~),(%=),(<%=),(^..),(^.),Getting)
import Control.Monad.ST
import Data.STRef
import Data.Monoid(Endo)

(*&) :: STRef s a -> (a -> a) -> ST s ()
(*&) = modifySTRef
infixl 1 *&

(*^.) :: STRef s a -> Getting b a b -> ST s b
(*^.) ref l = do { v <- readSTRef ref; return (v^.l) }
infixl 1 *^.

(*^..) :: STRef s a -> Getting (Endo [b]) a b -> ST s [b]
(*^..) ref l = do { v <- readSTRef ref; return (v^..l) }
infixl 1 *^..


readST :: STRef s a -> ST s a
readST = readSTRef

newST :: a -> ST s (STRef s a)
newST = newSTRef

(*.~) :: STRef s a -> a -> ST s ()
(*.~) = writeSTRef
infixl 1 *.~

pop :: STRef s [a] -> ST s (Maybe a)
pop lref = do
  l <- readST lref
  case l of { [] -> return Nothing; h:t -> lref *.~ t >> return (Just h) }

loopM :: Monad m => m (Maybe a) -> (a -> m ()) -> m ()
loopM mcond mbody = do
  cond <- mcond
  case cond of { Just x -> mbody x >> loopM mcond mbody; Nothing -> return () }

whenM :: Monad m => m Bool -> m () -> m ()
whenM mcond mtrue = do { cond <- mcond; if cond then mtrue else return () }


