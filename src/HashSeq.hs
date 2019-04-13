module HashSeq (HashSeq,hashSeq,unit,WithHash,hash,val,withHash) where

import Data.Word(Word64)

type Hash = (Word64,Word64)
base :: Word64
base = 126783261

class HashSeq a where { hashSeq :: a -> [Hash] }

unit :: Word64 -> Hash
unit x = (x,base)

data WithHash a = WithHash { hash :: {-# UNPACK #-} !Hash, val :: !a }

withHash :: HashSeq a => a -> WithHash a
withHash x = WithHash (foldl (\(v1,p1) (v2,p2) -> (v1+p1*v2,p1*p2)) (0,1) (hashSeq x)) x

instance Eq (WithHash a) where
  x == y = fst (hash x) == fst (hash y)

instance Ord (WithHash a) where
  compare x y = compare (fst (hash x)) (fst (hash y))
