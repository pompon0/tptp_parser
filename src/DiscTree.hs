{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ViewPatterns #-}
module DiscTree(build,match,Tree) where

import Lib
import Pred
import DNF
import qualified Data.Map as Map
import Control.Lens(makeLenses,Iso',Traversal',at,(&),(%~),(.~))
import Control.Lens.Iso(non)

data Tree x = Tree {
  _exact :: (Map.Map (FunName,Int) (Tree x)),
  _indexVar :: Maybe (Tree x),
  _inputVar :: [Tree x],
  _output :: [x]
} deriving(Eq,Show)
makeLenses ''Tree

-------------------------------------------------------------------

emptyTree = Tree Map.empty Nothing [] []

build :: Eq x => [(Term,x)] -> Tree x
build = setInputVar . foldr add emptyTree

add :: Eq x => (Term,x) -> Tree x -> Tree x
add (t,v) tree = tree & path t . output %~ (v:)

compose :: [a -> a] -> (a -> a)
compose = foldl (.) id 

path :: Eq x => Term -> Traversal' (Tree x) (Tree x)
path (unwrap -> TVar _) = indexVar.non emptyTree
path (unwrap -> TFun fn args) = exact.at (fn,length args).non emptyTree.compose (map path args)

setInputVar :: Tree x -> Tree x
setInputVar t = let
  t' = t & exact.traverse %~ setInputVar & indexVar.traverse %~ setInputVar
  in t' & inputVar .~ (t'^..indexVar.traverse) ++ [x |
    ((_,a),et) <- (Map.toList $ t'^.exact),
    x <- et^..(compose $ replicate a $ inputVar.traverse)]

match :: Term -> Traversal' (Tree x) x
match t = matchPath t . output . traverse

matchPath :: Term -> Traversal' (Tree x) (Tree x)
matchPath (unwrap -> TVar _) f t = (inputVar . traverse) f t
matchPath (unwrap -> TFun fn args) f (Tree e idx inp out) = pure Tree
  <*> (at (fn,length args).traverse.compose (map matchPath args)) f e
  <*> traverse f idx
  <*> pure inp
  <*> pure out
