{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ViewPatterns #-}
module DiscTree(build,add,match,emptyTree,Tree) where

import Lib
import Pred
import DNF
import qualified Data.Map as Map
import Control.Lens(makeLenses,Iso',ASetter',Traversal',at,non,to,(&),(%~),(.~),(^..),(^.),(^?))

data Tree x = Tree {
  _jumpFun :: Map.Map (FunName,Int) (Tree x),
  _jumpTerm :: Map.Map Term (Tree x),
  _output :: [x]
} deriving(Eq,Show)
makeLenses ''Tree

-------------------------------------------------------------------

mergeVars :: Term -> Term
mergeVars t = t & term'subst %~ (\_ -> wrap (TVar 0))

emptyTree = Tree Map.empty Map.empty []

build :: Eq x => [(Term,x)] -> Tree x
build = foldr add emptyTree

add :: Eq x => (Term,x) -> Tree x -> Tree x
add (t,v) tree = tree & path (mergeVars t) . output %~ (v:)

path :: Eq x => Term -> ASetter' (Tree x) (Tree x)
path t@(unwrap -> TVar _) f tree = (jumpTerm.at t.non emptyTree) f tree
path t@(unwrap -> TFun fn args) f tree = do
  let fna = (fn,length args)
  -- build recursively a path corresponding to t
  tree' <- (jumpFun.at fna.non emptyTree.compose (map path args)) f tree
  -- update the jumpTerm pointer - it is exactly the only pointer that needs updating.
  return $ tree' & jumpTerm.at t .~
    tree'^?jumpFun.at fna.traverse.compose (map (\a -> jumpTerm.at a.traverse) args)

match :: Term -> Traversal' (Tree x) x
match t = matchPath (mergeVars t) . output . traverse

matchPath :: Term -> Traversal' (Tree x) (Tree x)
matchPath t@(unwrap -> TVar _) f tree = (jumpTerm.traverse) f tree
matchPath t@(unwrap -> TFun fn args) f (Tree jf jt out) = pure Tree
  <*> (at (fn,length args).traverse.compose (map matchPath args)) f jf
  <*> (at (wrap $ TVar 0).traverse) f jt
  <*> pure out
