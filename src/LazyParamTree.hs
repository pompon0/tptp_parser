{-# LANGUAGE TemplateHaskell #-}
module LazyParamTree where

import Pred
import DNF
import Control.Monad(join)
import Control.Lens(Traversal',Lens',Fold,makeLenses, (&), (%~), (.~), over, view, use, (.=), (^.), (%=), (^..))

negAtom :: Atom -> Atom
negAtom a = a & atom'sign %~ not

--TODO: change it to (Node String [(Atom,Node)] | Leaf)
data Node = Node { _node'desc :: String, _node'atom :: Atom,  _node'sub :: Maybe [Node] }
makeLenses ''Node

node'deepAtom :: Traversal' Node Atom
node'deepAtom f (Node d a s) = pure (Node d) <*> f a <*> (traverse.traverse.node'deepAtom) f s

indent s = "  " ++ s

showNode :: Node -> [String]
showNode (Node d a s) = (show a <> "  " <> d) : map indent (join $ map showNode (s^..traverse.traverse))

instance Show Node where { show n = unlines (showNode n) }

nodes'orClause :: Fold [Node] OrClause
nodes'orClause f nodes = f (OrClause $ nodes^..traverse.node'atom) *> pure nodes

node'proof :: Fold Node OrClause
node'proof f (Node d a s) = (traverse.nodes'orClause) f s *> pure (Node d a) <*> (traverse.traverse.node'proof) f s

---------------------------------------

expand :: Atom -> [Node] -> Node
expand a s = Node "expand" a (Just s)

--TODO: add eq axiom check
refl :: Term -> Node
refl s = Node "refl" (Atom False $ PEq s s) (Just [Node "" (Atom True $ PEq s s) Nothing])

--TODO: add eq axiom check
predStrong :: Atom -> Atom -> [Node] -> Node
predStrong aPr aPs sr = Node "predStrong" aPs $ Just (
  Node "" (negAtom aPr) Nothing:
  Node "" (negAtom aPs) Nothing:sr)

paraStrong1 :: (Atom,Atom) -> (Term,Term,Term) -> Node -> Node -> Node
paraStrong1 (aLp,aLw) (p,r,w) nLw nrw = let
  npw = Node "paraStrong1:trans" (Atom False $ PEq p w) $ Just [
    Node "" (Atom False $ PEq p r) Nothing, nrw, Node "" (Atom True $ PEq p w) Nothing]
  in (atomCong (Atom True $ PEq p r) (aLp,aLw) nLw npw)

paraStrong2 :: (Atom,Atom) -> (Term,Term) -> (Term,Term) -> Node -> Node -> [Node] -> Node
paraStrong2 (aLfv,aLw) (fs,fv) (r,w) nLw nrw nsv = let
  nfsfv = Node "" (Atom False $ PEq fs fv) $ Just (
    Node "" (Atom True $ PEq fs fv) Nothing:nsv)
  nfvr = Node "paraStrong2:trans" (Atom False $ PEq fv r) $ Just [
    nfsfv,
    Node "" (Atom False $ PEq fs r) Nothing,
    Node "" (Atom True $ PEq fv r) Nothing]
  nfvw = Node "paraStrong2:trans" (Atom False $ PEq fv w) $ Just [
    nfvr, nrw, Node "" (Atom True $ PEq fv w) Nothing]
  in atomCong (Atom True $ PEq fs r) (aLfv,aLw) nLw nfvw

paraStrong3 :: (Atom,Atom) -> (Term,Term) -> Term -> Node -> [Node] -> Node
paraStrong3 (aLfs,aLw) (fs,fv) w nLw nsv = let
  nfsfv = Node "" (Atom False $ PEq fs fv) $ Just (
    Node "" (Atom True $ PEq fs fv) Nothing:nsv)
  nfsw = Node "paraStrong3:trans" (Atom  False $ PEq fs w) $ Just [
    nfsfv,
    Node "" (Atom False $ PEq fv w) Nothing,
    Node "" (Atom True $ PEq fs w) Nothing]
  in atomCong aLfs (aLfs,aLw) nLw nfsw

predWeak :: Atom -> Node
predWeak aPs = Node "predWeak" aPs Nothing

paraWeak :: Atom -> (Atom,Atom) -> (Term,Term) -> Node -> Node
paraWeak root (aLw,aLp) (p,w) nLw = let
  npw = Node "" (Atom False $ PEq p w) Nothing
  in atomCong root (aLp,aLw) nLw npw

atomCong :: Atom -> (Atom,Atom) -> Node -> Node -> Node
atomCong root (ax,ay) nay nxy =
  if (ax^.atom'sign) /= (ay^.atom'sign) then error "ax.sign /= ay.sign" else
  case filter (\(tx,ty) -> tx/=ty) $ zip (ax^.atom'args) (ay^.atom'args) of {
    [txy] -> Node "" root $ Just [
      Node "atomCong" (negAtom ax) Nothing,
      nay,
      termCong txy nxy];
    _ -> error "length diff/=1";
  }

termCong :: (Term,Term) -> Node -> Node
termCong (tx,ty) nxy =
  if nxy^.node'atom == (Atom False $ PEq tx ty) then nxy else
  case (tx,ty) of {
    (TFun fx ax, TFun fy ay) | fx==fy -> case filter (\(tx,ty) -> tx/=ty) $ zip ax ay of {
      [txy'] -> Node "termCong" (Atom False $ PEq tx ty) $ Just [Node "" (Atom True $ PEq tx ty) Nothing, termCong txy' nxy];
      _ -> error "length diff/=1";
    };
    _ -> error "termCong";
  }

