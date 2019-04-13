{-# LANGUAGE TemplateHaskell #-}
module LazyParamTree where

import Lib
import Pred
import DNF
import Control.Monad(join)
import Control.Lens(Traversal',Lens',Fold,makeLenses, (&), (%~), (.~), over, view, use, (.=), (%=),(^.),(^..))
import Debug.Trace

negAtom :: Atom -> Atom
negAtom a = a & atom'sign %~ not

--TODO: change it to (Node String [(Atom,Node)] | Leaf)
data Node = Node { _node'desc :: String, _node'sub :: [(Atom,Node)] } | Leaf
makeLenses ''Node

atomNode'deepAtom :: Traversal' (Atom,Node) Atom
atomNode'deepAtom f (a,n) = pure (,) <*> f a <*> node'deepAtom f n

node'deepAtom :: Traversal' Node Atom
node'deepAtom f (Node d s) = pure (Node d) <*> (traverse.atomNode'deepAtom) f s
node'deepAtom f Leaf = pure Leaf

indent s = "  " ++ s

showNode :: Node -> [String]
showNode (Node d s) = (d:) $ join $ map (\(a,n) -> show a : map indent (showNode n)) s
showNode Leaf = []

instance Show Node where { show n = unlines (showNode n) }

node'proof :: Fold Node OrClause
node'proof f (Node d s) = f (OrClause $ map fst s) *> (traverse.node'proof) f (map snd s) *> pure (Node d s)
node'proof f Leaf = pure Leaf

---------------------------------------

expand :: [(Atom,Node)] -> Node
expand = Node "expand"

--TODO: add eq axiom check
refl :: Term -> Node
refl s = Node "refl" [(Atom True $ wrap $ PEq s s, Leaf)]

trans :: (Atom,Node) -> (Atom,Node) -> (Atom,Node)
trans (axy,nxy) (ayz,nyz) = case (axy,ayz) of
  (Atom False p, Atom False p') -> case (unwrap p, unwrap p') of
    (PEq x y, PEq y' z) | y==y' -> let axz = Atom False (wrap $ PEq x z) in (axz, Node "trans" [(axy,nxy),(ayz,nyz),(negAtom axz,Leaf)])
    _ -> error $ "trans(" <> show axy <> ", " <> show ayz <> ")"
  _ -> error $ "trans(" <> show axy <> ", " <> show ayz <> ")"

cong :: FunName -> [(Atom,Node)] -> (Atom,Node)
cong f anxy = let
  (lx,ly) = unzip $ map (\(Atom False p, _) -> case unwrap p of { PEq x y -> (x,y); _ -> error "cong"}) anxy
  afxfy = Atom False $ wrap $ PEq (wrap $ TFun f lx) (wrap $ TFun f ly)
  in (afxfy, Node "conj" ((negAtom afxfy,Leaf):anxy))

symm :: (Atom,Node) -> (Atom,Node)
symm (axy@(Atom s p),nxy) = let
  (x,y) = case unwrap p of { PEq x y -> (x,y); _ -> error "symm" }
  ayx = Atom s $ wrap $ PEq y x
  in (ayx, Node "symm" [(axy,nxy),(negAtom ayx,Leaf)])


predWeak :: Node 
predWeak = Leaf

atomCong :: Atom -> (Atom,Node) -> (Atom,Node) -> Node
atomCong aLx (aLy,nLy) (axy,nxy) = -- traceShow ("atomCong",aLx,aLy,nLy,axy,nxy) $
  if (aLx^.atom'sign) /= (aLy^.atom'sign) then error "aLx.sign /= aLy.sign" else
  case filter (\(tx,ty) -> tx/=ty) $ zip (aLx^.atom'args) (aLy^.atom'args) of {
    [(tx,ty)] -> Node "" [(negAtom aLx, Leaf),(aLy,nLy),termCong (tx,ty) (axy,nxy)];
    _ -> error "length diff/=1";
  }

termCong :: (Term,Term) -> (Atom,Node) -> (Atom,Node)
termCong (tx,ty) (axy,nxy) = --traceShow ("termCong",tx,ty,axy,nxy) $
  if axy == (Atom False $ wrap $ PEq tx ty) then (axy,nxy) else
  case (unwrap tx, unwrap ty) of {
    (TFun fx ax, TFun fy ay) | fx==fy -> case filter (\(tx,ty) -> tx/=ty) $ zip ax ay of {
      [txy'] -> (Atom False $ wrap $ PEq tx ty, Node "termCong" [(Atom True $ wrap $ PEq tx ty, Leaf), termCong txy' (axy,nxy)]);
      _ -> error "length diff/=1";
    };
    _ -> error $ "termCong " <> show tx <> " ~ " <> show ty <> " :: " <> show axy;
  }

