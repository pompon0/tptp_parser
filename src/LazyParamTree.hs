{-# LANGUAGE TemplateHaskell #-}
module LazyParamTree where

import Lib
import Pred
import DNF
import Control.Monad(join)
import Control.Lens(Traversal',Lens',Fold,makeLenses, (&), (%~), (.~), over, view, use, (.=), (%=))

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
refl s = Node "refl" [(Atom True $ PEq s s, Leaf)]

trans :: (Atom,Node) -> (Atom,Node) -> (Atom,Node)
trans (axy,nxy) (ayz,nyz) = case (axy,ayz) of
  (Atom False (PEq x y), Atom False (PEq _ z)) ->
    let axz = Atom False (PEq x z) in (axz, Node "trans" [(axy,nxy),(ayz,nyz),(negAtom axz,Leaf)])
  _ -> error $ "trans(" <> show axy <> ", " <> show ayz <> ")"

cong :: FunName -> [(Atom,Node)] -> (Atom,Node)
cong f anxy = let
  (lx,ly) = unzip $ map (\(Atom False (PEq x y), _) -> (x,y)) anxy
  afxfy = Atom False $ PEq (TFun f lx) (TFun f ly)
  in (afxfy, Node "conj" ((negAtom afxfy,Leaf):anxy))

symm :: (Atom,Node) -> (Atom,Node)
symm (axy,nxy) = let
  (Atom False (PEq x y)) = axy
  ayx = Atom False $ PEq y x
  in (ayx, Node "symm" [(axy,nxy),(negAtom ayx,Leaf)])


--TODO: add eq axiom check
predStrong :: Atom -> Atom -> [(Atom,Node)] -> Node
predStrong aPr aPs sr = Node "predStrong" ((negAtom aPr, Leaf):(negAtom aPs, Leaf):sr)

paraStrong1 :: Atom -> (Atom,Node) -> (Atom,Node) -> (Atom,Node) -> Node
paraStrong1 aLp anpw anLw anrw = atomCong aLp anLw (trans anpw (symm anrw))

paraStrong2 :: Atom -> FunName -> (Atom,Node) -> (Atom,Node) -> (Atom,Node) -> [(Atom,Node)] -> Node
paraStrong2 aLfv f anfsr anLw anrw ansv = let
  anfvfs = symm (cong f ansv)
  anfvr = trans anfvfs anfsr
  anfvw = trans anfvr anrw
  in atomCong aLfv anLw anfvw

paraStrong3 :: Atom -> FunName -> (Atom,Node) -> (Atom,Node) -> [(Atom,Node)] -> Node
paraStrong3 aLfs f anfvw anLw ansv = let
  anfsfv = cong f ansv
  in atomCong aLfs anLw (trans anfsfv anfvw)

predWeak :: Node 
predWeak = Leaf

paraWeak :: Atom -> (Atom,Node) -> (Atom,Node) -> Node
paraWeak aLp anpw anLw = atomCong aLp anLw anpw

atomCong :: Atom -> (Atom,Node) -> (Atom,Node) -> Node
atomCong aLx (aLy,nLy) (axy,nxy) =
  if (aLx^.atom'sign) /= (aLy^.atom'sign) then error "aLx.sign /= aLy.sign" else
  case filter (\(tx,ty) -> tx/=ty) $ zip (aLx^.atom'args) (aLy^.atom'args) of {
    [(tx,ty)] -> Node "" [(negAtom aLx, Leaf),(aLy,nLy),termCong (tx,ty) (axy,nxy)];
    _ -> error "length diff/=1";
  }

termCong :: (Term,Term) -> (Atom,Node) -> (Atom,Node)
termCong (tx,ty) (axy,nxy) =
  if axy == (Atom False $ PEq tx ty) then (axy,nxy) else
  case (tx,ty) of {
    (TFun fx ax, TFun fy ay) | fx==fy -> case filter (\(tx,ty) -> tx/=ty) $ zip ax ay of {
      [txy'] -> (Atom False $ PEq tx ty, Node "termCong" [(Atom True $ PEq tx ty, Leaf), termCong txy' (axy,nxy)]);
      _ -> error "length diff/=1";
    };
    _ -> error "termCong";
  }

