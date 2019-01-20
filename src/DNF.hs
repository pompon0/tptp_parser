module DNF(dnf,simplify,Form(..),Cla(..),F.Pred(..),F.Term(..)) where

import qualified Skolem as F
import Lib
import qualified Data.Set.Monad as Set

data Form = Form { cla :: Set.Set Cla }
data Cla = Cla { pos,neg :: Set.Set Pred } deriving(Eq,Ord)
type Pred = F.Pred

instance Show Form where
  show (Form x) = unlines (map show $ Set.toList x)
instance Show Cla where
  show (Cla p n) = sepList (Set.toList n) ++ " => " ++ sepList (Set.toList p)

sumForm (Form x) (Form y) = Form (Set.union x y)
prodForm (Form x) (Form y) = Form $ do
  Cla px nx <- x
  Cla py ny <- y
  return $ Cla (Set.union px py) (Set.union nx ny)

dnf :: F.Form -> Form
dnf (F.PosAtom p) = Form $ Set.singleton $ Cla (Set.singleton p) Set.empty
dnf (F.NegAtom p) = Form $ Set.singleton $ Cla Set.empty (Set.singleton p)
dnf (F.Or x) = foldl sumForm (Form Set.empty) (map dnf x)
dnf (F.And x) = foldl prodForm (Form $ Set.singleton $ Cla Set.empty Set.empty) (map dnf x)


simplify :: Form -> Form
simplify (Form x) =
  let
    subClause (Cla px nx) (Cla py ny) = (Set.isSubsetOf px py) && (Set.isSubsetOf nx ny)
    nonTrivial  = Set.filter (\(Cla p n) -> Set.null $ Set.intersection p n) x
    notSubsumed = Set.filter (\c -> not $ any (\x -> x /= c && subClause x c) x) nonTrivial
  in Form notSubsumed

