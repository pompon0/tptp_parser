module DNF where

import qualified Skolem as F
import Lib

data Form = Form [Cla]
data Cla = Cla { pos,neg :: [F.Pred] }

instance Show Form where
  show (Form x) = unlines (map show x)
instance Show Cla where
  show (Cla p n) = sepList n ++ " => " ++ sepList p

sumForm (Form x) (Form y) = Form (x ++ y)
prodForm (Form x) (Form y) = Form [Cla (px ++ py) (nx ++ ny) | Cla px nx <- x, Cla py ny <- y]

dnf :: F.Form -> Form
dnf (F.PosAtom p) = Form [Cla [p] []]
dnf (F.NegAtom p) = Form [Cla [] [p]]
dnf (F.Or x) = foldl sumForm (Form []) (map dnf x)
dnf (F.And x) = foldl prodForm (Form [Cla [] []]) (map dnf x)
