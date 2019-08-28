{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Parser where

import Prelude hiding(exponent,null)
import Data.ProtoLens(defMessage)
import Lens.Micro((.~),(^.),(&))
import Data.ProtoLens.Labels()

import Lib
import qualified Data.Text as Text
import qualified Text.Parsec.Char as C
import qualified Text.Parsec as P
import qualified TraceM as N
import qualified Proto.Tptp as T

parse :: N.TraceM m => String -> m T.File
parse input = do
  case P.runP tptp_file () "input" input of
    Left err -> N.fail $ "parse error :: " ++ show err
    Right f -> return f

char :: (P.Stream s m Char) => Char -> P.ParsecT s u m Char
char c = do { C.spaces; C.char c }
string :: (P.Stream s m Char) => String -> P.ParsecT s u m String
string s = do { C.spaces; C.string s }

tptp_file :: (P.Stream s m Char) => P.ParsecT s u m T.File
tptp_file = do
  i <- tptp_input_list
  return $ defMessage & #input.~i
tptp_input_list :: (P.Stream s m Char) => P.ParsecT s u m [T.Input]
tptp_input_list = P.choice [
  P.try $ do { C.spaces; P.eof; return [] },
  do {
    C.spaces;
    f <- fof_annotated;
    l <- tptp_input_list; return (f:l);
  }] 

formula_role :: (P.Stream s m Char) => P.ParsecT s u m T.Input'Role
formula_role = do { C.spaces; P.choice [
  P.try $ do { C.string "axiom"; return T.Input'AXIOM },
  P.try $ do { C.string "hypothesis"; return T.Input'HYPOTHESIS },
  P.try $ do { C.string "definition"; return T.Input'DEFINITION },
  P.try $ do { C.string "assumption"; return T.Input'ASSUMPTION },
  P.try $ do { C.string "lemma"; return T.Input'LEMMA },
  P.try $ do { C.string "theorem"; return T.Input'THEOREM },
  P.try $ do { C.string "corollary"; return T.Input'COROLLARY },
  P.try $ do { C.string "conjecture"; return T.Input'CONJECTURE },
  P.try $ do { C.string "negated_conjecture"; return T.Input'NEGATED_CONJECTURE },
  P.try $ do { C.string "plain"; return T.Input'PLAIN },
  P.try $ do { C.string "type"; return T.Input'TYPE },
  P.try $ do { C.string "fi_domain"; return T.Input'FI_DOMAIN },
  P.try $ do { C.string "fi_functors"; return T.Input'FI_FUNCTORS },
  P.try $ do { C.string "fi_predicates"; return T.Input'FI_PREDICATES },
  P.try $ do { C.string "unknown"; return T.Input'UNKNOWN }]}

language :: (P.Stream s m Char) => P.ParsecT s u m T.Input'Language
language = do { l <- name; case l of {
  "fof" -> return T.Input'FOF;
  "cnf" -> return T.Input'CNF;
  _ -> fail ("unexpected language: " ++ l);
}}

fof_annotated :: (P.Stream s m Char) => P.ParsecT s u m T.Input
fof_annotated = do
  l <- language; char '('
  n <- name; char ','
  r <- formula_role; char ','
  f <- fof_logic_formula; char ')'; char '.'
  return $ defMessage
    & #language.~l
    & #name.~(Text.pack n)
    & #role.~r
    & #formula.~f

fof_logic_formula :: (P.Stream s m Char) => P.ParsecT s u m T.Formula
fof_logic_formula = do
  f :: T.Formula <- fof_unit_formula
  c :: [(T.Formula'Operator'Type,T.Formula)] <- P.many $ P.try $ do
    o <- connective
    f <- fof_unit_formula
    return (o,f)
  case c of
    [] -> return f
    (o,x):t -> case all (\(o',_)->o'==o) t of
        False -> fail "operator mismatch"
        True -> return $ defMessage & #op.~(defMessage & #type'.~o & #args.~f:x:(map snd t))

fof_neg_formula :: (P.Stream s m Char) => P.ParsecT s u m T.Formula
fof_neg_formula = do -- ~...
    char '~'
    f :: T.Formula <- fof_unit_formula
    return $ defMessage & #op.~(defMessage & #type'.~T.Formula'Operator'NEG & #args.~[f])

fof_quant_formula :: (P.Stream s m Char) => P.ParsecT s u m T.Formula
fof_quant_formula = do 
    C.spaces
    quantType <- P.choice [
      do { C.char '!'; return T.Formula'Quant'FORALL },
      do { C.char '?'; return T.Formula'Quant'EXISTS }]
    char '['
    vars :: [T.Term] <- fof_variable_list
    char ']'; char ':'
    f <- fof_unit_formula
    return $ defMessage
      & #quant .~ (defMessage & #type'.~quantType & #var.~(map (\t->t^. #name) vars) & #sub.~f)

fof_pred_formula :: (P.Stream s m Char) => P.ParsecT s u m T.Formula
fof_pred_formula = do
    l <- P.choice [P.try fof_plain_term, P.try variable]
    c :: Maybe (Bool,T.Term) <- P.optionMaybe $ P.try $ do
      neg :: Bool <- P.choice[
        P.try $ do { string "!="; return True },
        P.try $ do { string "="; return False }]
      r :: T.Term <- P.choice [P.try fof_plain_term, P.try variable]
      return (neg,r) 
    return $ case c of
      Nothing -> defMessage & #pred.~(defMessage
        & #type'.~T.Formula'Pred'CUSTOM & #name.~(l^. #name)& #args .~ (l^. #args))
      Just (neg,r) ->
        let eq = defMessage & #pred.~(defMessage & #type'.~T.Formula'Pred'EQ & #args.~[l,r]) in
        case neg of
          False -> eq
          True -> defMessage & #op.~(defMessage & #type'.~T.Formula'Operator'NEG & #args.~[eq])

fof_unit_formula :: (P.Stream s m Char) => P.ParsecT s u m T.Formula
fof_unit_formula = P.choice [
  P.try $ do { string "$true"; return $ defMessage & #op.~(defMessage & #type'.~T.Formula'Operator'TRUE) },
  P.try $ do { string "$false"; return $ defMessage & #op.~(defMessage & #type'.~T.Formula'Operator'FALSE) },
  P.try $ fof_neg_formula,
  P.try $ fof_quant_formula, 
  P.try $ fof_pred_formula,
  P.try $ do {
    char '(';
    f <- fof_logic_formula;
    char ')';
    return f;
  }] -- (...

fof_variable_list :: (P.Stream s m Char) => P.ParsecT s u m [T.Term]
fof_variable_list = P.sepBy variable (char ',')

-- a...
fof_plain_term :: (P.Stream s m Char) => P.ParsecT s u m T.Term
fof_plain_term = do
  name <- lower_word -- a...
  maybeArgs <- P.optionMaybe $ P.try $ do
    char '('
    args <- fof_arguments
    char ')'
    return args
  let term = defMessage & #type' .~ T.Term'EXP & #name .~ Text.pack name
  return $ case maybeArgs of
    Just args -> term & #args .~ args
    Nothing -> term
-- a/A...
fof_arguments :: (P.Stream s m Char) => P.ParsecT s u m [T.Term]
fof_arguments = P.sepBy (P.choice [P.try fof_plain_term, P.try variable]) (char ',')

name :: (P.Stream s m Char) => P.ParsecT s u m String
name = P.choice [P.try lower_word, P.try integer]

connective :: (P.Stream s m Char) => P.ParsecT s u m T.Formula'Operator'Type
connective = do { C.spaces; P.choice [
  P.try $ do { C.string "|"; return T.Formula'Operator'OR },
  P.try $ do { C.string "&"; return T.Formula'Operator'AND },
  P.try $ do { C.string "<=>"; return T.Formula'Operator'IFF },
  P.try $ do { C.string "=>"; return T.Formula'Operator'IMPL },
  --P.try $ do { C.string "<="; return T.Formula'Operator'IMPL }, -- TODO: fix it
  P.try $ do { C.string "<~>"; return T.Formula'Operator'XOR },
  P.try $ do { C.string "~|"; return T.Formula'Operator'NOR },
  P.try $ do { C.string "~&"; return T.Formula'Operator'NAND }] }

-- A...
variable :: (P.Stream s m Char) => P.ParsecT s u m T.Term
variable = do
  sname <- upper_word
  return $ defMessage
    & #type' .~ T.Term'VAR
    & #name .~ Text.pack sname
----------------------------------------------------

-- A...
upper_word :: (P.Stream s m Char) => P.ParsecT s u m String
upper_word = do 
  C.spaces
  h <- C.oneOf upper_alpha
  t <- P.many $ C.oneOf alpha_numeric
  return (h:t)
-- a...
lower_word :: (P.Stream s m Char) => P.ParsecT s u m String
lower_word = do
  C.spaces
  h <- C.oneOf lower_alpha
  t <- P.many $ C.oneOf alpha_numeric
  return (h:t)

-- +/-/0...
integer :: (P.Stream s m Char) => P.ParsecT s u m String
integer = P.choice [P.try signed_integer, P.try unsigned_integer]

-- +/-...
signed_integer :: (P.Stream s m Char) => P.ParsecT s u m String
signed_integer = do
  C.spaces
  s <- C.oneOf sign
  i <- unsigned_integer
  return (s:i)

-- 0...
unsigned_integer :: (P.Stream s m Char) => P.ParsecT s u m String
unsigned_integer = do { C.spaces; P.many1 $ C.oneOf numeric }

sign = "+-"
non_zero_numeric = "123456789"
numeric = "0123456789"
lower_alpha = "abcdefghijklmnopqrstuvwxyz"
upper_alpha = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
alpha_numeric = lower_alpha ++ upper_alpha ++ numeric ++ "_"

