{-# LANGUAGE FlexibleContexts #-}
module Parser where

import Prelude hiding(exponent,null)
import qualified Text.Parsec.Char as C
import qualified Text.Parsec as P
import qualified TraceM as N

parse :: N.TraceM m => String -> m ()
parse input = do
  case P.runP tptp_file () "input" input of
    Left err -> N.fail $ "parse error :: " ++ show err
    Right () -> return ()

char :: (P.Stream s m Char) => Char -> P.ParsecT s u m Char
char c = do { C.spaces; C.char c }
string :: (P.Stream s m Char) => String -> P.ParsecT s u m String
string s = do { C.spaces; C.string s }

tptp_file :: (P.Stream s m Char) => P.ParsecT s u m ()
tptp_file = do { C.spaces; P.many $ do {fof_annotated; C.spaces}; return () }
--tptp_input :: (P.Stream s m Char) => P.ParsecT s u m ()
--tptp_input = fof_annotated
--annotated_formula :: (P.Stream s m Char) => P.ParsecT s u m ()
--annotated_formula = fof_annotated
--annotations = null
--null = return ()
formula_role :: (P.Stream s m Char) => P.ParsecT s u m ()
formula_role = do { C.spaces; P.choice [
  P.try $ C.string "axiom",
  P.try $ C.string "hypothesis",
  P.try $ C.string "definition",
  P.try $ C.string "assumption",
  P.try $ C.string "lemma",
  P.try $ C.string "theorem",
  P.try $ C.string "corollary",
  P.try $ C.string "conjecture",
  P.try $ C.string "negated_conjecture",
  P.try $ C.string "plain",
  P.try $ C.string "type",
  P.try $ C.string "fi_domain",
  P.try $ C.string "fi_functors",
  P.try $ C.string "fi_predicates",
  P.try $ C.string "unknown"]; return () }

fof_annotated :: (P.Stream s m Char) => P.ParsecT s u m ()
fof_annotated = do
  string "fof"; char '('
  name; char ','
  formula_role; char ','
  fof_logic_formula; char ')'
  return ()

fof_logic_formula :: (P.Stream s m Char) => P.ParsecT s u m ()
fof_logic_formula = do
  fof_unit_formula
  P.many $ P.try $ do { connective; fof_unit_formula }
  return ()

fof_unit_formula :: (P.Stream s m Char) => P.ParsecT s u m ()
fof_unit_formula = P.choice [
  P.try $ do { char '~'; fof_unit_formula }, -- ~...
  P.try $ do {
    C.spaces;
    C.oneOf "!?"; char '['; fof_variable_list; char ']'; char ':';
    fof_unit_formula
  },
  P.try $ do {
    P.choice [P.try fof_plain_term, P.try variable];
    P.optionMaybe $ P.try $ do {
      P.choice[P.try $ string "!=", P.try $ string "="];
      P.choice[P.try fof_plain_term, P.try variable]
    };
    return ()
  },
  P.try $ do { char '('; fof_logic_formula; char ')'; return () }] -- (...
fof_variable_list :: (P.Stream s m Char) => P.ParsecT s u m ()
fof_variable_list = do { variable; P.many $ P.try $ do { char ','; variable }; return () }
-- a...
fof_plain_term :: (P.Stream s m Char) => P.ParsecT s u m ()
fof_plain_term = do
  lower_word -- a...
  P.optionMaybe $ P.try $ do {  char '('; fof_arguments; char ')'; }
  return ()
-- a/A...
fof_arguments :: (P.Stream s m Char) => P.ParsecT s u m ()
fof_arguments = do
  P.choice[P.try fof_plain_term, P.try variable]
  P.optionMaybe $ P.try $ do { char ','; fof_arguments }
  return ()

name :: (P.Stream s m Char) => P.ParsecT s u m String
name = P.choice [P.try lower_word, P.try integer]

connective :: (P.Stream s m Char) => P.ParsecT s u m String
connective = do { C.spaces; P.choice [
  P.try $ C.string "|",
  P.try $ C.string "&",
  P.try $ C.string "<=>",
  P.try $ C.string "=>",
  P.try $ C.string "<=",
  P.try $ C.string "<~>",
  P.try $ C.string "~|",
  P.try $ C.string "~&"] }

-- A...
variable :: (P.Stream s m Char) => P.ParsecT s u m ()
variable = do { upper_word; return () }
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

