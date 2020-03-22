{-# LANGUAGE MonadComprehensions #-}
--need this in any files importing 'MonParsComs' as well -
--the 'import' statement won't just assume lang ext's from imported
--modules...

module PropWffParsing where

import Tableaux 
import MonParsComs
-- the ADT for wfform. We'll import this from Tableaux
-- data wfform t = 
--    Sym t
--  | Neg  (wfform t)
--  | Conj (wfform t) (wfform t)
--  | Disj (wfform t) (wfform t)
--  | Impl (wfform t) (wfform t)
--   deriving (Eq, Show)


{-
9/7/2019 : parser for wfform's of propositional logic.
Formation rules:
 1. 'p' followed by one or more apostrophes (') is a wfform
 2. for A    wfform  : ~A        is a wfform
 3. for A, B wfform's: (A⋀B) is a wfform
 4. for A, B wfform's: (A⋁B) is a wfform
 5. for A, B wfform's: (A⊃B) is a wfform
-}

{-
BNF grammar:
 psym     ::= p ' | psym '
 wfform   ::= psym | 
              unop wfform |
              ( wfform binop wfform )
 unop  ::= ~
 binop ::= ⋀ | ⋁ | ⊃
-}

--for now, I will parse 'wfform String' - would be great
--to be able to parse the different 
     -- p : take (n >= 1) . repeat '\''
--into distinct variables ... 

--N.B. in ghci, need to *escape* the character:   '
--by entering '\''
tick :: Parser Char  -- String -> [(Char, String)]
tick = char '\''

p_char :: Parser Char
p_char = char 'p'

--want to use: many1 :: Parser a -> Parser [a]
--since I need *one or more* apostr's following a p
psym :: Parser (Wff String) 
psym = [ Sym $ p : xs | p  <- p_char 
                      , xs <- many1 tick ]

--use `plus` instead, where the paper has (++)
--can I infix data constructors? Yes
--e.g. let x = 'c' `Pair` 5
unop :: Parser (Wff String -> Wff String)
unop = [ Neg | _ <- char '~' ]

binop :: Parser (Wff String -> Wff String -> Wff String)
binop = 
  -- [ Conj | _ <- char '⋀' ] `plus`
  -- [ Disj | _ <- char '⋁' ] `plus`
  -- [ Impl | _ <- char '⊃' ]
  -- --using 'ops':
  ops [(char '⋀', Conj) ,
       (char '⋁', Disj) ,
       (char '⊃', Impl) ]

binwfform :: Parser (Wff String)
binwfform = [ bin v w | v   <- wfform
                      , bin <- binop
                      , w   <- wfform ]

wfform :: Parser (Wff String)
wfform =   psym                     `plus`
           [ un v | un <- unop
                  , v  <- wfform ]  `plus`
           [ bv   | _   <- char '(' --simplify this after
                  , bv  <- binwfform
                  , _   <- char ')' ]

{-
Finally - there is only ever going to be one result by applying
this parser. In other words, for 

 let wff = runParser wfform $ str

for any (str :: String) that we care to apply the parser 'wfform' 
to, we should get '(length wff) == 1' - so the way to get a Maybe Wff
from this is: identify whether the 2nd part of the resulting tuple
is empty or not. If empty, then 'wfform' succeeded & we can return Just
the 1st part - otherwise, Nothing.
-}
maybeWff :: String -> Maybe (Wff String)
maybeWff str =
 case length finished of
  0              -> Nothing
  1              -> Just (fst $ head finished)
  _              -> Nothing
 where wf       = runParser wfform $ str
       finished = filter (\p -> null $ snd p) wf 
 

