{-# LANGUAGE MonadComprehensions #-}

module MonParsComs where 

-- to resolve: "Not in scope: type constructor or class ‘Alternative’"
import qualified Control.Applicative as CA
import qualified Control.Monad       as M

--parser type, with type parameter for the type
--of the result to be returned

{-
use of 'newtype' here does two things for us:
1. allows us to give the Monad instance declaration
   the name of a data type, however
2. also lets us place a field in the data-constructor part
   which serves to implement part of an *isomorphism* between
   'Parser a' & 'String -> [(a, String)]'. We now can apply the
   function contained in a term p :: Parser a *without* having 
   to pattern match on p's contents.
-}
newtype Parser a = Parser 
 { runParser :: String -> [(a, String)] }
-- note the bijection:
-- runParser :: Parser a -> String -> [(a, String)]
-- Parser    :: (String -> [(a, String)]) -> Parser a


--given:              v :: a,
--gives back a parser which
 --1. returns v as result
 --2. consumes none of its input string
result :: a -> Parser a
result v = Parser $
 \inp -> [(v, inp)]

--a parser which
 --1. has no result
 --2. discards its input altogether
zero :: Parser a
zero = Parser $
 \inp -> []

--a parser which
 --1. consumes 1st char. off of input string,
 --   if non-empty;
 --2. otherwise, fails just like 'zero'
item :: Parser Char
item = Parser $
 \inp -> case inp of
  []      -> []
  (x:xs)  -> [(x, xs)]

--'sq' applies p to its input,
--     then applies q to the unconsumed part of input,
--     finally parsing off pairs of type (a, b)
--     with their unconsumed part of input due to p, q.
--'sq' *simply juxtaposes 1st & 2nd parsers' results*
--     without doing anything else on them to 'put them
--     together' or such
sq :: Parser a -> Parser b -> Parser (a,b)
p `sq` q = Parser $ 
 \inp -> 
  [((v,w), inp'') | (v, inp')  <- runParser p $ inp,
                    (w, inp'') <- runParser q $ inp' ]

--can think of 'bind' as
--1. parsing off from the input using p :: Parser a
--   if possible, then
--2. applying f to its result in order to 'get back'
--   a Parser b, to finish working on inp (via inp')
bind :: Parser a -> (a -> Parser b) -> Parser b
p `bind` f = Parser $ 
 \inp -> 
  concat 
   [ (runParser $ f v) inp' | (v, inp') <- runParser p $ inp ]

{-
Example:
These two functions do the same thing:
-}
sum_three :: Parser Integer
sum_three = 
 digit `bind` \x1 ->
  digit `bind` \x2 ->
   digit `bind` \x3 ->
    result (sum $ map (read . (:[])) [x1, x2, x3])

sum_three' :: Parser Integer
sum_three' = Parser $
 \inp ->
  concat
   [runParser (result (sum $ map (read . (:[])) [v1, v2, v3]))
              inp'''
    | (v1, inp')        <- runParser digit $ inp     ,
      (v2, inp'')       <- runParser digit $ inp'    ,
      (v3, inp''')      <- runParser digit $ inp''            ]



--now, use item to define a combinator 'sat' that
-- 1. takes a predicate (Boolean-valued function),
--    and yields
-- 2. a parser that consumes a single character
--    *if the character satisfies the predicate,*
--    but fails otherwise
sat :: (Char -> Bool) -> Parser Char 
sat p = 
 item `bind` 
  (\x -> if p x 
         then result x
         else zero)

--using 'sat', we can define parsers for specific characters, single digits,
--lower-case letters, and upper-case letters:
char :: Char -> Parser Char
char x = sat (\y -> x == y) 

digit :: Parser Char 
digit = sat (\y -> '0' <= y && y <= '9')  

lower :: Parser Char
lower = sat (\y -> 'a' <= y && y <= 'z')

upper :: Parser Char
upper = sat (\y -> 'A' <= y && y <= 'Z')

{-
Consider the parser that accepts two lower-case
letters in sequence, returning a string of length
two:
-}
two_lowers :: Parser [Char]
two_lowers =
  lower `bind` \x ->
  lower `bind` \y ->
  result [x, y]


plus     :: Parser a -> Parser a -> Parser a
p `plus` q = Parser $ \inp ->
 (runParser p $ inp) ++ (runParser q $ inp)


letter :: Parser Char
letter = lower `plus` upper 

alphanum :: Parser Char 
alphanum = digit `plus` letter

{-
More interestingly, a parser for words (strings of letters) is defined
by
-}
-- word :: Parser String   --String -> [(String, String)]
-- word = Parser $ \inp ->
--  (runParser neWord $ inp) ++ ((runParser $ result "") inp) 
--  where 
--   neWord = letter `bind` \x  ->   -- if inp starts with a letter
--            word   `bind` \xs ->
--            result (x:xs)

-- monParsComs.hs:131:10: error:
--     • No instance for (Applicative Parser)
--         arising from the superclasses of an instance declaration
--     • In the instance declaration for ‘Monad Parser’

-- instance Monad Parser where
--  return = result
--  (>>=)  = bind

-- can I work out how to write Applicative, Functor typeclass
-- instances for 'Parser'?

-- gonna start "from the top" & see if I can work my way down ...

-- Functor
--   |
--   V
-- Applicative
--   |
--   V
-- Monad

-- I could just define this in terms of 'bind', but 
-- I am avoiding doing so in order not to reason 
-- circularly ...
parsemap :: (a -> b) -> Parser a -> Parser b
parsemap f p = Parser $ 
 \inp ->
  [(f v, inp') | (v, inp') <- runParser p $ inp]

instance Functor Parser where
 fmap = parsemap

-- this 'fmap' is lawful because:
-- 1. fmap (id :: a        -> b       ) =
--          id :: Parser a -> Parser b
-- 2. fmap (g . f)                      =
--    (fmap g) . (fmap f)

-- is this lawful?
-- seems to work for now but perhaps come back to this later ...
parseply :: Parser (a -> b) -> Parser a -> Parser b 
fp `parseply` q = Parser $ 
 \inp ->
  [ (phi v, inp'') | (v, inp')    <- runParser q  $ inp
                   , (phi, inp'') <- runParser fp $ inp' ]

instance Applicative Parser where
 pure  = result
 (<*>) = parseply

--
instance Monad Parser where
 return = result
 (>>=)  = bind

-- some examples to check out the Applicative laws
-- with. 
-- Need to confirm:

-- 1. IDENTITY: For any parser v,
-- result id `parseply` v = v

-- 2. HOMOMORPHISM: For any f :: a -> b
--                    , any x :: a
-- result f `parseply` result x = result (f x)

-- 3. INTERCHANGE: For any parser u :: Parser (a -> b)
--                   , any x :: a
-- u `parseply` result y = result ($ y) `parseply` u

-- 4. COMPOSITION:
-- u <*> (v <*> w) = pure (.) <*> u <*> v <*> w

-- e.g.
-- these 2 composite parsers should give the same output. (& they do)
-- dbl_sult `parseply` (rev_sult `parseply` word)
-- result (.) `parseply` dbl_sult `parseply` rev_sult `parseply` word

mayprep :: Parser (String -> String)
mayprep = Parser $
 \inp ->
  case inp of 
   []     -> [( id  , [])]
   (x:xs) -> [( (x:), xs)]

q_sult :: Parser String
q_sult = result "q"

rev_sult :: Parser (String -> String)
rev_sult = result reverse

dbl :: String -> String
dbl = concat . take 2 . repeat

dbl_sult :: Parser (String -> String)
dbl_sult = result 
 (concat . take 2 . repeat)


{-
Monad comprehension syntax
-}

{- 
Yet a 3rd way to write 'sum-three':
requires 'MonadComprehensions' lang. ext.
-}

-- notice that with this syntax,
-- the intermediate inp, inp', inp'', inp'''
-- are *not* given variable names or even mentioned at all.
-- Nor is the output of the transformation we apply on the 
-- parsed-off items handed off to a 'result' to deal with.
sum_three'' :: Parser Integer
sum_three'' = 
  [ sum (map (read . (:[])) [x1, x2, x3]) | 
     x1 <- digit 
   , x2 <- digit
   , x3 <- digit]

{-
"As our first example of using comprehension notation, we define
a parser for recognizing specific strings, with the string itself
returned as the result:"
-}

-- first, how would you write this normally with bind / plus?
stringy :: String -> Parser String
stringy str = 
 --either str is empty, *or* else it has at least one char
 --if has at least one char, then need to parse off 1st char
 --from the inp *and* attempt to parse off the rest from the
 --inp
 case str of
  ""       -> result ""
  (x:xs)   ->
   char    x  `bind` \x ->
   stringy xs `bind` \xs ->
   result (x:xs)

-- now, with monad comprehension syntax
string :: String -> Parser String
string ""        = result "" -- [""] here doesn't work
string (x:xs)    = [ x:xs | x <- char x, xs <- string xs]

{-
"In list comprehension notation, we are not just restricted to
generators that bind variables to values, but can also use 
Boolean-valued guards that restrict the values of the bound
variables. For example, a function 'negs' that selects all the
negative numbers from a list of integers can be expressed as 
follows:"
-}

negs    :: [Int] -> [Int]
negs xs = [ x | x <- xs, x < 0]

{-
"Wadler (1990) observed that the use of guards makes sense for 
an arbitrary monad with a zero. The monad comprehension notation
in Gofer supports this use of guards. For example, the 'sat' combinator
can be defined more succinctly using a comprehension with a guard:"
-}

{-
I get:
 No instance for (GHC.Base.Alternative Parser) 
 arising from a statement in a monad comprehension
-}

--so, I'm missing a typeclass instance

instance CA.Alternative Parser where
 empty = zero
 (<|>) = plus

sat' :: (Char -> Bool) -> Parser Char 
sat' p = [ x | x <- item, p x ]

{-
"We conclude this section by noting that there is another notation that can
be used to make monadic programs easier to read: the so-called `do` notation.
For example, using this notation the combinators string, sat can be defined
as follows:"
-}
stringo :: String -> Parser String
stringo ""      = do { result "" }
stringo (x:xs)  = do { char x ; string xs ; result (x:xs) }

-- this example doesn't compile.
-- sato     :: (Char -> Bool) -> Parser Char 
-- sato p    = do { x <- item ; if (p x) ; result x } 
sato :: (Char -> Bool) -> Parser Char
sato p = do 
 x <- item
 if (p x) then result x 
          else zero

-- 4. Combinators for repetition
{-
4.1 Simple repetition
Earlier we defined a parser 'word' for consuming zero or more letters from the
input string. Using monad comprehension notation, the definition is:
-}
-- to imitate the paper's syntax, we require an instance of typeclass MonadPlus
-- also note that MonadPlus has 'mplus' operation, not '(++)', defined

instance M.MonadPlus Parser where
 mzero = zero
 mplus = plus

word :: Parser String
word = [ (x:xs) | x <- letter, xs <- word   ]
       `plus` [ b | b <- result "" ]

-- CA.many comes 'for free' with CA.Alternative. Let's write our own anyway:
{-
"The combinator 'many' applies a parser p zero or more times to an input string.
The results from each application of p are returned in a list:"
-}
many :: Parser a -> Parser [a]
many p = [ (x:xs) | x  <- p,
                    xs <- many p ]
         `plus` -- '[]' is "" but de-specialized to any type whatsoever
                -- and not just [Char] i.e. String
         [ b      | b <- result [] ]

{-
"As another application of many, we can define a parser for identifiers.
For simplicity, we regard an identifier as a lower-case letter followed by
zero or more alphanumeric characters. It would be easy to extend the 
definition to handle extra characters, such as underlines or backquotes."
-}
ident :: Parser String 
ident = [ (x:xs) | x  <- lower, 
                   xs <- many alphanum ]

{-
"Sometimes we will only be interested in non-empty sequences of items.
For this reason we define a special combinator, 'many1', in terms of many:"
-}
many1 :: Parser a -> Parser [a]
many1 p = 
 -- the *only* difference is that we don't include the 'result []'
 -- alternative where we give up. Either there is at least 1 char.
 -- at the front which p can parse, or else no results come back.

 -- 'many1 p' may fail, whereas 'many p' always succeeds.
 [ x:xs | x <- p, xs <- many p]

{-
"Using 'many1' we can define a parser for natural numbers:"
-}
nat :: Parser Int 
nat = [ read x | x <- many1 digit ]

{-
"In turn, 'nat' can be used to define a parser for integers:"
-}
int :: Parser Int 
int = [ -n | _  <- char '-' ,   -- captures subcase of a negative int.
                                -- no need to name the value since we 
                                -- don't do anything with it.
             n  <- nat ] -- no need to read 'ys'; this already
                         -- comes back as an 'Int'
      `plus` nat -- captures subcase of a non-negative int

{-
A more sophisticated way to define 'int' is as follows. First try and
parse the negation character '-'. If this is successful then return the
negation function as the result of the parse; otherwise return the identity
function. The final step is then to parse a natural number, and use the
function returned by attempting to parse the '-' character to modify
the resulting number:
-}
int' :: Parser Int 
int' = [ f n | f <- op , n <- nat ]
    where
     op -- :: Num a => Parser (a -> a) 
          = [ negate | _ <- char '-'  ] `plus` 
            [ id     | _ <- result [] ]

-- 4.2 Repetition with separators

-- this works, but is hideous to look at. (the case where you assume
-- that the input string is to be parsed into a *non-empty* list is 
-- easier & has less case logic thrown about)
intso :: Parser [Int]
intso = 
 --first, the input string has to start out right, or else
 --fail right away
 char '[' `bind` \x ->           -- Parser Char
  --following char is either ']' or one or more ints separated by ','
  f `bind` \y ->
   result y
 where f = (int `bind` \m ->        -- int, then comma, then more ints
            char ',' `bind` \x ->
            f         `bind`  \ms ->
            result (m:ms) ) 
               `plus` 
           (int `bind` \m ->        -- int, then ']'
            char ']' `bind` \x ->
             result [m])
               `plus`
           (char ']' `bind` \x ->   -- ']', following right after the '['
            result [])

-- simplifying with monad comprehension syntax
intso' :: Parser [Int]
intso' =
 [ l | _ <- char '[' ,
       l <- f ]
 where 
  f = [ m:ms | m  <- int ,
               _  <- char ',' ,
               ms <- f ]
       `plus`
      [ [m]  | m  <- int ,
               _  <- char ']' ]
       `plus`
      [ []   | _  <- char ']' ]

{-
Solution for the case of a non-empty list of ints:
"The 'many' combinators parse sequences of items. Now we consider a slightly 
more general pattern of repetition, in which separators between the items
are involved. Consider the problem of parsing a non-empty list of integers,
such as [1,-42,17]. Such a parser can be defined in terms of the 'many' 
combinator as follows:"
-}

ints :: Parser [Int]
ints = [ n:ns | _   <- char '[' 
              , n   <- int 
              , ns  <- many [ m | _ <- char ',' , m <- int ]  
              , _   <- char ']' ]

{-
"As was the case in the previous section for the 'word' parser, we can imagine
a number of other parsers with a similar structure to 'ints', so it is useful 
to abstrct on the pattern of repetition and deefine a general purpose combinator,
which we call 'sepby1'. The combinator 'sepby1' is like 'many1' in that it recognizes
non-empty sequences of a given parser p, but different in that the instances of p
are separated by a parser 'sep' whose result values are ignored:"
-}
sepby1       :: Parser a -> Parser b -> Parser [a]
p `sepby1` sep =
 [ x:xs | x  <- p
        , xs <- many [ y | _ <- sep, y <- p ] ]

{-
"Now ints can be defined in a more compact form:"
-}
-- ints'     :: Parser [Int]
-- ints' = [ ns | _   <- char '[' 
--              , ns  <- int `sepby1` char ',' 
--              , _   <- char ']' ]

{-
"In fact we can go a little further. The bracketing of parsers by other parsers
whose results are ignoeed - in the case above, the bracketing parsers are char '['
and char ']' - is common enough to also merit its own combinator:"
-}

bracket :: Parser a -> Parser b -> Parser c -> Parser b
bracket open p close = 
 [ val | _   <- open 
       , val <- p
       , _   <- close ]

{-
"Now ints can be defined just as"
-}
ints' :: Parser [Int]
ints' = bracket (char '[')
                (int `sepby1` char ',')
                (char ']')

{-
Finally, while many1 was defined in terms of many, the combinator sepby
(for possibly-empty sequences) is naturally defined in terms of sepby1:
-}
sepby :: Parser a -> Parser b -> Parser [a]
p `sepby` sep = (p `sepby1` sep) `plus`
                [ [] | _ <- result [] ]

-- 4.3 Repetition with meaningful separators
{-
Consider the problem of parsing simple arithmetic expressions such as
1+2-(3+4) , built up from natural numbers using add'n, subtr'n, parens.
The 2 arith. op's are assumed to associate to the left, thus e.g.
          1-2-3     should be parsed as:   (1-2)-3
, and have the same precedence. The standard BNF grammar for such expr's is
written as follows:

 expr   ::= expr addop factor | factor
 addop  ::= + | -
 factor ::= nat | ( expr )

This grammar can be translated directly into a combinator parser:
-}

-- expr   :: Parser Int 
-- expr = [ f x y | x <- expr 
--                , f <- addop
--                , y <- factor ]
--        `plus` factor 

-- addop  :: Parser (Int -> Int -> Int)
-- addop = [ (+) | _ <- char '+'] `plus`
--         [ (-) | _ <- char '-']

-- factor :: Parser Int 
-- factor = nat `plus` 
--          bracket (char '(')
--                  expr
--                  (char ')')

{-
"In fact, rather than just returning some kind of parse tree, the 'expr' 
parser above actually evaluates arithmetic expressions to their integer 
value : the addop parser returns a function as its result value, which
is used to combine the result values produced by parsing the arguments 
to the operator.

Of course, however, there is a problem with the expr parser as defined 
above. The fact that the operators associate to the left is taken account 
of by expr being *left-recursive* - the first thing it does is make a
recursive call to itself. Thus expr never makes any progress, and does
not terminate."

Instead - *replace left-recursion by iteration*!
The idea is that you can just read off a factor on the left of the input
string, and if you encounter parens then you know you're dealing with a
subordinate expression - otherwise, just read off a nat.
-}

{-
"Looking at the expr grammar, we see that an expression is a sequence 
of *factors* (either nat's or themselves expressions) , separated by 
*addops*. Thus the parser for expressions can be re-defined using many
as follows:
-}
-- expr :: Parser Int
-- expr = [ foldl (\a (g, b) -> a `g` b) 
--                x
--                fys
--         | x   <- factor  -- foldl, due to left-associativity
--         , fys  <- many [ (f,y) | f <- addop, y <- factor ] ]

-- addop :: Parser (Int -> Int -> Int)
-- addop = [ (+) | _ <- char '+' ] `plus`
--         [ (-) | _ <- char '-' ]

factor :: Parser Int 
factor = nat `plus` bracket (char '(')
                            expr
                            (char ')')

{-
"Playing the generalization game once again, we can abstract on the pattern
of repetition in 'expr' and define a new combinator. The combinator, chainl1,
parses non-empty sequences of items separated by operators that associate to
the left:"
-}
-- chainl1      :: Parser a -> Parser (a -> a -> a) -> Parser a
-- p `chainl1` op = [ foldl (\x (f,y) -> f x y)
--                          x
--                          fys 
--                  | x   <- p
--                  , fys <- many [ (f,y) | f <- op, y <- p ]]

{-
"Thus our parser for expressions can now be written as follows:"
-}
expr :: Parser Int 
expr = factor `chainl1` addop

{-
"Most operator parsers will have a similar structure to addop above, so it is
useful to abstract a combinator for building such parsers:"
-}
ops  :: [(Parser a, b)] -> Parser b 
ops xs = foldr1 plus [ [op | _ <- p] | (p,op) <- xs ]

addop :: Num a => Parser (a -> a -> a)
addop = ops [ (char '+', (+)) , (char '-', (-)) ]

{-
"A possible inefficiency in the definition of the chainl1 combinator is the
construction of the intermediate list fys. This can be avoided by giving 
a direct recursive definition of chainl1 that does not make use of foldl and
many, using an *accumulating parameter* to construct the final result" - 
i.e. instead of building up a structured intermediate result & only collapsing
     by evaluation at the very last minute,
     only keep on hand the *intermediate output* gotten by evaluating the portion
     parsed so far.
-}
chainl1       :: Parser a -> Parser (a -> a -> a) -> Parser a
p `chainl1` op = 
 p  `bind` rest
 where 
  rest x = (op `bind` \f ->
              p `bind` \y ->
               rest (f x y) ) 
           `plus` [ x | _ <- result x ]
