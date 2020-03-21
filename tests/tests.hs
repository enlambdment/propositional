module Main where

import PropWffParsing
import Tableaux 
import MonParsComs
import Test.QuickCheck
import Test.Hspec
import Numeric.Natural
import Data.Tree
-- import Data.List
-- import Control.Monad



{-
 wfform     :: Parser (Wff String)
 runParser  :: Parser a -> String -> [(a, String)]

 newtype Parser a = Parser 
 { runParser :: String -> [(a, String)] }
-- note the bijection:
-- runParser :: Parser a -> String -> [(a, String)]
-- Parser    :: (String -> [(a, String)]) -> Parser a
-}

-- Values for testing 'PropWffParsing'

str1 :: String
str1 = "p'"

str2 :: String
str2 = "p''"

str3 :: String
str3 = "p'''"

str1' :: String
str1' = "(" ++ str1 ++ "⊃" ++ str2 ++ ")"

str2' :: String  
str2' = "(" ++ str1 ++ "⋀" ++ str3 ++ ")"

str3' :: String    --
str3' = "(" ++ str2 
            ++ "⋁"
            ++ str2'
     ++ ")"

str4' :: String
str4' = "(" ++ str3' 
            ++ "⋁"
            ++ str1'
     ++ ")"



-- Values & typeclass instance for testing 'Tableaux'

--for some simple examples, make a monoid instance
--for Natural

instance Semigroup Natural where
 (<>)      = (+)

instance Monoid Natural where
 mempty    = 0
 mappend   = (<>)

nats_tree_four :: Tree Natural
nats_tree_four = 
 Node 4
  [Node 5 [],
   Node 6 [],
   Node 7 []] 

nats_empty_sf :: Tree Natural
nats_empty_sf =
 Node 5
  []

nats_tree_seven :: Tree Natural
nats_tree_seven = 
 Node 7
  [Node 5 [],
   Node 6 [],
   Node 7 []]

nats_tree_four' :: Tree Natural
nats_tree_four' = 
 Node 4
  [Node 6 [],
   Node 7 [],
   Node 8 []]  

nats_nonempty_sf :: Tree Natural
nats_nonempty_sf =
 Node 5
  [Node 1 []]

ls_tree :: Tree [Natural]
ls_tree =
 Node [4,5,6]
 [Node [1,3,5] [],
  Node [1,2,3] [],
  Node [5,4,3] []]



p = Sym 'p'
q = Sym 'q'
r = Sym 'r'

w1 = p                     -- p
w2 = Conj p (Neg p)        -- p ⋀ ~p
w3 = Conj p q              -- p ⋀ q
w4 = Disj (Neg p) (Neg q)  -- ~p ⋁ ~q
w5 = Neg q                 -- ~q
w6 = Disj r (Neg p)        -- r ⋁ ~p

sw1 = Swff True w1                     -- (True, p)
sw2 = Swff False w5                    -- (False, ~q)
sw3 = Swff True w2                     -- (True, p ⋀ ~p)
sw4 = Swff False w3                    -- (False, p ⋀ q)
sw5 = Swff True w4                     -- (True, ~p ⋁ ~q)
sw6 = Swff False w6                    -- (False, r ⋁ ~p)
sw7 = Swff True (Impl w5 w4)           -- (True, ~q ⊃ (~p ⋁ ~q))
sw8 = Swff False (Impl (Neg w4) (w3))  -- (False, ~(~p ⋁ ~q) ⊃ (p ⋀ q))

tr3 = Node [sw3] []                    -- a conjunction at the rootLabel
tr5 = Node [sw5] []                    -- a disjunction at the rootLabel
tr7 = Node [sw7] []                    -- an implication at the rootLabel




{- 
 DESIRED PROPERTY OF 'isTauto':

a.
 GIVEN: an arbitrary    v :: Wff t,
 WHEN : every row of    truthTable v
        has             (v, Just True)
        as its last entry
 THEN : isTauto v == True

b.
 GIVEN: ...
 WHEN : any row of      truthTable v
        has             (v, Just False)
        as its last entry
 THEN : isTauto v == False        
-}

{- To write this property test, 
   need a way to generate arbitrary Wff Char's -}

{- auxiliary small data type to facilitate expedient 
   property tests for 'isTauto' -}
data X = X1 | X2 | X3 
 deriving (Eq, Show)

instance Arbitrary X where
 arbitrary = elements [X1, X2, X3]

prop_alwaysTrue_isTauto :: Wff X -> Property 
prop_alwaysTrue_isTauto w =
 all (== Just True) ((lastColumn . truthTable) w) ==>
  isTauto w 

prop_everFalse_notTauto :: Wff X -> Property
prop_everFalse_notTauto w =
 any (== Just False) ((lastColumn . truthTable) w) ==>
  not (isTauto w)



main :: IO ()
main = hspec $ do
 describe "PropWffParsing" $ do
  it "p' is a well-formed formula" $ do
   maybeWff str1 `shouldBe` (Just $ Sym "p'") 
  it "p'' is a well-formed formula" $ do
   maybeWff str2 `shouldBe` (Just $ Sym "p''") 
  it "p''' is a well-formed formula" $ do
   maybeWff str3 `shouldBe` (Just $ Sym "p'''")
  it "(p'⊃p'') is a well-formed formula" $ do
   maybeWff str1' `shouldBe` (Just $ Impl (Sym "p'") (Sym "p''"))
  it "(p'⋀p''') is a well-formed formula" $ do
   maybeWff str2' `shouldBe` (Just $ Conj (Sym "p'") (Sym "p'''")) 
  it "(p''⋁(p'⋀p''')) is a well-formed formula" $ do
   maybeWff str3' `shouldBe` (Just $ Disj (Sym "p''") (Conj (Sym "p'") (Sym "p'''")))
 describe "Tableaux" $ do
  {- testing the functions to evolve root-label & sub-forest -}
  it "stick 3 to root node: 4, to get root node: 7" $ do
   stick_node 3 nats_tree_four `shouldBe` nats_tree_seven
  it "stick 1 to leaves, to get all leaves incremented" $ do
   stick_leaves (1 :: Natural) nats_tree_four `shouldBe` nats_tree_four'
  it "stick 1 to empty leaves, to get new leaf with 1" $ do
   stick_leaves (1 :: Natural) nats_empty_sf `shouldBe` nats_nonempty_sf
  {- testing the function 'elim' to eliminate a signed well formed formula into more 'atomic' statements -}
  it "elim (True, p) = [ (True, p) ]" $ do 
    elim sw1 `shouldBe` Left [Swff True p]
  it "elim (False, ~q) = [ (True, q) ]" $ do 
    elim sw2 `shouldBe` Left [Swff True q]
  it "elim (True, p ⋀ ~p) = [ (True, p), (True, ~p) ]" $ do 
    elim sw3 `shouldBe` Left [Swff True p, Swff True (Neg p)]
  it "elim (False, p ⋀ q) = ( (False, p), (False q) )" $ do
    elim sw4 `shouldBe` Right (Swff False p, Swff False q)
  it "elim (True, ~p ⋁ ~q) = ( (True, ~p), (True, ~q) )" $ do 
    elim sw5 `shouldBe` Right (Swff True (Neg p), Swff True (Neg q))
  it "elim (False, r ⋁ ~p) = [ (False, r), (False, ~p) ]" $ do 
    elim sw6 `shouldBe` Left [Swff False r, Swff False (Neg p)]
  it "elim (True, ~q ⊃ (~p ⋁ ~q)) = ( (False, ~q), (True, (~p ⋁ ~q)) )" $ do 
    elim sw7 `shouldBe` Right (Swff False (Neg q), Swff True (Disj (Neg p) (Neg q)))
  it "elim (False, ~(~p ⋁ ~q) ⊃ (p ⋀ q)) = [ (True, ~(~p ⋁ ~q)), (False, (p ⋀ q)) ]" $ do 
    elim sw8 `shouldBe` Left [Swff True (Neg (Disj (Neg p) (Neg q))), Swff False (Conj p q)]
  {- testing the function 'next_level' to evolve out the next layer of a tableaux -}
  it "a true conjunction's next level contains one branch with both conjuncts" $ do
    (subForest $ next_level tr3) `shouldBe` 
     [Node {rootLabel = [Swff {bool = True, wff = Sym 'p'},
                         Swff {bool = True, wff = Neg (Sym 'p')}], 
            subForest = []}] 
  it "a true disjunction's next level contains two branches with one disjunct each" $ do 
    (subForest $ next_level tr5) `shouldBe`
     [Node {rootLabel = [Swff {bool = True, wff = Neg $ Sym 'p'}],
            subForest = []},
      Node {rootLabel = [Swff {bool = True, wff = Neg $ Sym 'q'}],
            subForest = []}]
  it "a true implication's next level contains two branches: false antecedent or true consequent" $ do
    (subForest $ next_level tr7) `shouldBe`
     [Node {rootLabel = [Swff {bool = False, wff = w5}],
            subForest = []},
      Node {rootLabel = [Swff {bool = True, wff = w4}],
            subForest = []}]
 describe "Property tests for 'isTauto'" $ do 
  it "a well-formed formula true for every row of its truth table is a tautology" $ do 
   quickCheck prop_alwaysTrue_isTauto
  it "a well-formed formula false for any row of its truth table is not a tautology" $ do
   quickCheck prop_everFalse_notTauto

   
