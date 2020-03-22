module Tableaux where

import Numeric.Natural
import Test.QuickCheck
import Data.Tree
import Data.List
import Control.Monad 

data Wff t = 
   Sym t
 | Neg  (Wff t)
 | Conj (Wff t) (Wff t)
 | Disj (Wff t) (Wff t)
 | Impl (Wff t) (Wff t)
  deriving (Eq)

instance Show t => Show (Wff t) where
 show w = case w of 
  Sym t        -> show t 
  Neg v        -> "~" ++ show v 
  Conj v1 v2   -> "(" ++ show v1 ++ "⋀" ++ show v2 ++ ")"
  Disj v1 v2   -> "(" ++ show v1 ++ "⋁" ++ show v2 ++ ")"
  Impl v1 v2   -> "(" ++ show v1 ++ "⊃" ++ show v2 ++ ")"

--Chapter II. Analytic Tableaux (p. 15)

--product type for signed wff's
--I need record syntax w/ field accessors
--for something that I'll do later
data SignedWff t = Swff {
  bool :: Bool ,
  wff  :: (Wff t) 
  }
  deriving (Eq)

instance Show t => Show (SignedWff t) where 
 show (Swff b w) = [head $ show b] ++ " " ++ (show w)




--this feels sort of ad hoc but I can't think
--of a better way
type Box t = Either [t] (t, t) 

--data Either [t] (t, t) = 
 --Left [t]      |
 --Right (t, t)

--to construct a *term* of type :: Box t,
--you need to use either
 --Left,       on a [t], or
 --Right,      on a (t,t)

--we will need a function for fleshing out a subforest,
--based upon contents of the immediately preceding 'rootLabel'
--of the node

--trying out some argument capture w/ record syntax
stick_node :: Monoid a => a -> Tree a -> Tree a
stick_node x n@(Node {rootLabel = rl}) =
 n{rootLabel = x `mappend` rl}

--the behavior here has to depend on whether
--(subForest n) = [] or is non-empty
stick_leaves :: Monoid a => a -> Tree a -> Tree a
stick_leaves x n@(Node {subForest = sf}) =
 case sf of
  []               ->  n{subForest = sf ++ [Node x []]}   
  otherwise        ->  n{subForest = map (stick_node x) sf}
     


--renaming 'reduce' to 'elim' per the standard terminology
--re: elimination rules
elim :: SignedWff t -> Box (SignedWff t)
elim s@(Swff b w) =
 case (b, w) of 
  (_, Sym x)          -> Left  [s]
  (_, Neg v)          -> Left  [Swff (not b) v]
  --cases on Conj
  (True, Conj u v)    -> Left  [Swff b u,     Swff b v]
  (False, Conj u v)   -> Right (Swff False u, Swff False v)
  --cases on Disj
  (True, Disj u v)    -> Right (Swff True u,  Swff True v)
  (False, Disj u v)   -> Left  [Swff False u, Swff False v]
  --cases on Impl
  (True, Impl u v)    -> Right (Swff False u, Swff True v)
  (False, Impl u v)   -> Left  [Swff True u,  Swff False v]

--suppose you already know the shape of some elim'd
--swff s, via 'elim s :: Box Swff', and you want to
--do the appropriate thing to the tree you're working on
step ::  Box q -> Tree [q] -> Tree [q]
step b n@(Node rl sf) =
 case (b, sf) of
  (Left ws, _)            -> stick_leaves ws n 
  (Right (v, w), _)       --I can't think of a neater solution
   | null sf         ->  n{subForest = sf ++ [Node [v] []] ++ [Node [w] []]}
   | otherwise       ->  n{subForest = concat [map (stick_node [v]) sf,
                                               map (stick_node [w]) sf ] }

-- model one step of the evolution process
-- for an analytic tableau
next_level :: Tree [SignedWff t] -> Tree [SignedWff t]
next_level n@(Node rl sf) = 
 foldr step n (map elim rl)



--                  isTauto                    
--the main process can now be described as follows:
--starting with some          s  :: Wff t,
--and using the signed wff      s' := Swff False s :: Swff t, 
--build the tree              t = Node [f] []
--and determine whether, at root-label level,
--[f] consists of nothing but symbols :: Sym t
--if so, search it for contradictions
--otherwise,
   --1. t <- next_level t, to get t'
   --2. over the resulting subforest, subForest t',
   --   determine whether all root-labels are just
   --   list of symbols;
   --3a. if True, isTauto f = True iff 
   --             no root-label contains a contradiction;
   --                       = False otherwise
   --3b. if False, continue applying next_level 
   --but do it over the entire sub-forest this time

isSignSymList :: [SignedWff t] -> Bool
isSignSymList []                 = True
isSignSymList (z@(Swff b w):zs)  =
 case w of
  Sym _      -> isSignSymList zs
  _          -> False

--only to be used for applying `any` over a list of SignedWff's
contradicts :: (Eq t) => SignedWff t -> SignedWff t -> Bool
contradicts (Swff b s@(Sym p)) (Swff b' s'@(Sym p')) = 
 s == s' && b == not b'

--only to be used for filtering on a list of SignedWff's
same_sym :: (Eq t) => SignedWff t -> SignedWff t -> Bool
same_sym (Swff b s@(Sym p)) (Swff b' s'@(Sym p')) =
 s == s'


has_contra :: (Eq t) => [SignedWff t] -> Bool
has_contra []         = False
has_contra (w:ws)     =
 any (contradicts w) ws || 
  let l' = filter (not . same_sym w) ws
  in
   has_contra l'




--completely expand a signed wff into its tree
--with leaf-level nodes (i.e. having null sub-forest)
--all satisfying 
--   isSignSymList $ rootLabel n == True

--helper function to get all the leaf-level nodes of a tree
leaves :: Tree t -> [t]
leaves t@(Node rl sf)
 | null sf                   = [rl]
 | otherwise                 = 
     let ls = map leaves sf
     in
      concat ls

--when calling this function it's assumed that sf is null
expand :: Tree [SignedWff t] -> Tree [SignedWff t]
expand t@(Node rl sf)
 | isSignSymList rl          = t
 | otherwise                 =
     let t' = next_level t
     in
      t'{subForest = map expand (subForest t') }


isTauto :: (Eq t) => Wff t -> Bool
isTauto w =
   let false_w   = Swff False w
       tableau_w = expand $ Node [false_w] []
       leaves_w  = leaves tableau_w
   in
       all has_contra leaves_w     --given some well-formed formula of prop' logic: w,
                                   --w is a tautology (isTauto w == True) iff
                                   --its fully expanded tableau's final leaf-level
                                   --lists of SignedWff's each contain some contradiction
                                   --(these will each be lists of signed symbols)



{- For any concrete type based upon 'Tree', the default behavior 
   is for 'show' to print record syntax to the screen, due to 
   'Show (Tree a)' instance.
   For ease of illustration, we will newtype 'Tree [a]' into 
   'Tableau a' so that tableaux can be 'pretty printed' to the
   screen by default, unlike Tree's. -}
newtype Tableau a = Tableau {
  getTableau :: Tree [a]
  }

instance Show a => Show (Tableau a) where
 show tab =
  let tr = getTableau tab
  in  drawTree $ fmap show tr



-- Typeclass instances and functions for 'isTauto' property testing

{- helper functions for 'isTauto' property test -}
nTupleBool :: Int -> [ [Bool] ]
nTupleBool n = go n [ [] ]
 where go 0 l  = l 
       go m l  = [b:bs | b <- [True,False], bs <- go (m-1) l]

{- work out the *inputs* (left hand part) for all rows of 
  a wff's truth table, once you have the list of tokens
  appearing in it -}
truthTable_in :: [a] -> [ [(a, Bool)] ]
truthTable_in ts =
 let len   = length ts 
     ntups = nTupleBool len
 in  map (zip ts) ntups

{- given a wff & a list [(t, Bool)] pairing each token of 
  that wff with a truth value (True or False), work out whether
  the wff is true or false -}
evalTruthTableRow :: (Eq t) => Wff t -> [(Wff t, Bool)] -> Maybe Bool
evalTruthTableRow    w        ps = 
 case w of 
  Sym t           -> let idxM  = elemIndex (Sym t) $ map fst ps 
                         pairM = liftM (ps !!) $ idxM
                         sndM  = liftM snd 
                     in  sndM pairM
  Neg v           -> liftM not $ evalTruthTableRow v ps
  Conj v1 v2      -> (liftM2 (&&)) (evalTruthTableRow v1 ps)
                                   (evalTruthTableRow v2 ps)
  Disj v1 v2      -> (liftM2 (||)) (evalTruthTableRow v1 ps)
                                   (evalTruthTableRow v2 ps) 
  Impl v1 v2      -> (liftM2 (||)) (liftM not $ evalTruthTableRow v1 ps)
                                   (evalTruthTableRow v2 ps)

getSymTokens :: Wff t -> [Wff t]
getSymTokens w =
 case w of 
  Sym t           -> [Sym t]
  Neg v           -> getSymTokens v 
  Conj v1 v2      -> (getSymTokens v1) ++ (getSymTokens v2)
  Disj v1 v2      -> (getSymTokens v1) ++ (getSymTokens v2)
  Impl v1 v2      -> (getSymTokens v1) ++ (getSymTokens v2)

uniques :: (Eq a) => [a] -> [a]
uniques = foldr (\x l -> if not (x `elem` l) then x:l else l) []

getUniques :: (Eq t) => Wff t -> [Wff t]
getUniques = uniques . getSymTokens

{- given a wff, compute its full truth table -}
truthTable :: (Eq t) => Wff t -> [ [(Wff t, Maybe Bool)] ]
truthTable w = 
 let tokens = getUniques w         -- :: [Wff t]        
     inputs = truthTable_in tokens -- :: [] [(Wff t, Bool)]
 in  [ (map (\p -> (fst p, Just $ snd p)) inp) ++ [(w, evalTruthTableRow w inp)] | inp <- inputs ]

{- can I write a helper function to 'pretty print' a wff's truth table? -}
showTruthTable :: (Eq t, Show t) => Wff t -> IO ()
showTruthTable w = do
 let tbl    = truthTable w
 let header = map (show . fst) (head tbl)
 let h_tabs = intercalate ['\t'] header 
 putStrLn h_tabs
 let h_bars = intercalate ['\t'] $ map (const "---") header
 putStrLn h_bars 
 let show_mBool mb = case mb of 
      Just b    -> [head $ show b]
      Nothing   -> "_"
 let rw_ios = [ putStrLn $ intercalate ['\t'] $ map (show_mBool . snd) row | row <- tbl ] 
 sequence_ rw_ios
 
genWff :: Gen a -> Gen (Wff a)
genWff g = sized gen where
 gen n =
  frequency [ (1, liftM  Sym  g)
            , (n, liftM  Neg  (gen $ n `div` 2))
            , (n, liftM2 Conj (gen $ n `div` 2) (gen $ n `div` 2))
            , (n, liftM2 Disj (gen $ n `div` 2) (gen $ n `div` 2))
            , (n, liftM2 Impl (gen $ n `div` 2) (gen $ n `div` 2)) ]

instance Arbitrary a => Arbitrary (Wff a) where 
 arbitrary = genWff arbitrary

myArbWff :: Gen (Wff Char)
myArbWff = genWff $ elements ['a'..'d']

{- Pretty prints the truth tables for 10 randomly generated wff's. -}
showSampleTruthTbls :: IO ()
showSampleTruthTbls =
 (sample' myArbWff) >>= (sequence_ . (map showTruthTable))

lastColumn :: [ [(a,b)] ] -> [b]
lastColumn rows =
 let lastEntry row = snd $ row !! (length row - 1)
 in  map lastEntry rows 
 
