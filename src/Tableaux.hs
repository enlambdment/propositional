module Tableaux where

import Numeric.Natural
import Data.Tree

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
  deriving (Eq, Show)

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
     




--examples, for a tree of elements types [Swff t]

bxswf1 :: Box (SignedWff Char)
bxswf1 = Left 
 [Swff True $ Sym  'p',
  Swff False $ Sym 'q',
  Swff True $ Sym  'r']

bxswf2 :: Box (SignedWff Char)
bxswf2 = Right 
 (Swff True  $ Sym 'q',
  Swff False $ Sym 'p')

swffs_tree :: Tree [SignedWff Char]
swffs_tree =
 Node [Swff True $ Sym 'a', Swff False $ Sym 'b'] 
  [Node [Swff True $ Sym 'c', Swff False $ Sym 'd'] [],
   Node [Swff True $ Sym 'c', Swff False $ Sym 'd', Swff True $ Sym 'f'] [],
   Node [Swff True $ Sym 'd', Swff False $ Sym 'f'] []]


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

--move this out into a scratch file and/or tests?
{-
p = Sym 'p'
q = Sym 'q'
r = Sym 'r'

t1 :: Tree [SignedWff Char]
t1 = 
 Node [Swff True p] []

t2 =
 Node [Swff True (Conj p q)] []

t3 =
 Node [Swff True (Conj p q)]
  [Node [Swff True  r] 
        [],
   Node [Swff False r] 
        []
        ] 
    
t4 =
 Node [Swff True (Conj p q),
       Swff True r]       
   [] 

t4' =
 Node [Swff True r,
       Swff True (Conj p q)]       
   [] 

t5 = 
 Node [Swff True (Disj p q)] []

t6 =
 Node [Swff True (Disj p q), Swff True r, Swff False q] []

t7 =
 Node [Swff True  (Disj p q),
       Swff False (Conj p (Neg r)),
       Swff True (Impl r q)]
      []
-}
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


--these wff's should give `isTauto w = False`
--move this out into a scratch file and/or tests?
{-
wff1 = p
wff2 = q
wff3 = r

wff4 = Conj p q
wff5 = Disj p r
wff6 = Impl p q

--these wff's should give `isTauto w = True`
wff7 = Disj p (Neg p)
wff8 = Impl p (Disj p q)
wff9 = 
 Impl
  (Impl p (Impl q r))
  (Impl (Impl p q) (Impl p r)) 
  -}







--auxiliary function for use with drawTree
--need to turn every node into a 'String' ?

--'drawTree' has type :: Tree String -> String,
--so first, need to be able to turn Tree [SignedWff t]
--into Tree String  
mapTree :: (a -> b) -> Tree a -> Tree b 
mapTree f (Node rl sf) = Node (f rl) (map (mapTree f) sf)

stringifyTree :: (Show t) => Tree t -> Tree String
stringifyTree = mapTree show

--start from a SignedWff t; show its resulting,
--fully expanded tree via tableau method, using
--'drawTree'
--It does but I wanted, but the tree printing
--doesn't work well with record syntax ...
drawTableau :: (Show t) => SignedWff t -> String
drawTableau swff = 
  let 
    t_0 = Node [swff] []
  in
    drawTree $ stringifyTree $ expand t_0

