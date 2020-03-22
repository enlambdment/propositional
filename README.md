# propositional

_This README was formatted with the help of [StackEdit](https://stackedit.io/), an in-browser Markdown editor._

The purpose of this project was to write Haskell code to do two things:

1. Given a string which is written in some formal language for truth-functional propositional logic, _parse the string_ in order to produce a term of some type bearing tree-like structure (to reflect the structure of the well-formed formula, or _wff_)
2. Given a well-formed formula (_wff_) of truth-functional propositional logic, _determine whether it is a tautology_ by using the method of analytic tableaux.

This README will briefly introduce truth-functional propositional logic, analytic tableaux, and the main functionality implemented via this package's modules.

## Truth-functional propositional logic

(The following summary is based on _Metalogic: An Introduction to the Metatheory of Standard First Order Logic_, Geoffrey Hunter.)

In this context, _truth function_ refers to a mapping from sequences of truth values (True or False) to truth values. _Truth-functional propositional logic_, then, refers to the system of logic (rules concerning the truth or falsehood of well-formed formulae, as well as relating the truth or falsehood of given wff's with other wff's) that concerns propositions.

This system of logic is thus concerned with bare (a.k.a. atomic, etc.) propositions, denoted by _propositional symbols_, and the formulae built up out of them by use of _logical connectives._

The formal language P which Hunter uses for propositional logic is as follows (p. 54):

> _Symbols of P_  
> P has exactly six symbols, viz.:  
> p  
> ' [dash]   
> ~ [tilde]  
> ⊃ [hook]  
> ( [left-hand bracket]  
> ) [right-hand bracket]  
> [...] We shall call the tilde and the hook the _connectives_ of P.  
> We shall say that the symbol _p_ followed by one or more dashes is a _propositional symbol_ of P. [e.g. _p'_, _p''_, _p'''_, etc.]  
> 
> _Formulas (wffs) of P_
> 1. Any propositional symbol is a wff of P.
> 2. [...] If A is a wff of P, then ~A is a wff of P.
> 3. [...] If A and B are wffs of P, then (A⊃B) is a wff of P.
> 4. Nothing else is a wff of P.
> [In this description the letters 'A' and 'B' are metalinguistic variables.]

Loosely speaking, the tilde (~) expresses negation ("not A"), while the hook (⊃) expresses implication ("if A then B"). This formal language is augmented by some authors with two additional connectives, ⋀ to express logical conjunction (e.g. A⋀B "A and B"), and "⋁" to express logical disjunction (e.g. A⋁B "A or B".) The formal language handled in `PropWffParsing` adopts this latter practice, thus consisting of all strings which can be built up out of these eight symbols.

The module `MonParsComs` implements _monadic parser combinators_ as described in the paper [_Monadic Parser Combinators_](https://www.cs.nott.ac.uk/~pszgmh/monparsing.pdf), Graham Hutton & Erik Meijer. (Some adaptation from Gofer, a predecessor of Haskell, to the current Haskell standard was required.) Then, the module `PropWffParsing` uses monadic parsing in order to define a parser for wff's of truth-functional propositional logic (propositional logic, for short) written in the formal language described above.

The paper by Hutton & Meijer walks through the implementation of monadic parsing and its combinators in greater detail. One point worth highlighting here is the use (in current Haskell) of the ```MonadComprehensions``` language extension, which introduces a _monad comprehension_ syntax that is relatively transparent to those familiar with the ubiquitous _list comprehension._ Consider the following parser, which parses off a propositional symbol from a string or else fails:

```
many1 :: Parser a -> Parser [a]
many1 p = [ x:xs | x <- p, xs <- many p]

p_char :: Parser Char
p_char = char 'p'

tick :: Parser Char  
tick = char '\''

psym :: Parser (Wff String) 
psym = [ Sym $ p : xs | p  <- p_char 
                      , xs <- many1 tick ]
```

The parser for propositional symbols, ```psym```, is written so as to build up a list of all "stages" in the act of parsing, including partial parses.

```
*Main> :t runParser
runParser :: Parser a -> String -> [(a, String)]
*Main> let p2 = "p''"
*Main> let parse2 = runParser psym $ p2
*Main> parse2
[("p''",""),("p'","'")]
*Main> let p1f = "p'f"   
*Main> let p1f_parse = runParser psym $ p1f  
*Main> p1f_parse  
[("p'","f")]  
*Main> let f1 = "f'"  
*Main> let f_parse = runParser psym $ f1  
*Main> f_parse
[]
```

Meanwhile, the main parser, ```wfform```, can be observed parsing off any well-formed formula into a term of type ```Wff String```, where the propositional symbols are strings consisting of _p_ followed by one or more dashes. Note how the ```Show (Wff String)``` instance ends up with the individual propositional symbols surrounded by double quotes when the wff is printed:

```
*Main> let str1 = "(p'⋀((~p''⋁p')⊃~p'))" 
*Main> let str1_parse = runParser wfform $ str1
*Main> str1_parse
[(("p'"⋀((~"p''"⋁"p'")⊃~"p'")),"")]
*Main> let str1_wff = fst . head $ str1_parse
*Main> str1_wff
("p'"⋀((~"p''"⋁"p'")⊃~"p'"))
*Main> :t str1_wff
str1_wff :: Wff String 
```

## Truth tables

An _interpretation_ of the formal language P is an assignment to each propositional symbol of P of exactly one value, True or False (p. 57.) Thus, "[a] wff A is a _tautology of P_ iff A is true for every assignment of truth values to its propositional symbols when the connectives bear their usual truth-table meanings: i.e. iff A is true for every interpretation of P [...] Intuitively, a tautology is a formula that can be checked to be true for all interpretations by the usual (finite) truth-table method. Some logically valid formulas of [languages for predicate logic] cannot be so checked." (p. 60.) 

The truth-table method referred to above can be described as follows:

1. Identify all distinct propositional symbols used in forming the wff;
2. Work out all possible assignments of True or False to each propositional symbol. Each assignment will constitute one row of the truth table;
3. Then, use the truth-functional meaning of the connectives, under the standard interpretation given to them ("not", "if ... then ...", "and", "or"), to work out the assignment of True or False to the entire wff.

In the module `tests.hs`, helper functions are implemented for working out the truth table of a given wff, and for presenting it in an easily readable manner (in this example, propositional symbols are taken from the Roman alphabet, instead of being restricted to _p_ followed by one or more dashes):

```
f, g, h :: Wff Char
f = Sym 'f'
g = Sym 'g'
h = Sym 'h'

myWff :: Wff Char
myWff = Neg (Conj (Impl (Conj f g) f) (Disj h (Disj f g)))
```

Nevertheless, the data type `Wff t` implements the typeclass `Show` in a manner whereby the data constructors are converted into standard logical symbols, where appropriate:

```
*Main> myWff
~((('f'⋀'g')⊃'f')⋀('h'⋁('f'⋁'g')))
```

By applying `showTruthTable` to this wff, we can view its truth table worked out according to the above method:

```
*Main> showTruthTable myWff
'h'  'f'  'g'  ~((('f'⋀'g')⊃'f')⋀('h'⋁('f'⋁'g')))
---  ---  ---  ---
T    T    T    F
T    T    F    F
T    F    T    F
T    F    F    F
F    T    T    F
F    T    F    F
F    F    T    F
F    F    F    T
```

## Analytic tableaux

(The following summary is based on _First-Order Logic_, Raymond M. Smullyan.)

While wff's of propositional logic can be checked to see whether they are tautologies (always true; "trivial") using a straightforward truth-table method, such finitary methods are not always available, depending on the logic of interest (e.g. for predicate logics, whose propositions are quantified over variables e.g. "for all x, P(x)", such truth-table methods are not available.) For this reason, alternative methods for determining whether a wff of a given logical system is a tautology (true in every interpretation) or not are of general interest.

Smullyan describes "an extremely elegant and efficient proof procedure for propositional logic which we will subsequently extend to first order logic", the method of _analytic tableaux_ which is a variant of tableaux methods due to prior logicians, such as Beth, Hintikka, Anderson and Belnap (p. 15.) The method is based upon the following observations concerning ordinary propositional logic:

> 1) 
>    a) If ~X is true, then X is false.  
>    b) If ~X is false, then X is true.
> 2) 
>    a) If a conjunction X⋀Y is true, then X, Y are both true.  
>    b) If a conjunction X⋀Y is false, then either X is false or Y is false.
> 3) 
>    a) If a disjunction X⋁Y is true, then either X is true or Y is true.   
>    b) If a disjunction X⋁Y is false, then both X, Y are false.
> 4) 
>    a) If X⊃Y is true, then either X is false or Y is true.   
>    b) If X⊃Y is false, then X is true and Y is false.

From here, Smullyan proceeds to illustrate the method of tableaux on a specific formula, and then define it as a formal process (p. 16-17.) The formal process introduces the notion of a _signed well-formed formula (wff)_, which can be readily implemented as the Cartesian product of ```Bool``` and ```Wff t```. In this project, the module ```Tableaux.hs``` uses an alternative implementation using record syntax, so that accessors for the "sign" vs. "wff" parts of a signed formula can be leveraged:

```
data SignedWff t = Swff {
  bool :: Bool ,
  wff  :: (Wff t) 
  }
  deriving (Eq, Show)
```

In order to determine whether a given wff of propositional logic, ```v```, is a tautology, Smullyan's tableaux method offers the following alternative to working out a truth table: suppose that the wff is false (i.e. consider the signed wff ```Swff False v```), then "branch out" all alternatives, applying the tableaux rules repeatedly until the leaf-level nodes each consist _solely_ of "atomic propositions" i.e. signed propositional symbols. At this point, each leaf-level node can be easily checked to see whether it contains a contradiction (i.e. both ```Swff True (Sym x)``` and ```Swff False (Sym x)``` for any wff ```Sym x```.) ```isTauto``` stipulates that a wff of propositional logic is a tautology iff denying the wff invariably (i.e. in every possible alternative) results in a contradiction.

```
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
```

We can illustrate how one step of the overall process works, as follows. Consider the following formula:

```
*Main MonParsComs PropWffParsing Tableaux> let myWff = Conj (Sym 'a') (Impl (Neg $ Sym 'b') (Neg $ Sym 'a'))   
*Main MonParsComs PropWffParsing Tableaux> myWff
('a'⋀(~'b'⊃~'a'))  
```

To determine whether this formula is a tautology, we consider the signed wff which declares ```myWff``` to be ```False```, then expand that into all possible resulting alternatives, and examine these to see if any contains a contradiction. We first have to "package" the formula accordingly:

```
*Main MonParsComs PropWffParsing Tableaux> let false_myWff = Swff False myWff  
*Main MonParsComs PropWffParsing Tableaux> false_myWff  
F ('a'⋀(~'b'⊃~'a'))  
```

(I have defined a custom Show instance, ```instance Show t => Show (SignedWff t)```, in order to suppress the record syntax that would otherwise be printed.) 

```
*Main MonParsComs PropWffParsing Tableaux> let tree_false_myWff = Data.Tree.Node [false_myWff] []  
*Main MonParsComs PropWffParsing Tableaux> tree_false_myWff   
Node {rootLabel = [F ('a'⋀(~'b'⊃~'a'))], subForest = []}  
*Main MonParsComs PropWffParsing Tableaux> let myTab = Tableau tree_false_myWff  
*Main MonParsComs PropWffParsing Tableaux> myTab  
[F ('a'⋀(~'b'⊃~'a'))]
  
```

We are stating of a conjunction that it is false. According to rule 2b. above, "If a conjunction X⋀Y is false, then either X is false or Y is false." So there are two alternatives to be "broken out", as we work out the next stage of this tableau:

```
*Main MonParsComs PropWffParsing Tableaux> :t next_level
next_level
  :: Data.Tree.Tree [SignedWff t] -> Data.Tree.Tree [SignedWff t]  
*Main MonParsComs PropWffParsing Tableaux> let tree_false_myWff' = next_level tree_false_myWff  
*Main MonParsComs PropWffParsing Tableaux> let myTab' = Tableau tree_false_myWff'
*Main MonParsComs PropWffParsing Tableaux> myTab'
[F ('a'⋀(~'b'⊃~'a'))]
|
+- [F 'a']
|
`- [F (~'b'⊃~'a')]  

```

(Since ```Tree``` belongs to ```base```, a ```newtype``` is needed if I want to define an alternative ```show``` behavior besides the default for ```Tree```-based types, i.e. an alternative ```Show``` instance. This is the purpose of ```Tableau a```: to provide a type isomorphic to ```Tree [a]```, but whose terms are printed to the screen without displaying record syntax.)

Each alternative now gets its own "branch" of the tableau, and the same ```next_level``` step is carried out, as needed, on any leaf-level ```Swff```'s now present, until the tableau is complete. Here is the completed tableau for the wff ```('a'⋀(~'b'⊃~'a'))```:

```
*Main MonParsComs PropWffParsing Tableaux> let tree_false_myWff_f = expand tree_false_myWff  
*Main MonParsComs PropWffParsing Tableaux> let myTab_f = Tableau tree_false_myWff_f  
*Main MonParsComs PropWffParsing Tableaux> myTab_f  
[F ('a'⋀(~'b'⊃~'a'))]
|
+- [F 'a']
|
`- [F (~'b'⊃~'a')]
   |
   `- [T ~'b',F ~'a']
      |
      `- [F 'b',T 'a']  

```

Because the leaf-level nodes are each lists of signed "atomic" propositions, it is easy to examine each and see whether any contains a contradiction. Neither ```[F 'a']``` nor ```[F 'b',T 'a']``` contains an atomic proposition stated to be both true and false. So denying the original formula does _not_ unavoidably result in contradiction: in other words, the formula is _not_ a tautology of first-order propositional logic.

## Testing

([This tutorial on property testing with QuickCheck](https://www.cis.upenn.edu/~cis552/current/lectures/stub/QuickCheck.html) was frequently consulted in the course of preparing the tests discussed below.)

In order to verify that ```isTauto``` implements Smullyan's tableaux method correctly, it was necessary to confirm that ```isTauto v == True``` whenever the direct truth-table method applied to ```v``` finds that it is always true, but not otherwise. QuickCheck is leveraged in order to carry out this property test, which calls for the instance ```Arbitrary (Wff a)``` to be implemented (so that arbitrary wff's may be generated for the property test.) 

To accomplish this arbitrary generation, ```sized``` from the QuickCheck functionality is used, by calling it on a function, ```gen```, with an ```Int```-valued parameter. Roughly speaking, the purpose of ```gen``` is to "kick off" the construction of a ```v :: Wff a```: as the construction proceeds, every recursive call is more likely to conclude in a leaf-level propositional symbol, so that eventually a (finite) wff is generated in a non-deterministic manner.

```
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
```

During experimentation with different concrete types ```a``` and different choices of ```g :: Gen a```, it was found that as the number of terms inhabiting the type ```a``` (or the number of terms made available for ```g``` to select from) increased, the likelihood of an arbitrary wff being a tautology (as exhibited by the truth-table method) becomes vanishingly small. This resulted in property tests which took unsuitably long to complete. To get around this, an auxiliary data type was introduced so as to have, by construction, exactly 3 terms:

```
data X = X1 | X2 | X3 
 deriving (Eq, Show)

instance Arbitrary X where
 arbitrary = elements [X1, X2, X3]
```

With a smaller data type available to draw on for propositional symbols, the desired behavior could now be verified:

```
[...]
Property tests for 'isTauto'
+++ OK, passed 100 tests; 277 discarded.
  a well-formed formula true for every row of its truth table is a tautology
+++ OK, passed 100 tests; 25 discarded.
  a well-formed formula false for any row of its truth table is not a tautology

Finished in 31.8132 seconds
22 examples, 0 failures
```
