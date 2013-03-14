{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}

module Verifier.SAW.TermNet
  ( PatternShape(..)
  , Pattern(..)
  , Key
  , key_of_term  -- :: Term t => t -> [Key]
  , Net          -- :: * -> *
  , empty        -- :: Net a
  , insert       -- :: Eq a => ([Key], a) -> Net a -> Net a
  , insert_term  -- :: (Term t, Eq a) => (t, a) -> Net a -> Net a
  , delete       -- :: Eq a => ([Key], a) -> Net a -> Net a
  , delete_term  -- :: (Term t, Eq a) => (t, a) -> Net a -> Net a
  , lookup       -- :: Net a -> [Key] -> [a]
  , match_term   -- :: Term t => Net a -> t -> [a]
  , unify_term   -- :: Term t => Net a -> t -> [a]
  , merge        -- :: Eq a => Net a -> Net a -> Net a
  , content      -- :: Net a -> [a]
  ) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.List as List
import Prelude hiding (lookup)

{-
Based on Pure/net.ML from Isabelle 2012.
Ported from Standard ML to Haskell by Brian Huffman.

    Title:      Pure/net.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Discrimination nets: a data structure for indexing items

From the book
    E. Charniak, C. K. Riesbeck, D. V. McDermott.
    Artificial Intelligence Programming.
    (Lawrence Erlbaum Associates, 1980).  [Chapter 14]

match_term no longer treats abstractions as wildcards; instead they match
only wildcards in patterns.  Requires operands to be beta-eta-normal.
-}

data PatternShape t = Atom String | Var | App t t

class Pattern t where
  patternShape :: t -> PatternShape t

isVarApp :: Pattern t => t -> Bool
isVarApp t = case patternShape t of
  Atom _   -> False
  Var      -> True
  App t' _ -> isVarApp t'

-- Start

data Key = CombK | VarK | AtomK String

{-Keys are preorder lists of symbols -- Combinations, Vars, Atoms.
  Any term whose head is a Var is regarded entirely as a Var.
  Abstractions are also regarded as Vars;  this covers eta-conversion
    and "near" eta-conversions such as %x.?P(?f(x)).
-}

add_key_of_terms :: Pattern t => t -> [Key] -> [Key]
add_key_of_terms t cs
  | isVarApp t = VarK : cs
  | otherwise  = rands (patternShape t) cs
  where
    rands (App f t) cs = CombK : rands (patternShape f) (add_key_of_terms t cs)
    rands (Atom c)  cs = AtomK c : cs

{-convert a term to a list of keys-}
key_of_term :: Pattern t => t -> [Key]
key_of_term t = add_key_of_terms t []

{-Trees indexed by key lists: each arc is labelled by a key.
  Each node contains a list of items, and arcs to children.
  The empty key addresses the entire net.
  Lookup functions preserve order in items stored at same level.
-}

data Net a
  = Leaf [a]
  | Net { comb :: Net a, var :: Net a, atoms :: Map String (Net a) }
  deriving Show

empty :: Net a
empty = Leaf []

is_empty :: Net a -> Bool
is_empty (Leaf []) = True
is_empty _ = False

emptynet :: Net a
emptynet = Net { comb = empty, var = empty, atoms = Map.empty }

{-** Insertion into a discrimination net **-}

{-Adds item x to the list at the node addressed by the keys.
  Creates node if not already present.
  The empty list of keys generates a Leaf node, others a Net node.
-}
insert :: forall a. (Eq a) => ([Key], a) -> Net a -> Net a
insert (keys, x) net = ins1 keys net
  where
    ins1 :: [Key] -> Net a -> Net a
    ins1 [] (Leaf xs)
      | x `elem` xs = Leaf xs
      | otherwise   = Leaf (x : xs)
    ins1 keys (Leaf []) = ins1 keys emptynet
    ins1 (CombK : keys) (Net {comb, var, atoms}) =
      Net {comb = ins1 keys comb, var = var, atoms = atoms}
    ins1 (VarK : keys) (Net {comb, var, atoms}) =
      Net {comb = comb, var = ins1 keys var, atoms = atoms}
    ins1 (AtomK a : keys) (Net {comb, var, atoms}) =
      let atoms' = Map.alter (Just . ins1 keys . fromMaybe empty) a atoms
      in Net {comb = comb, var = var, atoms = atoms'}

insert_term :: (Pattern t, Eq a) => (t, a) -> Net a -> Net a
insert_term (t, x) = insert (key_of_term t, x)

{-** Deletion from a discrimination net **-}

{-Create a new Net node if it would be nonempty-}
newnet :: Net a -> Net a
newnet (args @ Net {comb, var, atoms}) =
  if is_empty comb && is_empty var && Map.null atoms
  then empty else args

{-Deletes item x from the list at the node addressed by the keys.
  Returns Nothing if absent.  Collapses the net if possible. -}
delete :: (Eq a) => ([Key], a) -> Net a -> Net a
delete (keys, x) net = del1 keys net
  where
    del1 [] (Leaf xs) = Leaf (List.delete x xs)
    del1 keys (Leaf []) = Leaf []
    del1 (CombK : keys) (Net {comb, var, atoms}) =
      newnet $ Net {comb = del1 keys comb, var = var, atoms = atoms}
    del1 (VarK : keys) (Net {comb, var, atoms}) =
      newnet $ Net {comb = comb, var = del1 keys var, atoms = atoms}
    del1 (AtomK a : keys) (Net {comb, var, atoms}) =
      let nonempty (Leaf []) = Nothing
          nonempty net = Just net
          atoms' = Map.update (nonempty . del1 keys) a atoms
      in newnet $ Net {comb = comb, var = var, atoms = atoms'}

delete_term :: (Pattern t, Eq a) => (t, a) -> Net a -> Net a
delete_term (t, x) = delete (key_of_term t, x)

{-** Retrieval functions for discrimination nets **-}

{-Return the list of items at the given node, [] if no such node-}
lookup :: Net a -> [Key] -> [a]
lookup (Leaf xs) [] = xs
lookup (Leaf _) (_ : _) = []  {-non-empty keys and empty net-}
lookup (Net {comb, var, atoms}) (CombK : keys) = lookup comb keys
lookup (Net {comb, var, atoms}) (VarK : keys) = lookup var keys
lookup (Net {comb, var, atoms}) (AtomK a : keys) =
  case Map.lookup a atoms of
    Just net -> lookup net keys
    Nothing -> []

{-Skipping a term in a net.  Recursively skip 2 levels if a combination-}
net_skip :: Net a -> [Net a] -> [Net a]
net_skip (Leaf _) nets = nets
net_skip (Net {comb, var, atoms}) nets =
  foldr net_skip (Map.fold (:) (var : nets) atoms) (net_skip comb [])

{-* Matching and Unification *-}

{-conses the linked net, if present, to nets-}
look1 :: (Map String (Net a), String) -> [Net a] -> [Net a]
look1 (atoms, a) nets =
  case Map.lookup a atoms of
    Just net -> net : nets
    Nothing -> nets

{-Return the nodes accessible from the term (cons them before nets)
  "unif" signifies retrieval for unification rather than matching.
  Var in net matches any term.
  Abs or Var in object: if "unif", regarded as wildcard,
                                   else matches only a variable in net.
-}
matching :: Pattern t => Bool -> t -> Net a -> [Net a] -> [Net a]
matching unif t net nets =
  case net of
    Leaf _ -> nets
    Net {var, ..} ->
      case patternShape t of
        Var -> if unif then net_skip net nets else var : nets {-only matches Var in net-}
        _   -> rands t net (var : nets)  {-var could match also-}
  where
    rands _ (Leaf _) nets = nets
    rands t (Net {comb, atoms, ..}) nets =
      case patternShape t of
        Atom c    -> look1 (atoms, c) nets
        Var       -> nets
        App t1 t2 -> foldr (matching unif t2) nets (rands t1 comb [])

extract_leaves :: [Net a] -> [a]
extract_leaves = concatMap (\(Leaf xs) -> xs)

{-return items whose key could match t, WHICH MUST BE BETA-ETA NORMAL-}
match_term :: Pattern t => Net a -> t -> [a]
match_term net t = extract_leaves (matching False t net [])

{-return items whose key could unify with t-}
unify_term :: Pattern t => Net a -> t -> [a]
unify_term net t = extract_leaves (matching True t net [])

{--------------------------------------------------------------------

{-* operations on nets *-}

{-subtraction: collect entries of second net that are NOT present in first net-}
fun subtract eq net1 net2 =
  let
    fun subtr (Net _) (Leaf ys) = append ys
      | subtr (Leaf xs) (Leaf ys) =
          fold_rev (fn y => if member eq xs y then I else cons y) ys
      | subtr (Leaf _) (net as Net _) = subtr emptynet net
      | subtr (Net {comb = comb1, var = var1, atoms = atoms1})
            (Net {comb = comb2, var = var2, atoms = atoms2}) =
          subtr comb1 comb2
          #> subtr var1 var2
          #> Symtab.fold (fn (a, net) =>
            subtr (the_default emptynet (Symtab.lookup atoms1 a)) net) atoms2
  in subtr net1 net2 [] end;

fun entries net = subtract (K false) empty net;

--------------------------------------------------------------------------------}

{- merge -}

cons_fst :: a -> ([a], b) -> ([a], b)
cons_fst x (xs, y) = (x : xs, y)

dest :: Net a -> [([Key], a)]
dest (Leaf xs) = map ((,) []) xs
dest (Net {comb, var, atoms}) =
  map (cons_fst CombK) (dest comb) ++
  map (cons_fst VarK) (dest var) ++
  concatMap (\(a, net) -> map (cons_fst (AtomK a)) (dest net)) (Map.assocs atoms)

merge :: Eq a => Net a -> Net a -> Net a
merge net1 net2 = foldl (flip insert) net1 (dest net2)

content :: Net a -> [a]
content (Leaf xs) = xs
content (Net {comb, var, atoms}) =
  content comb ++
  content var ++
  concatMap content (Map.elems atoms)
