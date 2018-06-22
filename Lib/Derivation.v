Require Import List String.
Require Import Grammar ParseTree.
Import ListNotations.

Inductive derivesTree {g : grammar} : 
  symbol -> list string -> tree -> Prop :=
| derivesT : 
    forall (y : string),
      derivesTree (T y) [y] (Leaf y)
| derivesNT : 
    forall (x : string) 
           (gamma : list symbol) 
           (tokens : list string) 
           (subtrees : list tree),
      In (x, gamma) g.(productions)
      -> derivesForest gamma tokens subtrees
      -> derivesTree (NT x) tokens (Node x subtrees)
with derivesForest {g : grammar} : 
       list symbol -> list string -> list tree -> Prop :=
     | derivesNil : derivesForest [] [] []
     | derivesCons : 
         forall (hdRoot : symbol)
                (prefix suffix : list string)
                (hdTree : tree)
                (tlRoots : list symbol)
                (tlTrees : list tree),
           derivesTree hdRoot prefix hdTree
           -> derivesForest tlRoots suffix tlTrees
           -> derivesForest (hdRoot :: tlRoots) 
                            (prefix ++ suffix) 
                            (hdTree :: tlTrees).

Scheme derivesTree_mutual_ind :=
  Minimality for derivesTree Sort Prop
  with derivesForest_mutual_ind :=
    Minimality for derivesForest Sort Prop.

