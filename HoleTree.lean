import Util

namespace HoleTree

/--
A tree datatype that represent syntax trees including annotated holes. A hole is called meta-node and its 
annotations are given through a List. Trees whose meta-nodes share the same annotations up to permutation
of the list should be considered as equivalent. 
-/
inductive Tree (α : Type) := 
  | node (value : α) (children : List (Tree α)) : Tree α
  | metanode (annotations : List (Tree α)) : Tree α
deriving BEq

instance : Inhabited (Tree α) where 
  default := .metanode []

def treeListToString [ToString α] (treeList : List (Tree α)) : String :=  
  let rec treeToString : Tree α → String
      | .node v [] => toString v
      | .node v c => toString v ++ " [" ++ treeListToString c ++ "]"
      | .metanode c => "{" ++ treeListToString c ++ "}"
  match treeList with
  | [] => ""
  | [x] => treeToString x 
  | x :: xs => (treeToString x) ++ ", " ++ treeListToString xs

instance [ToString α] : ToString (Tree α) where 
  toString t := treeListToString [t]

def Tree.leaf (value : α) : Tree α := Tree.node value []

def Tree.size : Tree α → Nat 
  | node _ [] 
  | metanode [] => 1 
  | node v (x::xs) => x.size + (node v xs).size
  | metanode (x::xs) => x.size + (metanode xs).size   

#eval (.node "+" [.leaf "a", .leaf "b"] : Tree String).size == 3

def size : List (Tree α) → Nat 
  | [] => 0
  | x::xs => x.size + size xs

/-- 
Returns true if all annotations of the first tree can be permuted such that 
it becomes equal to the second tree.
-/
def Tree.equivalentTo [BEq α]: Tree α → Tree α → Bool
  | node v [], node w [] => if v==w then true else false 
  | node v (x::xs), node w (y::ys) => 
    if x==y then (node v xs).equivalentTo (node w ys) 
            else false 
  | metanode xs, metanode ys => List.equalUpToPermutation xs ys
  | _, _ => false

#eval (.metanode [.leaf "a", .leaf "b"] : Tree String).equivalentTo 
      (.metanode [.leaf "b", .leaf "a"])

def countMakemetanodeChildrenListMembers : List (Tree α) → List (Tree α) × Nat
  | [] => ([], 0)
  | (.node v xs) :: ts =>   let tail := countMakemetanodeChildrenListMembers ts
                            (.node v xs :: tail.fst, tail.snd) 
  | (.metanode xs) :: ts => let tail := countMakemetanodeChildrenListMembers ts
                            (xs ++ tail.fst, 1 + tail.snd)

/--
For all trees in the list, finds any occurences where a meta-node `m1` has a child node `m2` which is of type 
meta node and then replaces `m2` with its children. This is done recursively, so that no more occurences of 
iterated meta-nodes exist in the result. 
-/
def countCollapseMetanodesList : List (Tree α) → List (Tree α) × Nat
  | [] => ([], 0)
  | (.node x xs) :: ts => let tail := countCollapseMetanodesList ts
                          let children := countCollapseMetanodesList xs
                          (.node x children.fst :: tail.fst, children.snd + tail.snd)
  | (.metanode xs) :: ts => let tail := countCollapseMetanodesList ts
                            let children := countCollapseMetanodesList xs
                            let childrenWithMetaAtHeadRemoved := countMakemetanodeChildrenListMembers children.fst
                            (.metanode childrenWithMetaAtHeadRemoved.fst :: ts, 
                            tail.snd + children.snd + childrenWithMetaAtHeadRemoved.snd)

/--
Finds any occurences where a meta-node `m1` has a child node `m2` which is of type meta node and then
replaces `m2` with its children. This is done recursively, so that no more occurences of iterated meta-nodes
exist in the result. The returned `Nat` is the number of deleted meta-nodes. 
-/
def Tree.countCollapseMetanodes (t : Tree α) : Tree α × Nat := 
  let result := countCollapseMetanodesList [t]
  (result.fst[0]!, result.snd)

#eval (.metanode [.leaf "a", .metanode [.leaf "b"]] : Tree String).countCollapseMetanodes

#eval (.node "+" [.leaf "a", .metanode [.metanode [.leaf "b"]]] : Tree String).countCollapseMetanodes

#eval (.node "+" [.leaf "a", .metanode [.metanode [.metanode [.leaf "b"]]]] : Tree String).countCollapseMetanodes

#eval (.node "+" [.leaf "a", .metanode [.metanode [.node "-" [.metanode [.leaf "b"]]]]] 
      : Tree String).countCollapseMetanodes

#eval (.metanode [.leaf "a", .metanode [.leaf "b"], .metanode [.leaf "c"]] : Tree String).countCollapseMetanodes

/--
Returns a string that can be used to render the given trees with the tikz forest package. 
-/
def treeListToTikzForest [ToString α] (treeList : List (Tree α)) : String :=  
  let rec treeToTikzForest : Tree α → String
      | .node v [] => "[" ++ toString v ++ "]"
      | .node v c => "[" ++ toString v ++ treeListToTikzForest c ++ "]"
      | .metanode c => "[M,for children=forked edge" ++ treeListToTikzForest c ++ "]"
  match treeList with
  | [] => ""
  | [x] => treeToTikzForest x 
  | x :: xs => (treeToTikzForest x) ++ treeListToTikzForest xs

/--
Returns a string that can be used to render the given tree with the tikz forest package. 
-/
def Tree.toTikzForest [ToString α] (tree: Tree α) : String := 
  treeListToTikzForest [tree]