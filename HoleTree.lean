import Util
import Mathlib.Data.List.Sort 

namespace HoleTree

inductive Tree (α : Type u) := 
  | node (label : α) (children : List (Tree α)) : Tree α
  | metanode (annotations : List (Tree α)) : Tree α
deriving BEq

instance : Inhabited (Tree α) where 
  default := .metanode []

partial def treeListToString [ToString α] (treeList : List (Tree α)) : String :=  
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

def Tree.numberOfNodes : Tree α → Nat 
  | node _ [] 
  | metanode [] => 1 
  | node v (x::xs) => x.numberOfNodes + (node v xs).numberOfNodes
  | metanode (x::xs) => x.numberOfNodes + (metanode xs).numberOfNodes   

#eval (.node "+" [.leaf "a", .leaf "b"] : Tree String).numberOfNodes == 3

def numberOfNodes : List (Tree α) → Nat 
  | [] => 0
  | x::xs => x.numberOfNodes + numberOfNodes xs

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
partial def treeListToTikzForest [ToString α] (treeList : List (Tree α)) : String :=  
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

partial def treeListHash [Hashable α] : List (Tree α) → UInt64 
  | [] => hash 0
  | .node v vs :: xs => let tailHash := treeListHash xs
                        let childHash := treeListHash vs  
                        mixHash (mixHash (hash v) (childHash)) tailHash
  | .metanode as :: xs => let tailHash := treeListHash xs
                        let metaNodeHashes := as.map (fun y => treeListHash [y])
                        let sortedHashes := metaNodeHashes.mergeSort (fun x y => x < y)
                        let metaNodeHash := sortedHashes.foldl mixHash (hash 0)
                        mixHash metaNodeHash tailHash

instance [Hashable α] : Hashable (Tree α) where 
  hash tree := treeListHash [tree]