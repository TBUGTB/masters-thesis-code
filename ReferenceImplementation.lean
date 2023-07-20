import Matchings
import HoleTree

open HoleTree Tree

namespace SyntacticSimilarity

structure Computation (α : Type) where  
  generalizer : Tree α 
  distance : Nat 
deriving BEq

instance : Inhabited (Computation α) where 
  default := ⟨.metanode [], 0⟩ 

instance [ToString α] : ToString (Computation α) where 
  toString c := toString c.generalizer  ++ " | " ++ toString c.distance

instance : HAdd (Computation α) Nat (Computation α) where 
  hAdd c a := {c with distance := c.distance + a}

def distances (xs : List (Computation α)) : List Nat := 
  xs.map (fun x => x.distance)

def generalizers (xs : List (Computation α)) : List (Tree α) := 
  xs.map (fun x => x.generalizer)

def cumulativeDistance (xs : List (Computation α)) : Nat := 
  (distances xs).foldl (· + ·) 0 

/--
Returns the first entry of a list of computations whose distance value is minimal and its index. 
-/
def computationOfMinimalDistanceAndIdx : List (Computation α) → Computation α × Nat  
  | [x] => (x, 0)
  | x :: xs => if x.distance == 0 then -- skip tail calculation if x is optimal
                 (x, 0) 
               else 
                 let tail := computationOfMinimalDistanceAndIdx xs
                 if x.distance < tail.fst.distance then 
                   (x, 0) 
                 else 
                   (tail.fst, tail.snd + 1)
  | [] => dbg_trace "Cannot have minimizer of emtpy list"; default -- should never occur 

/--
Returns the first entry of a list of computations whose distance value is minimal. 
-/
def computationOfMinimalDistance (xs : List (Computation α)) : Computation α := 
  computationOfMinimalDistanceAndIdx xs |>.fst

/--
Returns the index of the first entry of the list whose distance value is minimal. 
-/
def idxOfComputationOfMinimalDistance (xs : List (Computation α)) : Nat := 
  computationOfMinimalDistanceAndIdx xs |>.snd

/--
Calculates syntactic generalizer and edit distance between the two given trees. The cost for deleting 
a tree is its size and creating a new meta node creates an additional cost of 1.
-/
partial def compute [BEq α] (tree1 : Tree α) (tree2 : Tree α) : Computation α := 
  
  let computeNodeList (t : Tree α) (xs : List (Tree α)) : Computation α := 
    if xs == [] then 
      ⟨metanode [], t.size + 1⟩ 
    else
      let computations := xs.map (fun x => compute t x)
      let (minimizer, minimizerIdx) := computationOfMinimalDistanceAndIdx computations
      let generalizer := metanode [minimizer.generalizer]
      let distance := minimizer.distance + size (xs.eraseIdx minimizerIdx) + 1
      ⟨generalizer, distance⟩

  let computeListList (xs : List (Tree α)) (ys : List (Tree α)) : Computation α := 
    let (shorter, longer) := shorterAndLonger xs ys
    let m := longer.length 

    let computations := shorter.map (fun a => longer.map (fun b => compute a b)) 
    
    let costMatrix := computations.map (fun as => as.map (fun b => b.distance))
    let (cost, matchingList) := minimalMatching costMatrix
    let IdxsOfChildrenNotInMatching := (List.range m).removeAll matchingList
    let matching := List.asFunction matchingList
    
    let costOfDeletingAnnotations := size (IdxsOfChildrenNotInMatching.map (fun i => longer[matching i]!))
    let distance := cost + costOfDeletingAnnotations
    let resultingChildren := computations.mapIdx (fun i x => x[matching i]!.generalizer)
    let generalizer := metanode resultingChildren 

    ⟨generalizer, distance⟩

  let computeNodesWithDifferentValue (lvalue : α) (ls : List (Tree α)) 
                                     (rvalue : α) (rs : List (Tree α)) : Computation α := 
    let leftInRight := computeNodeList (node lvalue ls) rs + 1
    let rightInLeft := computeNodeList (node rvalue rs) ls + 1
    let bothMetified := compute (metanode ls) (metanode rs) + 2
    computationOfMinimalDistance [leftInRight, rightInLeft, bothMetified]
    
  let result := match tree1, tree2 with
  | node v [], node w [] => if v==w then ⟨node v [], 0⟩ else ⟨metanode [], 2⟩
  | metanode xs, metanode [] 
  | metanode [], metanode xs => ⟨metanode [], size xs⟩ 
  | node v xs, node w ys => if v == w && xs.length == ys.length then 
                              let computations := List.zipWith compute xs ys
                              let distance := cumulativeDistance computations
                              let generalizer := node v (generalizers computations)
                              computationOfMinimalDistance [⟨generalizer, distance⟩, computeNodesWithDifferentValue v xs w ys]
                            else 
                              computeNodesWithDifferentValue v xs w ys
  | metanode xs, metanode ys => let matchNodes := computeListList xs ys
                                let matchLeftBelowRight := computeNodeList (metanode xs) ys
                                let matchRightBelowLeft := computeNodeList (metanode xs) ys
                                computationOfMinimalDistance [matchNodes, matchLeftBelowRight, matchRightBelowLeft]
  | node v xs, metanode ys 
  | metanode ys, node v xs => let convertNode := compute (metanode xs) (metanode ys) + 1
                              let insertAboveNode := computeNodeList (node v xs) ys + 1
                              let metanodeMappedToRoot := computeNodeList (node v xs) ys
                              computationOfMinimalDistance [metanodeMappedToRoot, convertNode, insertAboveNode] 

  result