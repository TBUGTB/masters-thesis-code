import Matchings
import HoleTree

open HoleTree Tree

namespace SyntacticSimilarity

structure SyntacticSimilarity (α : Type u) where  
  generalizer : Tree α 
  distance : Nat 
deriving BEq

instance : Inhabited (SyntacticSimilarity α) where 
  default := ⟨.metanode [], 0⟩ 

instance [ToString α] : ToString (SyntacticSimilarity α) where 
  toString c := toString c.generalizer  ++ " | " ++ toString c.distance

instance : HAdd (SyntacticSimilarity α) Nat (SyntacticSimilarity α) where 
  hAdd c a := {c with distance := c.distance + a}

def distances (xs : List (SyntacticSimilarity α)) : List Nat := 
  xs.map (fun x => x.distance)

def generalizers (xs : List (SyntacticSimilarity α)) : List (Tree α) := 
  xs.map (fun x => x.generalizer)

def cumulativeDistance (xs : List (SyntacticSimilarity α)) : Nat := 
  (distances xs).foldl (· + ·) 0 

/--
Returns the first entry of a list of syntactic similarities whose distance value is minimal and its index. 
-/
def minimalDistanceSyntacticSimilarityAndIdx : List (SyntacticSimilarity α) → SyntacticSimilarity α × Nat  
  | [x] => (x, 0)
  | x :: xs => if x.distance == 0 then -- skip tail calculation if x is optimal
                 (x, 0) 
               else 
                 let (tailMinimalDistanceSyntacticSimilarity, idx) := minimalDistanceSyntacticSimilarityAndIdx xs
                 if x.distance < tailMinimalDistanceSyntacticSimilarity.distance then 
                   (x, 0) 
                 else 
                   (tailMinimalDistanceSyntacticSimilarity, idx + 1)
  | [] => panic! default -- should never occur 

def minimalDistanceSyntacticSimilarity (xs : List (SyntacticSimilarity α)) : SyntacticSimilarity α := 
  minimalDistanceSyntacticSimilarityAndIdx xs |>.fst

partial def compute [BEq α] (tree1 : Tree α) (tree2 : Tree α) : SyntacticSimilarity α := 
  
  let computeNodeList (t : Tree α) (xs : List (Tree α)) : SyntacticSimilarity α := 
    if xs == [] then 
      ⟨metanode [], t.numberOfNodes⟩ 
    else
      let computations := xs.map (fun x => compute t x)
      let (minimizer, minimizerIdx) := minimalDistanceSyntacticSimilarityAndIdx computations
      let generalizer := metanode [minimizer.generalizer]
      let distance := minimizer.distance + numberOfNodes (xs.eraseIdx minimizerIdx) + 1
      ⟨generalizer, distance⟩

  let computeListList (xs : List (Tree α)) (ys : List (Tree α)) : SyntacticSimilarity α := 
    let (shorter, longer) := shorterAndLonger xs ys
    let m := longer.length 

    let computations := shorter.map (fun a => longer.map (fun b => compute a b)) 
    
    let costMatrix := computations.map (fun as => as.map (fun b => b.distance))
    let (cost, matchingList) := minimalMatching costMatrix
    let IdxsOfChildrenNotInMatching := (List.range m).removeAll matchingList
    let matching := List.asFunction matchingList
    
    let costOfDeletingAnnotations := numberOfNodes (IdxsOfChildrenNotInMatching.map (fun i => longer[matching i]!))
    let distance := cost + costOfDeletingAnnotations
    let resultingChildren := computations.mapIdx (fun i x => x[matching i]!.generalizer)
    let generalizer := metanode resultingChildren 

    ⟨generalizer, distance⟩

  let computeNodesWithDifferentValue (lvalue : α) (ls : List (Tree α)) 
                                     (rvalue : α) (rs : List (Tree α)) : SyntacticSimilarity α := 
    let leftInRight := computeNodeList (node lvalue ls) rs + 1
    let rightInLeft := computeNodeList (node rvalue rs) ls + 1
    let bothMetified := compute (metanode ls) (metanode rs) + 2
    minimalDistanceSyntacticSimilarity [leftInRight, rightInLeft, bothMetified]
    
  let result := match tree1, tree2 with
  | node v [], node w [] => if v==w then ⟨node v [], 0⟩ else ⟨metanode [], 2⟩
  | metanode xs, metanode [] 
  | metanode [], metanode xs => ⟨metanode [], numberOfNodes xs⟩ 
  | node v xs, node w ys => if v == w && xs.length == ys.length then 
                              let computations := List.zipWith compute xs ys
                              let distance := cumulativeDistance computations
                              let generalizer := node v (generalizers computations)
                              minimalDistanceSyntacticSimilarity [⟨generalizer, distance⟩, computeNodesWithDifferentValue v xs w ys]
                            else 
                              computeNodesWithDifferentValue v xs w ys
  | metanode xs, metanode ys => let matchNodes := computeListList xs ys
                                let matchLeftBelowRight := computeNodeList (metanode xs) ys
                                let matchRightBelowLeft := computeNodeList (metanode xs) ys
                                minimalDistanceSyntacticSimilarity [matchNodes, matchLeftBelowRight, matchRightBelowLeft]
  | node v xs, metanode ys 
  | metanode ys, node v xs => let convertNode := compute (metanode xs) (metanode ys) + 1
                              let insertAboveNode := computeNodeList (node v xs) ys + 1
                              let metanodeMappedToRoot := computeNodeList (node v xs) ys
                              minimalDistanceSyntacticSimilarity [metanodeMappedToRoot, convertNode, insertAboveNode] 

  result