import Matchings
import HoleTree

open HoleTree Tree

namespace SyntacticSimilarity

structure Similarity (α : Type u) where  
  generalizer : Tree α 
  distance : Nat 
deriving BEq

instance : Inhabited (Similarity α) where 
  default := ⟨.metanode [], 0⟩ 

instance [ToString α] : ToString (Similarity α) where 
  toString c := toString c.generalizer  ++ " | " ++ toString c.distance

instance : HAdd (Similarity α) Nat (Similarity α) where 
  hAdd c a := {c with distance := c.distance + a}

def distances (xs : List (Similarity α)) : List Nat := 
  xs.map (fun x => x.distance)

def generalizers (xs : List (Similarity α)) : List (Tree α) := 
  xs.map (fun x => x.generalizer)

def cumulativeDistance (xs : List (Similarity α)) : Nat := 
  (distances xs).foldl (· + ·) 0 

/--
Returns the first entry of a list of syntactic similarities whose distance value is minimal and its index. 
-/
def minimalDistanceSimilarityAndIdx : List (Similarity α) → Similarity α × Nat  
  | [x] => (x, 0)
  | x :: xs => if x.distance == 0 then -- skip tail calculation if x is optimal
                 (x, 0) 
               else 
                 let (tailMinimalDistanceSimilarity, idx) := minimalDistanceSimilarityAndIdx xs
                 if x.distance < tailMinimalDistanceSimilarity.distance then 
                   (x, 0) 
                 else 
                   (tailMinimalDistanceSimilarity, idx + 1)
  | [] => panic! "Cannot find the minimal distance syntactic similarity in empty list" 

def minimalDistanceSimilarity (xs : List (Similarity α)) : Similarity α := 
  minimalDistanceSimilarityAndIdx xs |>.fst

partial def compute [ToString α] [BEq α] (tree1 : Tree α) (tree2 : Tree α) : Similarity α := 
  
  let matchBelowOneOf (t : Tree α) (xs : List (Tree α)) : Similarity α := 
    if xs == [] then 
      ⟨metanode [], t.numberOfNodes⟩ 
    else
      let pairwiseSimilarity := xs.map (fun x => compute t x)
      let (minimizer, minimizerIdx) := minimalDistanceSimilarityAndIdx pairwiseSimilarity
      let generalizer := metanode [minimizer.generalizer]
      let distance := minimizer.distance + numberOfNodes (xs.eraseIdx minimizerIdx) + 1
      ⟨generalizer, distance⟩
    
  let nodesMatchAtOrdinaryNodeRoot (label : α) (children1 : List (Tree α)) (children2 : List (Tree α)) 
    : Similarity α := 
    let pairwiseSimilarities := List.zipWith compute children1 children2
    let distance := cumulativeDistance pairwiseSimilarities
    let generalizer := node label (generalizers pairwiseSimilarities)
    ⟨generalizer, distance⟩ 

  let nodesDontMatch (label1 : α) (children1 : List (Tree α)) 
                     (label2 : α) (children2 : List (Tree α)) : Similarity α :=
    let firstMatchesInChildNodeOfSecond := matchBelowOneOf (node label1 children1) children2 + 1
    let secondMatchesInChildNodeOfFirst := matchBelowOneOf (node label2 children2) children1 + 1
    minimalDistanceSimilarity [firstMatchesInChildNodeOfSecond, secondMatchesInChildNodeOfFirst]

  let nodesMatchAtMetaNodeRoot (children1 : List (Tree α)) (children2 : List (Tree α)) : Similarity α := 
    compute (metanode children1) (metanode children2) + 2

  let similarityOfNodesWithDifferentLabels (label1 : α) (children1 : List (Tree α)) 
                                           (label2 : α) (children2 : List (Tree α)) : Similarity α :=
    let case1 := nodesMatchAtMetaNodeRoot children1 children2
    let case2 := nodesDontMatch label1 children1 label2 children2
    minimalDistanceSimilarity [case1, case2]

  let similarityOfNodesWithIdenticalLabels (label : α) (children1 : List (Tree α)) (children2 : List (Tree α)) : Similarity α :=
    let case1a := nodesMatchAtOrdinaryNodeRoot label children1 children2
    let case1b := nodesMatchAtMetaNodeRoot children1 children2
    let case2 := nodesDontMatch label children1 label children2
    minimalDistanceSimilarity [case1a, case1b, case2]

  let metaNodesMatchAtRoot (annotations1 : List (Tree α)) (annotations2 : List (Tree α)) : Similarity α := 
    let (shorter, longer) := shorterAndLonger annotations1 annotations2
    let m := longer.length 

    let similarities := shorter.map (fun a => longer.map (fun b => compute a b))
    
    let costMatrix := similarities.map (fun as => as.map (fun b => b.distance))
    let (cost, matchingList) := minimalMatching costMatrix
    let IdxsOfAnnotationsNotInMatching := (List.range m).removeAll matchingList
    let matching := List.asFunction matchingList
    
    let costOfDeletingAnnotations := numberOfNodes (IdxsOfAnnotationsNotInMatching.map (fun i => longer[matching i]!))
    let distance := cost + costOfDeletingAnnotations
    let resultingAnnotations := similarities.mapIdx (fun i x => x[matching i]!.generalizer)
    let generalizer := metanode resultingAnnotations 

    ⟨generalizer, distance⟩

  let metaNodesDontMatch (annotations1 : List (Tree α)) (annotations2 : List (Tree α)) : Similarity α :=
    let firstMatchesInAnnotationOfSecond := matchBelowOneOf (metanode annotations1) annotations2
    let secondMatchesInAnnotationOfFirst := matchBelowOneOf (metanode annotations2) annotations1
    minimalDistanceSimilarity [firstMatchesInAnnotationOfSecond, secondMatchesInAnnotationOfFirst]

  match tree1, tree2 with
  | node v [], node w [] => if v==w then 
                              ⟨node v [], 0⟩ 
                            else 
                              ⟨metanode [], 2⟩

  | metanode xs, metanode [] 
  | metanode [], metanode xs => let generalizer := metanode []
                                let distance := numberOfNodes xs
                                ⟨generalizer, distance⟩ 
  
  | node v xs, node w ys => if v == w && xs.length == ys.length then 
                              similarityOfNodesWithIdenticalLabels v xs ys
                            else 
                              similarityOfNodesWithDifferentLabels v xs w ys
  
  | metanode xs, metanode ys => let case1 := metaNodesMatchAtRoot xs ys
                                let case2 := metaNodesDontMatch xs ys
                                minimalDistanceSimilarity [case1, case2]
  
  | node v xs, metanode ys 
  | metanode ys, node v xs => let matchAtRoot := compute (metanode xs) (metanode ys) + 1
                              let onlyNodeMappedToRoot := matchBelowOneOf (metanode ys) xs + 1
                              let onlyMetanodeMappedToRoot := matchBelowOneOf (node v xs) ys
                              minimalDistanceSimilarity [matchAtRoot, onlyNodeMappedToRoot, 
                                                         onlyMetanodeMappedToRoot]