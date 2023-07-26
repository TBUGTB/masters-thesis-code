import IncompleteMatchings
import HoleTree 
import NaiveCache
import Mathlib.Order.WithBot

open HoleTree Tree

namespace SyntacticSimilarity

structure Similarity (α : Type u) where  
  generalizer : Tree α 
  distance : Nat 
deriving BEq

instance : Inhabited (Similarity α) where 
  default := ⟨metanode [], 0⟩ 

instance [ToString α] : ToString (Similarity α) where 
  toString c := toString c.generalizer  ++ " | " ++ toString c.distance

instance : HAdd (Option (Similarity α)) Nat (Option (Similarity α)) where 
  hAdd c a := match c with 
    | none => none 
    | some c => some {c with distance := c.distance + a}

def distances (xs : List (Similarity α)) : List Nat := 
  xs.map (fun x => x.distance)

def distance? : Option (Similarity α) → Option Nat  
  | none => none
  | some c => c.distance

def generalizers (xs : List (Similarity α)) : List (Tree α) := 
  xs.map (fun x => x.generalizer)

def cumulativeDistance (xs : List (Similarity α)) : Nat := 
  (distances xs).foldl (· + ·) 0 

def minimalDistanceSimilarityAndIdx? : List (Option (Similarity α)) → Option (Similarity α × Nat)  
  | x :: xs => let tail := minimalDistanceSimilarityAndIdx? xs
               match x, tail with 
               | some v, none => (v, 0)
               | none, some (c, i) => (c, i + 1)
               | none, none => none
               | some x, some (c, i) => 
                  if x.distance < c.distance then 
                    (x, 0) 
                  else 
                    (c, i + 1)
  | [] => none

def minimalDistanceSimilarity? (xs : List (Option (Similarity α))) : Option (Similarity α) := 
  match minimalDistanceSimilarityAndIdx? xs with 
  | none => none
  | some (c, _) => c

structure Configuration where 
  collapseMetanodes : Bool := true 
  maximumDistance : WithTop Nat := ⊤
deriving Repr, BEq, Inhabited 

abbrev SimilarityCache (α : Type u) := Cache (Tree α × Tree α) (Similarity α)

instance [ToString α] : ToString (SimilarityCache α) where 
  toString c := toString c.cache

abbrev SimilarityStateM (α : Type u) := StateM (SimilarityCache α)

abbrev ComputationM (α β : Type) := (ReaderT Configuration (SimilarityStateM α)) β

instance : HSub (WithTop Nat) Nat (Option Nat) where 
  hSub x y := match x with 
              | none => none 
              | some x => x - y

def Configuration.reduceMaximumDistanceBy (c : Configuration) (n : Nat) := 
  {c with maximumDistance := c.maximumDistance - n}

def withAddToDistanceAfterCalculation (n : Nat) (x : ComputationM α (Option (Similarity β))) : 
  ComputationM α (Option (Similarity β)) := 
  withReader (fun configuration => configuration.reduceMaximumDistanceBy n) do 
    x
  >>= fun x => pure (x + n)

def Similarity.distanceDoesNotExceedMaximum (c : Similarity α) : ComputationM α Bool := do 
  let maximumDistance := (← read).maximumDistance
  pure $ c.distance <= maximumDistance

def saveUnderKeyAndReturnIfValid [BEq α] [ToString α] (key : Tree α × Tree α) (similarity : Similarity α) : 
  ComputationM α (Option (Similarity α)) := do
  if (← similarity.distanceDoesNotExceedMaximum) then 
    saveToCache key similarity
    pure (some similarity) 
  else 
    pure none 

partial def computeWithCache [BEq α] [ToString α] (tree1 : Tree α) (tree2 : Tree α) : 
  ComputationM α (Option (Similarity α)) := do

  let saveAndReturnIfValid (c : Similarity α) : ComputationM α (Option (Similarity α)) := 
    saveUnderKeyAndReturnIfValid (tree1, tree2) c

  let saveAndReturnMinimalDistanceSimilarity 
    (xs : List (Option (Similarity α))) : ComputationM α (Option (Similarity α)) := 
    match minimalDistanceSimilarity? xs with 
    | none => pure none
    | some minimalDistanceSimilarity => saveAndReturnIfValid minimalDistanceSimilarity 

  let returnMinimalDistanceSimilarity 
    (xs : List (Option (Similarity α))) : ComputationM α (Option (Similarity α)) := 
    match minimalDistanceSimilarity? xs with 
    | none => pure none
    | some minimalDistanceSimilarity => pure minimalDistanceSimilarity 

  let matchBelowOneOf (t : Tree α) (xs : List (Tree α)) : ComputationM α (Option (Similarity α)) := 
    if xs == [] then 
      pure <| some ⟨metanode [], t.numberOfNodes⟩ 
    else do
      let pairwiseSimilarities ← xs.mapM (fun x => computeWithCache t x)
      match minimalDistanceSimilarityAndIdx? pairwiseSimilarities with 
      | none => pure none 
      | some (minimizer, minimizerIdx) =>
          let generalizer := metanode $ [minimizer.generalizer]
          let distance := minimizer.distance + numberOfNodes (xs.eraseIdx minimizerIdx) + 1
          pure <| some ⟨generalizer, distance⟩

  let nodesMatchAtOrdinaryNodeRoot (label : α) (children1 : List (Tree α)) (children2 : List (Tree α)) 
    : ComputationM α (Option (Similarity α)) := do 
    let pairwiseSimilarities ← (children1.zip children2).mapM (fun (x, y) => computeWithCache x y) 
    match valuesIfNoNone pairwiseSimilarities with 
    | none => pure none 
    | some childSimilarities => 
      let distance := cumulativeDistance childSimilarities
      let generalizer := node label (generalizers childSimilarities)
      pure <| some ⟨generalizer, distance⟩ 

  let nodesDontMatch (label1 : α) (children1 : List (Tree α)) 
                     (label2 : α) (children2 : List (Tree α)) : ComputationM α (Option (Similarity α)) := do
    let firstMatchesInChildNodeOfSecond := (← matchBelowOneOf (node label1 children1) children2) + 1
    let secondMatchesInChildNodeOfFirst := (← matchBelowOneOf (node label2 children2) children1) + 1
    returnMinimalDistanceSimilarity [firstMatchesInChildNodeOfSecond, secondMatchesInChildNodeOfFirst]

  let nodesMatchAtMetaNodeRoot (children1 : List (Tree α)) (children2 : List (Tree α)) : 
    ComputationM α (Option (Similarity α)) := do
    let calculation ← computeWithCache (metanode children1) (metanode children2)
    match calculation + 2 with 
    | none => pure none 
    | some v => pure <| some v 

  let similarityOfNodesWithDifferentLabels (label1 : α) (children1 : List (Tree α)) 
                                           (label2 : α) (children2 : List (Tree α)) : 
                                           ComputationM α (Option (Similarity α)) := do
    let case1 ← nodesMatchAtMetaNodeRoot children1 children2
    let case2 ← nodesDontMatch label1 children1 label2 children2
    saveAndReturnMinimalDistanceSimilarity [case1, case2]

  let similarityOfNodesWithIdenticalLabels (label : α) (children1 : List (Tree α)) (children2 : List (Tree α)) : 
    ComputationM α (Option (Similarity α)) := do
    let case1a ← nodesMatchAtOrdinaryNodeRoot label children1 children2
    let case1b ← nodesMatchAtMetaNodeRoot children1 children2
    let case2 ← nodesDontMatch label children1 label children2
    saveAndReturnMinimalDistanceSimilarity [case1a, case1b, case2]

  let metaNodesMatchAtRoot (annotations1 : List (Tree α)) (annotations2 : List (Tree α)) : 
    ComputationM α (Option (Similarity α)) := do
    let (shorter, longer) := shorterAndLonger annotations1 annotations2
    let m := longer.length 

    let computations ← shorter.mapM (fun a => longer.mapM (fun b => computeWithCache a b))

    let costMatrix := computations.map (fun as => as.map (fun b => distance? b))

    match minimalMatching costMatrix with 
    | none => pure none
    | some (cost, matchingList) => 
      let IdxsOfChildrenNotInMatching := (List.range m).removeAll matchingList
      let matching := List.asFunction matchingList
      
      let costOfDeletingChildren := numberOfNodes (IdxsOfChildrenNotInMatching.map (fun i => longer[matching i]!))
      let distance := cost + costOfDeletingChildren
      let resultingChildren := computations.mapIdx (fun i x => 
                                match x[matching i]! with 
                                | some c => c.generalizer
                                | none => dbg_trace "! Invalid result!"; metanode [])
      let generalizer := metanode resultingChildren 
      pure <| some ⟨generalizer, distance⟩ 

  let metaNodesDontMatch (annotations1 : List (Tree α)) (annotations2 : List (Tree α)) : 
    ComputationM α (Option (Similarity α)) := do
    let firstMatchesInAnnotationOfSecond ← matchBelowOneOf (metanode annotations1) annotations2
    let secondMatchesInAnnotationOfFirst ← matchBelowOneOf (metanode annotations2) annotations1
    returnMinimalDistanceSimilarity [firstMatchesInAnnotationOfSecond, secondMatchesInAnnotationOfFirst]

  let calculateSimilarity : Tree α → Tree α → ComputationM α (Option (Similarity α)) 
    | node v [], node w [] => saveAndReturnIfValid <|
      if v==w then 
        ⟨node v [], 0⟩ 
      else 
        ⟨metanode [], 2⟩

    | metanode xs, metanode [] 
    | metanode [], metanode xs => 
      let generalizer := metanode []
      let distance := numberOfNodes xs
      saveAndReturnIfValid ⟨generalizer, distance⟩ 
      
    | node v xs, node w ys => 
      if v == w && xs.length == ys.length then 
        similarityOfNodesWithIdenticalLabels v xs ys
      else 
        similarityOfNodesWithDifferentLabels v xs w ys

    | metanode xs, metanode ys => do 
      let case1 ← metaNodesMatchAtRoot xs ys
      let case2 ← metaNodesDontMatch xs ys
      saveAndReturnMinimalDistanceSimilarity [case1, case2]

    | node v xs, metanode ys 
    | metanode ys, node v xs => do 
      let matchAtRoot := (← computeWithCache (metanode xs) (metanode ys)) + 1
      let onlyNodeMappedToRoot := (← matchBelowOneOf (metanode ys) xs) + 1
      let onlyMetanodeMappedToRoot ← matchBelowOneOf (node v xs) ys
      saveAndReturnMinimalDistanceSimilarity [matchAtRoot, onlyNodeMappedToRoot, 
                                              onlyMetanodeMappedToRoot]

  let getFromCache trees := @getFromCache _ (Similarity α) _ trees

  match ← getFromCache (tree1, tree2) with
  | some v => pure v
  | none => let result := calculateSimilarity tree1 tree2
            match ← result with 
            | none => result
            | some v => dbg_trace s!"{tree1} <> {tree2} >> {v}"; result

instance : ToString (WithTop ℕ) where 
  toString s := match s with 
                | none => "⊤"
                | some v => toString v 

def computeAux [BEq α] [ToString α] (t1 : Tree α) (t2 : Tree α) 
  (configuration : Configuration) (cache : SimilarityCache α) : 
  Option (Similarity α) × SimilarityCache α := 
  dbg_trace s!"ComputeAux for n = {configuration.maximumDistance}";
  ReaderT.run (computeWithCache t1 t2) configuration cache 

def compute' [BEq α] [ToString α] (t1 : Tree α) (t2 : Tree α) (configuration : Configuration) : 
  Option (Similarity α) × SimilarityCache α := 
  let initialState := emptyCache
  ReaderT.run (computeWithCache t1 t2) configuration initialState 
  
def computeTest [ToString α] [BEq α] : Tree α → Tree α → Option (Similarity α) := 
  fun t1 t2 => (compute' t1 t2 ⟨true, none⟩).fst

#eval computeTest (node "+" [leaf "a", leaf "b"]) (node "*" [node "+" [leaf "a", leaf "b"]])

def computeUpTo [BEq α] [ToString α] (t1 : Tree α) (t2 : Tree α) (collapseMetaNodes : Bool := true) : 
  (n : Nat) → Option (Similarity α) × SimilarityCache α 
  | 0 => let initialConfiguration := ⟨collapseMetaNodes, some 0⟩ 
         computeAux t1 t2 initialConfiguration emptyCache 
  | n + 1 => match computeUpTo t1 t2 collapseMetaNodes n with 
             | (some c, cache) => (c, cache)
             | (none, cache) => let configuration := ⟨collapseMetaNodes, some (n+1)⟩ 
                                computeAux t1 t2 configuration cache

def compute [BEq α] [ToString α] (t1 : Tree α) (t2 : Tree α) : Option $ Similarity α := 
  -- compute' t1 t2 default |>.fst
  computeUpTo t1 t2 true 100 |>.fst


def tree1 : Tree String := node "+" [leaf "a", leaf "b"]
def TEST0 := compute tree1 tree1 == some ⟨tree1, 0⟩ 

def tree2 : Tree String := node "+" [leaf "a", leaf "c"]
def TEST1 := compute tree1 tree2 == some ⟨node "+" [leaf "a", metanode []], 2⟩ 

def tree3 : Tree String := (node "+" [leaf "d", tree1]) 
def TEST2 := compute tree1 tree3 == some ⟨metanode [node "+" [leaf "a", leaf "b"]], 3⟩ 

def tree4 : Tree String := (node "+" [tree1, node "+" [leaf "c", leaf "b"]])
def TEST3 := compute tree1 tree4 == some ⟨metanode [node "+" [leaf "a", leaf "b"]], 5⟩ 

def TEST4 := compute tree1 (.metanode [.leaf "a"]) == some ⟨metanode [leaf "a"], 2⟩ 

def tree5 : Tree String := node "+" [node "+" [leaf "c", leaf "b"], tree1]
def tree6 : Tree String := node "+" [tree1, node "+" [node "+" [leaf "d", leaf "c"], tree1]]
def tree7 : Tree String := node "+" [node "+" [metanode [], leaf "b"], metanode [tree1]]
def TEST5 := compute tree5 tree6 == some ⟨tree7, 7⟩  

def TESTS := TEST0 && TEST1 && TEST2 && TEST3 && TEST4 && TEST5

#eval TESTS
#eval computeUpTo tree1 tree3 true 3 |>.fst
#eval computeAux tree1 tree3 ⟨true, some 2⟩ default  

#eval (tree1, tree3) 