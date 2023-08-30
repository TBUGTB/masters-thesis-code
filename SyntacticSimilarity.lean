import Utility.IncompleteMatchings
import HoleTree 
import Utility.HashMapCache
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

instance [BEq α] : BEq (Tree α × Tree α) where 
  beq x y := x.fst == y.fst && x.snd == y.snd

abbrev SimilarityCache (α : Type) [BEq α] [Hashable α] := Cache (Tree α × Tree α) (Similarity α)

-- instance [ToString α] : ToString (SimilarityCache α) where 
--   toString c := toString c.cache

abbrev SimilarityStateM (α : Type) [BEq α] [Hashable α] := StateM (SimilarityCache α)

abbrev ComputationM (α β : Type) [BEq α] [Hashable α] := (ReaderT Configuration (SimilarityStateM α)) β

instance : HSub (WithTop Nat) Nat (Option Nat) where 
  hSub x y := match x with 
              | none => none 
              | some x => x - y

def Configuration.reduceMaximumDistanceBy (c : Configuration) (n : Nat) := 
  {c with maximumDistance := c.maximumDistance - n}

variable {α : Type} [BEq α] [Hashable α]

def withAddToDistanceAfterCalculation (n : Nat) (x : ComputationM α (Option (Similarity β))) : 
  ComputationM α (Option (Similarity β)) := 
  withReader (fun configuration => configuration.reduceMaximumDistanceBy n) do 
    x
  >>= fun x => pure (x + n)

def Similarity.distanceDoesNotExceedMaximum (c : Similarity α) : ComputationM α Bool := do 
  let maximumDistance := (← read).maximumDistance
  pure $ c.distance <= maximumDistance

def saveUnderKeyAndReturnIfValid [BEq α] [ToString α] [Hashable α] (key : Tree α × Tree α) (similarity : Similarity α) : 
  ComputationM α (Option (Similarity α)) := do
  if (← similarity.distanceDoesNotExceedMaximum) then 
    saveToCache key similarity
    pure (some similarity) 
  else 
    pure none 

section 

variable [ToString α] 
         (computeWithCache : Tree α → Tree α → ComputationM α (Option (Similarity α)))

  def matchBelowOneOf (t : Tree α) (xs : List (Tree α)) : ComputationM α (Option (Similarity α)) := 
    if xs == [] then 
      pure <| some ⟨metanode [], t.numberOfNodes⟩ 
    else do
      let pairwiseSimilarities ← xs.mapM (fun x => computeWithCache t x)
      match minimalDistanceSimilarityAndIdx? pairwiseSimilarities with 
      | none => pure none 
      | some (minimizer, minimizerIdx) =>
          let generalizer := metanode $ [minimizer.generalizer]
          let distance := minimizer.distance + numberOfNodes (xs.eraseIdx minimizerIdx)
          pure <| some ⟨generalizer, distance⟩

  def nodesMatchAtOrdinaryNodeRoot (label : α) (children1 : List (Tree α)) (children2 : List (Tree α)) 
    : ComputationM α (Option (Similarity α)) := do 
    let pairwiseSimilarities ← (children1.zip children2).mapM (fun (x, y) => computeWithCache x y) 
    match valuesIfNoNone pairwiseSimilarities with 
    | none => pure none 
    | some childSimilarities => 
      let distance := cumulativeDistance childSimilarities
      let generalizer := node label (generalizers childSimilarities)
      pure <| some ⟨generalizer, distance⟩ 

  def nodesMatchAtMetaNodeRoot (children1 : List (Tree α)) (children2 : List (Tree α)) : 
    ComputationM α (Option (Similarity α)) := do
    let calculation ← withAddToDistanceAfterCalculation 2 do 
      computeWithCache (metanode children1) (metanode children2)
    match calculation with 
    | none => pure none 
    | some v => pure <| some v 

  def metaNodesMatchAtRoot (annotations1 : List (Tree α)) (annotations2 : List (Tree α)) : 
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

end 

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

  let nodesDontMatch (label1 : α) (children1 : List (Tree α)) 
                     (label2 : α) (children2 : List (Tree α)) : ComputationM α (Option (Similarity α)) := do
    let firstMatchesInChildNodeOfSecond ← withAddToDistanceAfterCalculation 2 do
      matchBelowOneOf computeWithCache (node label1 children1) children2
    let secondMatchesInChildNodeOfFirst ← withAddToDistanceAfterCalculation 2 do 
      matchBelowOneOf computeWithCache (node label2 children2) children1
    returnMinimalDistanceSimilarity [firstMatchesInChildNodeOfSecond, secondMatchesInChildNodeOfFirst]

  let similarityOfNodesWithDifferentLabels (label1 : α) (children1 : List (Tree α)) 
                                           (label2 : α) (children2 : List (Tree α)) : 
                                           ComputationM α (Option (Similarity α)) := do
    let case1 ← nodesMatchAtMetaNodeRoot computeWithCache children1 children2
    let case2 ← nodesDontMatch label1 children1 label2 children2
    saveAndReturnMinimalDistanceSimilarity [case1, case2]

  let similarityOfNodesWithIdenticalLabels (label : α) (children1 : List (Tree α)) (children2 : List (Tree α)) : 
    ComputationM α (Option (Similarity α)) := do
    let case1a ← nodesMatchAtOrdinaryNodeRoot computeWithCache label children1 children2
    let case1b ← nodesMatchAtMetaNodeRoot computeWithCache children1 children2
    let case2 ← nodesDontMatch label children1 label children2
    saveAndReturnMinimalDistanceSimilarity [case1a, case1b, case2]

  let metaNodesDontMatch (annotations1 : List (Tree α)) (annotations2 : List (Tree α)) : 
    ComputationM α (Option (Similarity α)) := do
    let firstMatchesInAnnotationOfSecond ← matchBelowOneOf computeWithCache (metanode annotations1) annotations2
    let secondMatchesInAnnotationOfFirst ← matchBelowOneOf computeWithCache (metanode annotations2) annotations1
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

    -- additional case for optimization
    | metanode xs, metanode [y] 
    | metanode [y], metanode xs => matchBelowOneOf computeWithCache y xs
      
    | metanode xs, metanode ys => do 
      let case1 ← metaNodesMatchAtRoot computeWithCache xs ys
      let case2 ← metaNodesDontMatch xs ys
      saveAndReturnMinimalDistanceSimilarity [case1, case2]

    | node v xs, metanode ys 
    | metanode ys, node v xs => do 
      let matchAtRoot ← withAddToDistanceAfterCalculation 1 do  
                           computeWithCache (metanode xs) (metanode ys)
      let onlyNodeMappedToRoot ← withAddToDistanceAfterCalculation 1 do 
                                  matchBelowOneOf computeWithCache (metanode ys) xs
      let onlyMetanodeMappedToRoot ← withAddToDistanceAfterCalculation 1 do 
                                  matchBelowOneOf computeWithCache (node v xs) ys
      saveAndReturnMinimalDistanceSimilarity [matchAtRoot, onlyNodeMappedToRoot, 
                                              onlyMetanodeMappedToRoot]

  let getFromCache trees := @getFromCache (Tree α × Tree α) (Similarity α) _ _ trees

  match ← getFromCache (tree1, tree2) with
  | some v => pure v
  | none => let result := calculateSimilarity tree1 tree2
            
            -- let message := match ← result with 
            --   | none => ""
            --   | some v => s!"{tree1} <> {tree2} >> {v}"
            -- dbg_trace message
            
            result
-- end of computation function definition 


instance : ToString (WithTop ℕ) where 
  toString s := match s with 
                | none => "⊤"
                | some v => toString v 

def computeAux [BEq α] [ToString α] (t1 : Tree α) (t2 : Tree α) 
  (configuration : Configuration) (cache : SimilarityCache α) : 
  Option (Similarity α) × SimilarityCache α := 
  dbg_trace s!"ComputeAux for n = {configuration.maximumDistance}";
  ReaderT.run (computeWithCache t1 t2) configuration cache 

def compute' [BEq α] [Hashable α] [ToString α] (t1 : Tree α) (t2 : Tree α) (configuration : Configuration) : 
  Option (Similarity α) × SimilarityCache α := 
  let initialState := @emptyCache (Tree α × Tree α) _
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
             | (none, cache) => let configuration := ⟨collapseMetaNodes, some (n + 1)⟩ 
                                computeAux t1 t2 configuration cache

def compute [BEq α] [ToString α] (t1 : Tree α) (t2 : Tree α) : Option (Similarity α) := 
  compute' t1 t2 default |>.fst
  -- computeUpTo t1 t2 true 10 |>.fst

def indexOfMinimalDistanceTree [BEq α] [ToString α] (tree1 : Tree α) (ts : List (Tree α)) : Nat := 
  let pairwiseSimilarities := ts.map (compute tree1) 
  match minimalDistanceSimilarityAndIdx? pairwiseSimilarities with 
  | none => unreachable!
  | some (_, idx) => idx  