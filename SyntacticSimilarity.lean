import IncompleteMatchings
import HoleTree 
import ComputationCache
import Mathlib.Order.WithBot

open HoleTree Tree

namespace SyntacticSimilarity

structure Computation (α : Type) where  
  generalizer : Tree α 
  distance : Nat 
deriving BEq

instance : HAdd (Option (Computation α)) Nat (Option (Computation α)) where 
  hAdd c a := match c with 
    | none => none 
    | some c => some {c with distance := c.distance + a}

instance : Inhabited (Computation α) where 
  default := ⟨metanode [], 0⟩ 

instance [ToString α] : ToString (Computation α) where 
  toString c := toString c.generalizer  ++ " | " ++ toString c.distance

structure Configuration where 
  collapseMetanodes : Bool := true 
  maximumDistance : WithTop Nat := none
  maximumMetaNodes : WithTop Nat := none
deriving Repr, BEq, Inhabited 

abbrev ComputationCache (α : Type) := Cache (Tree α × Tree α) (Computation α)

instance [ToString α] : ToString (ComputationCache α) where 
  toString c := toString c.cache

abbrev ComputationStateM (α : Type) := StateM (ComputationCache α)

abbrev ComputationM (α β : Type) := (ReaderT Configuration (ComputationStateM α)) β

def computationOfMinimalDistanceAndIdx : List (Option (Computation α)) → Option (Computation α × Nat)  
  | x :: xs => let tail := computationOfMinimalDistanceAndIdx xs
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

-- This must already exist, refactor
def allValues : List (Option α) → Option (List α) 
  | [] => some []
  | x :: xs => match x, allValues xs with 
               | some v, some tail => v :: tail
               | _, _ => none

def distances (xs : List (Computation α)) : List Nat := 
  xs.map (fun x => x.distance)

def distance? (c : Option (Computation α)) : Option Nat := 
  match c with 
  | none => none
  | some c => c.distance

def generalizers (xs : List (Computation α)) : List (Tree α) := 
  xs.map (fun x => x.generalizer)

def cumulativeDistance (xs : List (Computation α)) : Nat := 
  (distances xs).foldl (· + ·) 0 

def computationOfMinimalDistance (xs : List (Option (Computation α))) : Option (Computation α) := 
  match computationOfMinimalDistanceAndIdx xs with 
  | none => none
  | some (c, _) => c

instance : HSub (WithTop Nat) Nat (Option Nat) where 
  hSub x y := match x with 
              | none => none 
              | some x => x - y

def Configuration.reduceMaximumDistanceBy (c : Configuration) (n : Nat) := 
  {c with maximumDistance := c.maximumDistance - n}

def withAddToDistanceAfterCalculation (n : Nat) : 
  ComputationM α (Option (Computation β)) → ComputationM α (Option (Computation β)) := 
  fun x => (withReader $ fun y => y.reduceMaximumDistanceBy n) do 
    x
  >>= fun x => pure (x + n)

def Computation.distanceDoesNotExceedMaximum (c : Computation α) : ComputationM α Bool := do 
  let maximumDistance := (← read).maximumDistance
  pure $ c.distance < maximumDistance

def saveAndReturnIfOptimal [BEq α] (key : Tree α × Tree α) (c : Computation α) : 
  ComputationM α (Option (Computation α)) := do
  if (← c.distanceDoesNotExceedMaximum) then 
    saveToCache key c
    pure (some c) 
  else 
    pure none 

partial def computeWithCache [BEq α] [ToString α] (tree1 : Tree α) (tree2 : Tree α) : 
  ComputationM α (Option (Computation α)) := do
    
    let getFromCache t := @getFromCache _ (Computation α) _ t

    let saveAndReturn (c : Computation α) : ComputationM α (Option (Computation α)) := 
      saveAndReturnIfOptimal (tree1, tree2) c

    let saveAndReturnMinimalCostComputation (xs : List (Option (Computation α))) :
      ComputationM α (Option (Computation α)) := 
      match computationOfMinimalDistance xs with 
      | none => pure none
      | some minimalComputation => saveAndReturn minimalComputation 

    let computeNodeList (t : Tree α) (xs : List (Tree α)) : ComputationM α (Option (Computation α)) := 
      if xs == [] then 
        saveAndReturn ⟨metanode [], t.size + 1⟩ 
      else do
        let computations ← xs.mapM (fun x => computeWithCache t x)
        match computationOfMinimalDistanceAndIdx computations with 
        | none => pure none 
        | some (minimizer, minimizerIdx) =>
            let generalizer := metanode $ [minimizer.generalizer]
            let distance := minimizer.distance + size (xs.eraseIdx minimizerIdx) + 1
            saveAndReturn ⟨generalizer, distance⟩

    let computeListList (xs : List (Tree α)) (ys : List (Tree α)) : ComputationM α (Option (Computation α)) := do
      let (shorter, longer) := shorterAndLonger xs ys
      let m := longer.length 

      let computations ← shorter.mapM (fun a => longer.mapM (fun b => computeWithCache a b))

      let costMatrix := computations.map (fun as => as.map (fun b => distance? b))

      match minimalMatching costMatrix with 
      | none => pure none
      | some (cost, matchingList) => 
        let IdxsOfChildrenNotInMatching := (List.range m).removeAll matchingList
        let matching := List.asFunction matchingList
        
        let costOfDeletingChildren := size (IdxsOfChildrenNotInMatching.map (fun i => longer[matching i]!))
        let distance := cost + costOfDeletingChildren
        let resultingChildren := computations.mapIdx (fun i x => 
                                  match x[matching i]! with 
                                  | some c => c.generalizer
                                  | none => dbg_trace "! Invalid result!"; metanode [])
        let generalizer := metanode resultingChildren 
        saveAndReturn ⟨generalizer, distance⟩ 

    if (← read).maximumDistance = some 0 then 
      return none
    
    match ← getFromCache (tree1, tree2) with
    | some v => pure v
    | none => match tree1, tree2 with
      | node v [], node w [] => saveAndReturn $ if v==w then ⟨node v [], 0⟩ else ⟨metanode [], 2⟩

      | metanode xs, metanode []
      | metanode [], metanode xs => saveAndReturn ⟨metanode [], size xs⟩
      
      | node v vs, node w ws =>  
        let leftInRight ← withAddToDistanceAfterCalculation 1 do 
          computeNodeList (node v vs) ws
        let rightInLeft ← withAddToDistanceAfterCalculation 1 do 
          computeNodeList (node w ws) vs
        let bothMetified ← withAddToDistanceAfterCalculation 2 do 
          computeWithCache (metanode ws) (metanode vs)
        if v == w then 
          let result ← (vs.zip ws).mapM (fun (x, y) => computeWithCache x y) 
          match allValues result with 
          | none => saveAndReturnMinimalCostComputation [leftInRight, rightInLeft, bothMetified]
          | some children => 
              let generalizer := node v $ generalizers children
              let distance := cumulativeDistance children
              let result : Computation α := ⟨generalizer, distance⟩ 
              saveAndReturnMinimalCostComputation [leftInRight, rightInLeft, bothMetified, result]
        else 
          saveAndReturnMinimalCostComputation [leftInRight, rightInLeft, bothMetified]

      | metanode xs, metanode ys => 
        let matchNodes ← computeListList xs ys
        let matchLeftBelowRight ← computeNodeList (metanode xs) ys
        let matchRightBelowLeft ← computeNodeList (metanode xs) ys
        saveAndReturnMinimalCostComputation [matchNodes, matchLeftBelowRight, matchRightBelowLeft] 
      
      | node v xs, metanode ys 
      | metanode ys, node v xs => 
        let convertNode ← withAddToDistanceAfterCalculation 1 do 
          computeWithCache (metanode xs) (metanode ys)
        let insertAboveNode ← withAddToDistanceAfterCalculation 1 do 
          computeNodeList (node v xs) ys
        let metanodeMappedToRoot ← computeNodeList (node v xs) ys
        saveAndReturnMinimalCostComputation [metanodeMappedToRoot, convertNode, insertAboveNode] 

def computeAux [BEq α] [ToString α] (t1 : Tree α) (t2 : Tree α) 
  (configuration : Configuration) (cache : ComputationCache α) : 
  Option (Computation α) × ComputationCache α := 
  ReaderT.run (computeWithCache t1 t2) configuration cache |>.run

def compute' [BEq α] [ToString α] (t1 : Tree α) (t2 : Tree α) (configuration : Configuration) : 
  Option (Computation α) × ComputationCache α := 
  let initialState := emptyCache
  ReaderT.run (computeWithCache t1 t2) configuration initialState |>.run
  
def computeTest [ToString α] [BEq α] : Tree α → Tree α → Option (Computation α) := 
  fun t1 t2 => (compute' t1 t2 ⟨true, none, none⟩).fst

#eval computeTest (node "+" [leaf "a", leaf "b"]) (node "*" [node "+" [leaf "a", leaf "b"]])

def computeUpTo [BEq α] [ToString α] (t1 : Tree α) (t2 : Tree α) (collapseMetaNodes : Bool := true) : 
  (n : Nat) → Option (Computation α) × ComputationCache α 
  | 0 => let initialConfiguration := ⟨collapseMetaNodes, some 1, ⊤⟩ 
         computeAux t1 t2 initialConfiguration emptyCache 
  | n + 1 => match computeUpTo t1 t2 collapseMetaNodes n with 
             | (some c, cache) => (c, cache)
             | (none, cache) => let configuration := ⟨collapseMetaNodes, some (n+1), none⟩ 
                                computeAux t1 t2 configuration cache

def compute [BEq α] [ToString α] (t1 : Tree α) (t2 : Tree α) : Option $ Computation α := 
  -- compute' t1 t2 |>.fst
  computeUpTo t1 t2 true 100 |>.fst
