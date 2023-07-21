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
  collapseMetaNodes : Bool := true 
  maximumDistance : Option Nat := none
  maximumMetaNodes : Option Nat := none
deriving Repr, BEq, Inhabited 

instance : ToString Configuration where 
  toString c := s!"{c.collapseMetaNodes} {c.maximumDistance} {c.maximumMetaNodes}"

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

instance : HSub (Option Nat) Nat (Option Nat) where 
  hSub x y := match x with 
              | none => none 
              | some x => x - y

def Configuration.reduceMaximumDistanceBy (c : Configuration) (n : Nat) := 
  {c with maximumDistance := c.maximumDistance - n}

def withAddToDistanceAfterCalculation (n : Nat) : ComputationM α (Option (Computation β)) → ComputationM α (Option (Computation β)) := 
  fun x => (withReader $ fun y => y.reduceMaximumDistanceBy n) do 
    x
  >>= fun x => pure (x + n)

def Computation.distanceDoesNotExceedMaximum (c : Computation α) : ComputationM α Prop := do 
  let maximumDistance := (← read).maximumDistance
  pure $ c.distance < maximumDistance

partial def computeWithCache [BEq α] [ToString α] 
  (tree1 : Tree α) (tree2 : Tree α) : ComputationM α (Option (Computation α)) := do
    
    let getFromCache t := @getFromCache _ (Computation α) _ t

    let saveAndReturn (v : Option (Computation α)) : ComputationM α (Option (Computation α)) := do 
      -- dbg_trace s!"Calculated {v} for {tree1} <> {tree2}"
      match v with 
      | none => pure none
      | some v => match (← read).maximumDistance with 
                  | none => saveToCache (tree1, tree2) v
                            pure (some v)
                  | some d => if v.distance <= d then 
                                saveToCache (tree1, tree2) v
                                pure (some v) 
                              else
                                pure none

    let computeNodeList (t : Tree α) (xs : List (Tree α)) : ComputationM α (Option (Computation α)) := do 
      if xs == [] then 
        saveAndReturn $ some ⟨metanode [], t.size + 1⟩ 
      else
        let computations ← xs.mapM (fun x => computeWithCache t x)
        match computationOfMinimalDistanceAndIdx computations with 
        | none => pure none 
        | some (minimizer, minimizerIdx) =>
            let generalizer := metanode $ [minimizer.generalizer]
            let distance := minimizer.distance + size (xs.eraseIdx minimizerIdx) + 1
            saveAndReturn $ some ⟨generalizer, distance⟩

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
        saveAndReturn $ some ⟨generalizer, distance⟩ 

    if (← read).maximumDistance = some 0 then 
      return none
    
    -- now get the the (cache) state
    match (← getFromCache (tree1, tree2)) with
    | some v => pure v
    | none => match tree1, tree2 with
      | node v [], node w [] => saveAndReturn $ some $ if v==w then ⟨node v [], 0⟩ else ⟨metanode [], 2⟩
      | metanode xs, metanode []
      | metanode [], metanode xs => saveAndReturn $ some ⟨metanode [], size xs⟩
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
          | none => saveAndReturn $ computationOfMinimalDistance [leftInRight, rightInLeft, bothMetified]
          | some children => 
              let generalizer := node v $ generalizers children
              let distance := cumulativeDistance children
              let result : Computation α := ⟨generalizer, distance⟩ 
              saveAndReturn $ computationOfMinimalDistance [leftInRight, rightInLeft, bothMetified, result]
        else 
          saveAndReturn $ computationOfMinimalDistance [leftInRight, rightInLeft, bothMetified]
      | metanode xs, metanode ys => let matchNodes ← computeListList xs ys
                                    let matchLeftBelowRight ← computeNodeList (metanode xs) ys
                                    let matchRightBelowLeft ← computeNodeList (metanode xs) ys
                                    saveAndReturn $ computationOfMinimalDistance [matchNodes, matchLeftBelowRight, matchRightBelowLeft] 
      | node v xs, metanode ys 
      | metanode ys, node v xs => let convertNode ← withAddToDistanceAfterCalculation 1 do 
                                    computeWithCache (metanode xs) (metanode ys)
                                  let insertAboveNode ← withAddToDistanceAfterCalculation 1 do 
                                    computeNodeList (node v xs) ys
                                  let metanodeMappedToRoot ← computeNodeList (node v xs) ys
                                  saveAndReturn $ computationOfMinimalDistance [metanodeMappedToRoot, convertNode, insertAboveNode] 

def compute' [BEq α] [ToString α] (t1 : Tree α) (t2 : Tree α) : 
  Option (Computation α) × ComputationCache α := 
  let computation := computeWithCache t1 t2
  let config := ⟨false, some 3, none⟩ 
  let initialState := default
  let result := ReaderT.run computation config initialState |>.run
  result

#eval compute' (node "+" [leaf "a", leaf "b"]) (node "*" [node "+" [leaf "a", leaf "b"]]) |>.fst

def computeUpTo [BEq α] [ToString α] (t1 : Tree α) (t2 : Tree α) (n : Nat) : Option (Computation α) × ComputationCache α :=
  match n with 
  | 0 => let computation := computeWithCache t1 t2
         let initialConfiguration := ⟨false, some 1, none⟩ 
         let initialState := default
         let (result, cache) := ReaderT.run computation initialConfiguration initialState |>.run
         (result, cache) 
  | n + 1 => 
    match computeUpTo t1 t2 n with 
    | (some v, cache) => if v.distance <= n then 
                          (some v, cache)
                         else
                          let computation := computeWithCache t1 t2
                          let configuration := ⟨false, some (n+1), none⟩ 
                          let (result, cache) := ReaderT.run computation configuration cache |>.run 
                          (result, cache)
    | (none, cache) => let computation := computeWithCache t1 t2
                       let initialConfiguration := ⟨false, some (n+1), none⟩ 
                       let (result, cache) := ReaderT.run computation initialConfiguration cache |>.run 
                       (result, cache)

def compute [BEq α] [ToString α] (t1 : Tree α) (t2 : Tree α) : Option $ Computation α := 
  -- compute' t1 t2 |>.fst
  computeUpTo t1 t2 100 |>.fst

