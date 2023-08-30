import Std.Data.List.Basic

/--
Given a cost matrix of dimensions `n`, `m` one can represent a matching as a list of numberOfNodes `n` whose 
entries are unique elements of `{0..m-1}`. This function returns a list of all possible such matchings. 
-/
def allMatchings (n : Nat) (m : Nat) : List (List Nat) := 
  match n with 
  | 0 => []
  | 1 => (List.range m).map (fun x => [x])
  | n + 1 => let matchingsN := allMatchings n m
             let notInMatching (matching : List Nat) : List Nat := (List.range m).removeAll matching
             List.join (matchingsN.map (fun matchingN => 
             let elementsThatNPlusOneCanMapTo := notInMatching matchingN
             elementsThatNPlusOneCanMapTo.map (fun newElem => matchingN ++ [newElem])
             ))

#eval allMatchings 2 2 == [[0, 1], [1, 0]]
#eval allMatchings 3 2 == []

/--
Given a cost matrix and a matching calculate the cost of the given matching. None represents infinity.  
-/
def cost (matrix : List (List (Option Nat))) (matching : List Nat) : Option Nat := 
  let costs := matching.mapIdx (fun idx m => matrix[idx]![m]!)
  costs.foldl (fun x y => match x, y with 
                           | some x, some y => x + y
                           | _, _ => none) 
              (some 0)

#eval cost [[some 12,  some 5], 
            [some 25, some 34]] 
           (matching := [0, 1]) == some 46

#eval cost [[some 0, some 1], 
            [some 1, none]]
          (matching := [0, 1])


def filterSome : List (Option α) → List α 
  | [] => []
  | (some v) :: ls => v :: filterSome ls
  | none :: ls => filterSome ls
  

/--
Given a cost matrix calculate a minimal matching and its cost by brut force.  
-/
def minimalMatching (matrix : List (List (Option Nat))) : Option (Nat × (List Nat)) :=
  let n := matrix.length
  let m := matrix[0]!.length
  let allMatchings := allMatchings n m
  let costOfMatchings := allMatchings.map (fun matching => cost matrix matching)
  let finiteCostOfMatchings := filterSome costOfMatchings
  match List.minimum? finiteCostOfMatchings with 
    | some minimum => 
      let idxOfMinimalMatching := costOfMatchings.indexOf (some minimum)
      (minimum, allMatchings[idxOfMinimalMatching]!)
    | none => none

#eval minimalMatching [[some 12, some 5], 
                       [some 25, some 34]] == (30, [1, 0])

#eval minimalMatching [[some 10, some 11, some 16], 
                       [some 15, some 9, some 12]] == (19, [0, 1])

#eval minimalMatching [[some 4, none], 
                       [some 2, none]]