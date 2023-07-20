import Std.Data.List.Basic

/--
Given a cost matrix of dimensions `n`, `m` one can represent a matching as a list of size `n` whose 
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
Given a cost matrix and a matching calculate the cost of the given matching. 
-/
def cost (matrix : List (List Nat)) (matching : List Nat) : Nat := 
  let costs := matching.mapIdx (fun idx m => matrix[idx]![m]!)
  costs.foldl (· + ·) 0

#eval cost [[12,  5], 
            [25, 34]] 
           (matching := [0, 1]) == 46

/--
Given a cost matrix calculate a minimal matching and its cost by brut force.  
-/
def minimalMatching (matrix : List (List Nat)) : Nat × (List Nat) :=
  let n := matrix.length
  let m := matrix[0]!.length
  let allMatchings := allMatchings n m
  let costOfMatchings := allMatchings.map (fun matching => cost matrix matching)
  match List.minimum? costOfMatchings with 
    | some minimum => 
      let idxOfMinimalMatching := costOfMatchings.indexOf minimum
      (minimum, allMatchings[idxOfMinimalMatching]!)
    | none => dbg_trace "No minimal matching found, the given cost matrix is empty"; (0, [])

#eval minimalMatching [[12,  5], 
                       [25, 34]] == (30, [1, 0])

#eval minimalMatching [[10, 11, 16], 
                       [15,  9, 12]] == (19, [0, 1])