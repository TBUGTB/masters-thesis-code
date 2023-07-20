/--
Applies `f` to the two lists in parallel, stopping at the shorter list. 
Like `List.zipWith` in `Data.List.Basic` but also returns the remainder of the longer list
* `zipWith f [x₁, x₂, x₃] [y₁, y₂, y₃, y₄] = ([f x₁ y₁, f x₂ y₂, f x₃ y₃], y₄)`
-/
def zipWithAndRemainder (f : α → α → β) : (xs : List α) → (ys : List α) → List β × List α 
  | xs, []
  | [], xs => ([], xs)
  | x::xs, y::ys => let (zipped, remainder) := zipWithAndRemainder f xs ys 
                    (f x y :: zipped, remainder)

/--
Returns a tuple whose first entry is the shorter and whose second entry is the longer of the two 
given lists.
-/
def shorterAndLonger (xs : List α) (ys : List α) : List α × List α := 
  if xs.length < ys.length then (xs, ys) else (ys, xs)

def List.asFunction (m : List Nat) : (Nat → Nat) := 
  fun i => match m[i]? with 
  | none => m.length 
  | some v => v

/--
Returns true if the two given lists are equal up to permutation else false. 
-/
def List.equalUpToPermutation [BEq α] : List α → List α → Bool 
  | [], [] => true
  | [], _ => false
  | x :: xs, ys => if ys.contains x 
                   then equalUpToPermutation xs (ys.erase x) else false
