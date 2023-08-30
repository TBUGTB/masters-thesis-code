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
If the list does not contain any `none`, returns a list of all the values of the options.   
-/
def valuesIfNoNone : List (Option α) → Option (List α) 
  | [] => some []
  | x :: xs => match x, valuesIfNoNone xs with 
               | some v, some tail => v :: tail
               | _, _ => none
