import Search
import Mathlib.Data.Real.Basic

section Numbers 

  example : ∀a b : Nat, a + (b + 0) = b + a := by 
    aesop_with_search [Nat.mul_comm, Nat.add_comm, Nat.add_assoc, Nat.mul_assoc]
  example : ∀a b c : Nat, (a + b) + c = a + (b + c) + 0 := by 
    aesop_with_search [Nat.mul_comm, Nat.add_comm, Nat.add_assoc, Nat.mul_assoc]
  example : ∀a b : Nat, ((((a + b) ^ 2) ^ 2) ^ 2) = ((((b + a) ^ 2) ^ 2) ^ 2) := by 
    aesop_with_search [Nat.mul_comm, Nat.add_comm, Nat.add_assoc, Nat.mul_assoc]
  example (a b : Nat) : a + (b + 0) = b + a := by 
    aesop_with_search [Nat.mul_comm, Nat.add_comm, Nat.add_assoc, Nat.mul_assoc]
  example (a b c : Nat) : (a + b) + c = a + (b + c) + 0 := by 
    aesop_with_search [Nat.mul_comm, Nat.add_comm, Nat.add_assoc, Nat.mul_assoc]
  example (a b : Nat) : ((((a + b) ^ 2) ^ 2) ^ 2) = ((((b + a) ^ 2) ^ 2) ^ 2) := by 
    aesop_with_search [Nat.mul_comm, Nat.add_comm, Nat.add_assoc, Nat.mul_assoc]
  example (a b : Int) : a + (b + 0) = b + a := by 
    aesop_with_search [Nat.mul_comm, Nat.add_comm, Nat.add_assoc, Nat.mul_assoc, 
                      Int.mul_comm, Int.add_comm, Int.add_assoc, Int.mul_assoc]
  example (a b c : Int) : (a + b) + c = a + (b + c) + 0 := by 
    aesop_with_search [Nat.mul_comm, Nat.add_comm, Nat.add_assoc, Nat.mul_assoc, 
                      Int.mul_comm, Int.add_comm, Int.add_assoc, Int.mul_assoc]
  example (a b : Int) : ((((a + b) ^ 2) ^ 2) ^ 2) = ((((b + a) ^ 2) ^ 2) ^ 2) := by 
    aesop_with_search [Nat.mul_comm, Nat.add_comm, Nat.add_assoc, Nat.mul_assoc, 
                      Int.mul_comm, Int.add_comm, Int.add_assoc, Int.mul_assoc]
    sorry -- correct lemma found but aesop does not succeed
  example : ∀a b : ℝ, a + (b + 0) = b + a := by 
    aesop_with_search [@mul_comm, @add_comm, @add_assoc, @mul_assoc]

section Functions 
  example (f g : α → α) (h: ∀ x, f x = g x) : f = g := by
    aesop_with_search [funext, funext₂, funext₃]
  example (f g : α → α) (h : ∀ x, f (g x) = g (f x)) : 
    f ∘ g = g ∘ f := by
    aesop_with_search [funext, funext₂, funext₃]

section Sets
  -- Universe parameters are passed explicitly yet since their appropriate conversion is not implemented in the tree conversion function
  example (α : Type u) (A B : Set α) : A ∪ (B ∪ ∅) = B ∪ A := by 
    aesop_with_search [Set.union_comm.{u}, Set.inter_comm.{u}, 
                      Set.union_assoc.{u}, Set.inter_assoc.{u}]
  example (α : Type u) (A B C D : Set α) : 
    ((A ∩ D) ∪ B) ∪ C = (A ∩ D) ∪ (B ∪ C) := by 
    aesop_with_search [Set.union_assoc.{u}, Set.inter_assoc.{u}]
  example (α : Type u) (A B : Set α) : A ∩ (B ∪ ∅) = B ∩ A := by 
    aesop_with_search [Set.union_comm.{u}, Set.inter_comm.{u}, 
                      Set.union_assoc.{u}, Set.inter_assoc.{u}]
  example (α : Type u) (A B C D : Set α) : 
    ((A ∩ D) ∩ B) ∩ C = (A ∩ D) ∩ (B ∩ C) := by 
    aesop_with_search [Set.union_assoc.{u}, Set.inter_assoc.{u}]
  example (α : Type u) (A B : Set α) (x : α) (h: x ∈ A) (h2 : x ∉ B) :
    x ∈ Set.diff A B := by 
    aesop_with_search [Set.union_comm.{u}, Set.inter_comm.{u}, 
                      Set.union_assoc, Set.inter_assoc, Set.diff]
    -- correct lemma found but aesop does not succeed
    -- the following two tactic applications close the goal:  
    rw [Set.diff]
    aesop

section Groups

  example [Group G] (g h : G) : (g * h) * h = g * (h * h) := by 
    aesop_with_search [@mul_assoc, @one_mul, @mul_one, @mul_left_inv]
    sorry -- correct lemma not found because of universe level issue
  example [CommGroup G] (g h : G) : g * h = h * g := by 
    aesop_with_search [@mul_comm, @mul_assoc, @mul_left_inv, @one_mul, @mul_one]
    sorry -- correct lemma not found because of universe level issue
