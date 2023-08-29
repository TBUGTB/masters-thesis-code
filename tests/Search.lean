import Search
import Mathlib.Data.Real.Basic

/-
The following are examples that try to demonstrate the power of the aesop_with_search tactic. This
is challenging for multiple reasons: 
  1. The tactic is limited by what Aesop can do with the search information. Sometimes, the 
     correct lemma is retrived by search but Aesop simply cannot complete the proof using this 
     information.
  2. It has to be illustrated that the tactic is strictly more capable than Aesop itself. 
     By construction, aesop_with_search can solve any goals that pure Aesop can solve. Therefore,
     all examples have to be chosen such that they are just beyond the scope of Aesop but still
     within reach if one more lemma is added to the rule set. One could overcome this limitation
     by allowing aesop_with_search to choose multiple lemmas that are passed on to Aesop. However, 
     for initial testing it is important to first validate the tactic in simple situations.  
These issues are also described in Section 5.6 of the thesis. 
-/
    

section Numbers 

  example : ∀a b : Nat, a + (b + 0) = b + a := by 
    aesop_with_search [Nat.mul_comm, Nat.add_comm, Nat.add_assoc, Nat.mul_assoc]
  example : ∀a b c : Nat, (a + b) + c = a + (b + c) + 0 := by 
    aesop_with_search [Nat.mul_comm, Nat.add_comm, Nat.add_assoc, Nat.mul_assoc]
  example : ∀a b : Nat, ((((a + b) ^ 2) ^ 2) ^ 2) = ((((b + a) ^ 2) ^ 2) ^ 2) := by 
    aesop_with_search [Nat.mul_comm, Nat.add_comm, Nat.add_assoc, Nat.mul_assoc]
  example : ∀ a b : Nat, a ^ (b+1) = a * a ^ b := by 
    aesop_with_search [Nat.mul_comm, Nat.add_comm, Nat.add_assoc, Nat.mul_assoc]
    -- correct lemma found but aesop does not succeed
    -- the following two tactic applications close the goal:  
    rw [Nat.mul_comm]
    aesop
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
  example (a b c : Int) : a * (b - c) = a * b - a * c := by 
    aesop_with_search [Int.mul_comm, Int.add_comm, Int.add_assoc, Int.mul_assoc, Int.mul_sub]
  example (a b c : Int) : a * (-b + c) = a * (c - b) := by 
    aesop_with_search [@mul_comm, @add_comm, @add_assoc, @mul_assoc, @sub_eq_neg_add, @neg_add_eq_sub]
    
  example : ∀a b : ℝ, a + (b + 0) = b + a := by 
    aesop_with_search [@mul_comm, @add_comm, @add_assoc, @mul_assoc]
  example : ∀a b : ℝ, a - b = - (- a + b) := by 
    aesop_with_search [@mul_comm, @add_comm, @add_assoc, @mul_assoc, @sub_eq_neg_add]
  example : ∀a b : ℝ, - a + b = b - a := by 
    aesop_with_search [@mul_comm, @add_comm, @add_assoc, @mul_assoc, @sub_eq_neg_add, @neg_add_eq_sub]
  example : ∀a : ℝ, ∀n : ℕ, a ^ (n + 1) = a ^ n * a := by 
    aesop_with_search [@mul_comm, @add_comm, @add_assoc, @mul_assoc]
    -- correct lemma found but aesop does not succeed
    rw [@mul_comm]
    aesop   


section Functions 

  example (f g : α → α) (h: ∀ x, f x = g x) : f = g := by
    aesop_with_search [funext, funext₂, funext₃]
  example (f g : α → α) (h : ∀ x, f (g x) = g (f x)) : 
    f ∘ g = g ∘ f := by
    aesop_with_search [funext, funext₂, funext₃]

section Sets
  -- Universe parameters are passed explicitly since their appropriate conversion is not implemented in the tree conversion function
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
    rw [Set.diff]
    aesop

section Groups

  example [Group G] (g h : G) : (g * h) * h = g * (h * h) := by 
    aesop_with_search [@mul_assoc, @one_mul, @mul_one, @mul_left_inv]
    sorry -- correct lemma not found because of universe level issue
  example [CommGroup G] (g h : G) : g * h = h * g := by 
    aesop_with_search [@mul_comm, @mul_assoc, @mul_left_inv, @one_mul, @mul_one]
    sorry -- correct lemma not found because of universe level issue

  -- the same goals not for abitrary types G but fixed types (and thus fixed universe levels) can be solved:
  example [Group Int] (g h : Int) : (g * h) * h = g * (h * h) := by 
    aesop_with_search [@mul_assoc, @one_mul, @mul_one, @mul_left_inv]
  example [CommGroup Int] (g h : Int) : g * h = h * g := by 
    aesop_with_search [@mul_comm, @mul_assoc, @mul_left_inv, @one_mul, @mul_one]
  
  example [CommGroup Int] (g h : Int) : g * h * 1 = h * g := by 
    aesop_with_search [@mul_comm, @mul_assoc, @mul_left_inv, @one_mul, @mul_one]
    sorry -- the first lemma is found correctly but the tactic then does not succeed 

  -- this can be alleviated through a second application of the same tactic: 
  example [CommGroup Int] (g h : Int) : g * h * 1 = h * g := by 
    aesop_with_search [@mul_comm, @mul_assoc, @mul_left_inv, @one_mul, @mul_one]
    aesop_with_search [@mul_comm, @mul_assoc, @mul_left_inv, @one_mul, @mul_one]

  example [CommGroup Int] (n : Nat) : g ^ (n + 1) = g * g ^ n := by 
    aesop_with_search [@mul_comm, @mul_assoc, @mul_left_inv, @one_mul, @mul_one]
    -- Correct result mul_comm is found but aesop does not succeed
    rw [mul_comm]
    aesop
