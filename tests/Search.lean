import Search

open Lean Lean.Meta

def libraryLemmaNames := [``Nat.mul_comm, ``Nat.add_comm, ``Nat.add_assoc]

elab "library_similarity_search" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let type ← goal.getType
    let reduced ← withTransparency .instances $ reduceAll type

    let result ← bestSyntacticLibraryMatch reduced libraryLemmaNames

    dbg_trace "Best match: {result}"

    let resultIdentifier : Ident := mkIdent result

    Elab.Tactic.evalTactic (← `(tactic| aesop (add unsafe $resultIdentifier:ident)))

example : ∀a b : Nat, a + (b + 0) = b + a := by 
  library_similarity_search

example : ∀a b c : Nat, (a + b) + c = a + (b + c) + 0 := by 
  library_similarity_search

example : ∀a b : Nat, ((((a + b) ^ 2) ^ 2) ^ 2) = ((((b + a) ^ 2) ^ 2) ^ 2) := by 
  -- library_similarity_search -- takes a bit longer so commented out 
  sorry
  
  -- The search finds the correct lemma, but 
  -- Aesop doesn't succeed in this case. Passing add_comm to simp or rw works