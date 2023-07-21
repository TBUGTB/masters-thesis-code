import SyntacticSimilarity

open HoleTree Tree SyntacticSimilarity

def aPlusB : Tree String := .node "+" [.leaf "a", .leaf "b"]

#eval compute aPlusB aPlusB -- (collapsemetanodes := true)

def TEST0 := compute aPlusB aPlusB == some ⟨aPlusB, 0⟩ 

#eval TEST0

def test0 : Tree String := (.node "+" [.leaf "c", aPlusB]) 
#eval (aPlusB, test0)
#eval compute aPlusB test0

def TEST1 := compute aPlusB test0 == some ⟨metanode [node "+" [leaf "a", leaf "b"]], 3⟩ 

#eval TEST1

def test1 : Tree String := (.node "+" [aPlusB, .node "+" [.leaf "c", .leaf "b"]])
#eval (aPlusB, test1)
#eval compute aPlusB test1 
#eval compute (.metanode [.leaf "a"]) aPlusB

def TEST2 := compute aPlusB test1 == some ⟨metanode [node "+" [leaf "a", leaf "b"]], 5⟩ 
def TEST3 := compute aPlusB (.metanode [.leaf "a"]) == some ⟨metanode [leaf "a"], 2⟩ 

def TESTS := TEST0 && TEST1 && TEST2 && TEST3

#eval TESTS

def test2 : Tree String := .node "+" [.node "+" [.leaf "c", .leaf "b"], aPlusB]
def test3 : Tree String := .node "+" [aPlusB, .node "+" [.node "+" [.leaf "d", .leaf "c"], aPlusB]]
#eval (test2, test3)
#eval compute test2 test3

def test4 : Tree String := .node "+" [.leaf "a", .node "*" [.leaf "b", .leaf "c"]]
def test5 : Tree String := .node "+" [.node "*" [.leaf "b", .leaf "a"], .leaf "c"]

#eval (test4, test5)
-- feature and not bug! 
#eval compute test4 test5 

-- -- More involved trees
def repeatN (x : α) (f : α → α) : Nat → α 
  | 0 => x
  | n+1 => f (repeatN x f n)

def largeTree (n : Nat) : Tree String := repeatN (.leaf "0") (fun x => Tree.node "+" [x, x]) n
#eval largeTree 2
-- #eval compute (largeTree 4) (.node "*" [largeTree 4]) 
-- 4 is still relatively fast, but 5 takes quite long

def square (t : Tree String) : Tree String := .node "(^2)" [t]

#eval repeatN aPlusB square 3
-- If n >= 3 the following gives unsatisfactory results, the common substructure of + [a, b] is not detected. 

#eval compute aPlusB (repeatN aPlusB square 3) -- even 100 still works after some time

#eval repeatN aPlusB (fun x => Tree.node "+" [x, x]) 1
#eval compute aPlusB (repeatN aPlusB (fun x => Tree.node "+" [x, x]) 5) -- more difficult but still fine for small values 