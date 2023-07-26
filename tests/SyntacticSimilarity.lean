import SyntacticSimilarity

open HoleTree Tree SyntacticSimilarity

def tree1 : Tree String := node "+" [leaf "a", leaf "b"]
def TEST0 := compute tree1 tree1 == some ⟨tree1, 0⟩ 

def tree2 : Tree String := node "+" [leaf "a", leaf "c"]
def TEST1 := compute tree1 tree2 == some ⟨node "+" [leaf "a", metanode []], 2⟩ 

def tree3 : Tree String := (node "+" [leaf "d", tree1]) 
def TEST2 := compute tree1 tree3 == some ⟨metanode [node "+" [leaf "a", leaf "b"]], 3⟩ 

def tree4 : Tree String := (node "+" [tree1, node "+" [leaf "c", leaf "b"]])
def TEST3 := compute tree1 tree4 == some ⟨metanode [node "+" [leaf "a", leaf "b"]], 5⟩ 

def TEST4 := compute tree1 (.metanode [.leaf "a"]) == some ⟨metanode [leaf "a"], 2⟩ 

def tree5 : Tree String := node "+" [node "+" [leaf "c", leaf "b"], tree1]
def tree6 : Tree String := node "+" [tree1, node "+" [node "+" [leaf "d", leaf "c"], tree1]]
def tree7 : Tree String := node "+" [node "+" [metanode [], leaf "b"], metanode [tree1]]
def TEST5 := compute tree5 tree6 == some ⟨tree7, 7⟩  

def TESTS := TEST0 && TEST1 && TEST2 && TEST3 && TEST4 && TEST5

#eval TEST2
#eval compute tree1 tree3
#eval (tree1, tree3)