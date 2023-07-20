import Lean
import ReferenceImplementation
import Aesop 

open Lean HoleTree Lean.Meta

def marker (s : String) : Expr := .mdata (MData.empty.insert "marker" s) default 

def unfoldArguments : Expr → Expr × List Expr
  | Expr.app f x => let (func, args) := unfoldArguments f
                    (func, args ++ [x]) 
  | e => (e, [])

partial def Lean.Expr.toTree : Expr → MetaM (Tree Expr)  
  | Expr.const declName us => pure <| Tree.leaf (.const declName us)
  | Expr.bvar n => dbg_trace "Detected bvar"; pure <| Tree.leaf  (.bvar n)
  | Expr.fvar fvarId =>  pure <| Tree.leaf (.fvar fvarId)
  | Expr.mvar mvarId =>  pure <| Tree.leaf (.mvar mvarId)
  | Expr.lit x =>  pure <| Tree.leaf (Expr.lit x)
  | Expr.sort u =>  pure <| Tree.leaf (Expr.sort u)
  | Expr.app f x => do 
                    let (func, args) := unfoldArguments (Expr.app f x)
                    let argTrees ← args.mapM Expr.toTree 
                    pure <| .node (func) argTrees 
  | Expr.forallE binderName binderType b binderInfo => do 
      let (mvars, _, body) ← forallMetaTelescopeReducing <| Expr.forallE binderName binderType b binderInfo
      let bodyTree ← body.toTree
      let mvarList := mvars.toList 
      let mvarTypes ← mvarList.mapM inferType
      let mvarTypeTrees ← mvarTypes.mapM Expr.toTree
      pure <| Tree.node (marker "forall") (mvarTypeTrees ++ [bodyTree])
  | Expr.lam binderName binderType b binderInfo => do 
      let (_, _, body) ← lambdaMetaTelescope <| Expr.lam binderName binderType b binderInfo
      let bodyTree ← body.toTree
      pure <| .node (marker "lambda") [bodyTree] 
  | Expr.mdata _ e => e.toTree
  | x => dbg_trace "Unforeseen expression case (let or proj) cannot be further transformed into a tree"; 
        pure <| .leaf x

def createExprTreeFromLemmaName (name : Lean.Name) : Lean.Elab.Tactic.TacticM (Tree Expr) := do 
  let lem ← mkConstWithFreshMVarLevels name
  let typ ← Lean.Meta.inferType lem
  let reduced ← withTransparency .instances $ reduceAll typ
  pure (← reduced.toTree)

def nextLibraryMatch (currentDistance : Option Nat) (distance : Nat) (currentName : Name) (name : Name) : 
                     (Option Nat) × Name :=
  match currentDistance with 
  | none => (distance, name)
  | some d => if d < distance then (currentDistance, currentName) else (distance, name) 

open Lean.Elab.Tactic in 
def bestSyntacticLibraryMatch (e : Expr) (libraryLemmas : List Name) : TacticM Name := do
  let tree ← e.toTree
  let mut currentMinimizer : Name := ``Nat
  let mut currentDistance : Option Nat := none
  for lem in libraryLemmas do 
    dbg_trace "... calculating distance between goal and {lem} ..."
    let lemTree ← createExprTreeFromLemmaName lem
    let computation := SyntacticSimilarity.compute tree lemTree
    -- dbg_trace f!"{computation.distance} {tree.size} {lemTree.size} {tree} \n {lemTree}"
    (currentDistance, currentMinimizer) := nextLibraryMatch currentDistance computation.distance currentMinimizer lem    
  pure currentMinimizer