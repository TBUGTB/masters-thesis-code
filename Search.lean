import Lean
import SyntacticSimilarity
import Aesop 

open Lean HoleTree Lean.Meta

def marker (s : String) : Expr := .mdata (MData.empty.insert "marker" s) default 

def unfoldArguments : Expr → Expr × List Expr
  | Expr.app f x => let (function, arguments) := unfoldArguments f
                    (function, arguments ++ [x]) 
  | e => (e, [])

partial def Lean.Expr.toTree : Expr → MetaM (Tree Expr)  
  | Expr.const declName us => pure <| Tree.leaf (.const declName us)
  | Expr.fvar fvarId =>  pure <| Tree.leaf (.fvar fvarId)
  | Expr.mvar mvarId =>  pure <| Tree.leaf (.mvar mvarId)
  | Expr.lit x =>  pure <| Tree.leaf (Expr.lit x)
  | Expr.sort u =>  pure <| Tree.leaf (Expr.sort u)
  | Expr.app f x => do 
                    let (function, arguments) := unfoldArguments (Expr.app f x)
                    let argumentsAsTrees ← arguments.mapM Expr.toTree 
                    pure <| Tree.node (function) argumentsAsTrees 
  | Expr.forallE binderName binderType b binderInfo => do 
      let (mvars, _, body) ← forallMetaTelescopeReducing <| Expr.forallE binderName binderType b binderInfo
      let bodyAsTree ← body.toTree
      let mvarList := mvars.toList 
      let mvarTypes ← mvarList.mapM inferType
      let mvarTypesAsTrees ← mvarTypes.mapM Expr.toTree
      pure <| Tree.node (marker "forall") (mvarTypesAsTrees ++ [bodyAsTree])
  | Expr.lam binderName binderType b binderInfo => do 
      let (_, _, body) ← lambdaMetaTelescope <| Expr.lam binderName binderType b binderInfo
      let bodyTree ← body.toTree
      pure <| Tree.node (marker "lambda") [bodyTree] 
  | Expr.bvar _ => panic! "Unbound bvar in expression"
  | Expr.mdata _ e => e.toTree
  | x => dbg_trace "Unsupported Lean.Expr constructure (let or proj) cannot be further transformed into a tree"; 
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
    -- dbg_trace f!"{computation.distance} {tree.numberOfNodes} {lemTree.numberOfNodes} {tree} \n {lemTree}"
    (currentDistance, currentMinimizer) := nextLibraryMatch currentDistance computation.distance currentMinimizer lem    
  pure currentMinimizer