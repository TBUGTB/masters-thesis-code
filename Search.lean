import Lean
import SyntacticSimilarity
import Aesop

open Lean HoleTree Lean.Meta Lean.Elab.Tactic

def marker (s : String) : Expr := .mdata (MData.empty.insert "marker" s) default 

def unfoldArguments : Expr → Expr × List Expr
  | Expr.app f x => let (function, arguments) := unfoldArguments f
                    (function, arguments ++ [x]) 
  | e => (e, [])

partial def Lean.Expr.toHoleTree : Expr → MetaM (Tree Expr)  
  | Expr.const declName us => pure <| Tree.leaf (.const declName us)
  | Expr.fvar fvarId =>  pure <| Tree.leaf (.fvar fvarId)
  | Expr.mvar mvarId =>  pure <| Tree.leaf (.mvar mvarId)
  | Expr.lit x =>  pure <| Tree.leaf (Expr.lit x)
  | Expr.sort u =>  pure <| Tree.leaf (Expr.sort u)
  | Expr.app f x => do 
      let (function, arguments) := unfoldArguments (Expr.app f x)
      let functionAsTree ← function.toHoleTree
      let argumentsAsTrees ← arguments.mapM Expr.toHoleTree 
      pure <| Tree.node (marker "app") (functionAsTree :: argumentsAsTrees) 
  | Expr.forallE binderName binderType b binderInfo => do 
      let (mvars, _, body) ← forallMetaTelescopeReducing <| Expr.forallE binderName binderType b binderInfo
      let bodyAsTree ← body.toHoleTree
      let mvarList := mvars.toList  
      let mvarTypes ← mvarList.mapM inferType
      let mvarTypesAsTrees ← mvarTypes.mapM Expr.toHoleTree
      pure <| Tree.node (marker "forall") (mvarTypesAsTrees ++ [bodyAsTree])
  | Expr.lam binderName binderType b binderInfo => do 
      let (_, _, body) ← lambdaMetaTelescope <| Expr.lam binderName binderType b binderInfo
      let bodyTree ← body.toHoleTree
      pure <| Tree.node (marker "lambda") [bodyTree] 
  | Expr.bvar _ => panic! "Unbound bvar in expression"
  | Expr.mdata _ e => e.toHoleTree
  | Expr.letE _ (type : Expr) (value : Expr) (body : Expr) _ => do
      pure <| Tree.node (marker "let") [← type.toHoleTree, ← value.toHoleTree, ← body.toHoleTree]
  | Expr.proj _ (idx : Nat) (struct : Expr) => do 
      pure <| Tree.node (marker s!"proj {idx}") [← struct.toHoleTree]

def createHoleTreeFromLemmaExpr (l : Lean.Expr) : MetaM (Tree Expr) := do 
  let lemmaType ← Lean.Meta.inferType l
  let reduced ← withTransparency .instances $ reduceAll lemmaType
  pure (← reduced.toHoleTree)

def idxOfBestSyntacticLibraryMatch (e : Expr) (libraryLemmas : Array Expr) : MetaM Nat := do
  let goalAsHoleTree ← e.toHoleTree
  let lemmasAsHoleTrees ← libraryLemmas.mapM createHoleTreeFromLemmaExpr
  let lemmasAsHoleTreesList := lemmasAsHoleTrees.toList
  let indexOfBestMatch := SyntacticSimilarity.indexOfMinimalDistanceTree goalAsHoleTree lemmasAsHoleTreesList
  pure indexOfBestMatch

open Lean Elab 

def evalAesopWithLemmaAsUnsafeRule (lemmaName : Name) : TacticM Unit := do
  dbg_trace lemmaName
  let identifier := mkIdent lemmaName
  Tactic.evalTactic (← `(tactic| aesop (add unsafe $identifier:ident)))

elab "aesop_with_search" "[" lemmas:term,* "]" : tactic => 
  Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let type ← goal.getType
  let reduced ← withTransparency .instances $ reduceAll type

  let lemmasAsExpr ← lemmas.getElems.mapM (fun x => elabTerm x none)

  let idxOfBestMatch ← idxOfBestSyntacticLibraryMatch reduced lemmasAsExpr
  let bestMatch := lemmasAsExpr[idxOfBestMatch]!

  match bestMatch with 
  | .const name _ => evalAesopWithLemmaAsUnsafeRule name
  | .app f arg => let (function, _) := unfoldArguments (.app f arg)
                  dbg_trace function
                  match function with 
                  | .const name _ => evalAesopWithLemmaAsUnsafeRule name
                  | _ => pure ()
  | _ => pure () 