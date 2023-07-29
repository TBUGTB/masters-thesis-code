import Lean
import SyntacticSimilarity

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
                    pure <| Tree.node (marker "app") [← f.toHoleTree, ← x.toHoleTree]
                    -- let (function, arguments) := unfoldArguments (Expr.app f x)
                    -- let argumentsAsTrees ← arguments.mapM Expr.toHoleTree 
                    -- pure <| Tree.node (function) argumentsAsTrees 
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
  | x => dbg_trace "Unsupported Lean.Expr constructor (let or proj) cannot be further transformed into a tree"; 
        pure <| .leaf x

def createHoleTreeFromLemmaName (name : Lean.Name) : MetaM (Tree Expr) := do 
  let lemmaAsConstant ← mkConstWithFreshMVarLevels name
  let lemmaExpr ← Lean.Meta.inferType lemmaAsConstant
  let reduced ← withTransparency .instances $ reduceAll lemmaExpr
  pure (← reduced.toHoleTree)

def bestSyntacticLibraryMatch (e : Expr) (libraryLemmas : List Name) : MetaM Name := do
  let goalAsHoleTree ← e.toHoleTree
  let lemmasAsHoleTrees ← libraryLemmas.mapM createHoleTreeFromLemmaName
  let indexOfBestMatch := SyntacticSimilarity.indexOfMinimalDistanceTree goalAsHoleTree lemmasAsHoleTrees
  let bestMatch := libraryLemmas[indexOfBestMatch]!
  pure bestMatch