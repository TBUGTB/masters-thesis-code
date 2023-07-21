import Std.Data.HashMap
-- import SyntacticSimilarity.LeastCommonGeneralizer

open Lean

universe u v

structure Cache (α : Type u) (β : Type v) where 
  cache : List (α × Option β)
  deriving Repr

instance : Inhabited (Cache α β) where 
  default := { cache := [] }

def emptyCache : Cache α β := default

def getFromCache [BEq α] (key : α) : StateM (Cache α β) (Option β) := do 
  let (keys, values) := (← get).cache.unzip
  if keys.contains key then 
    let keyIdx := keys.indexOf key
    let value := values[keyIdx]? >>= fun x => x
    pure value
  else 
    pure none

def saveToCache [BEq α] (key : α) (val : β) : StateM (Cache α β) PUnit := do 
  let currentCache := (← get).cache
  let newCache := (key, some val) :: currentCache 
  modify (fun s => {s with cache := newCache})   

def StateM.run {σ : Type u} {α : Type u} (x : StateM σ α) (s : σ) : (α × σ) :=
  x s
