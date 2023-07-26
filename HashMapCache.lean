import Std.Data.HashMap.Basic

open Lean

universe u v

structure Cache (α β : Type) [BEq α] [Hashable α] where 
  cache : Std.HashMap α β

instance {α β : Type} [BEq α] [Hashable α] : Inhabited (Cache α β) where 
  default := { cache := Std.HashMap.empty  }

def emptyCache [BEq α] [Hashable α] : Cache α β := default

def getFromCache {α β : Type} [BEq α] [Hashable α] 
  (key : α) : StateM (Cache α β) (Option β) := do 
  pure $ (← get).cache.find? key

def saveToCache {α β : Type} [BEq α] [Hashable α] (key : α) (val : β) : StateM (Cache α β) PUnit := do  
  modify (fun s => {s with cache := s.cache.insert key val})   