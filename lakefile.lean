import Lake
open Lake DSL

package «lean4» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
    
lean_lib Util {
  -- add any library configuration options here
}

lean_lib HoleTree {
  -- add any library configuration options here
}

lean_lib Matchings {
  -- add any library configuration options here
}

lean_lib ReferenceImplementation {
  -- add any library configuration options here
}

lean_lib Search {
  -- add any library configuration options here
}

lean_lib NaiveCache {
  -- add any library configuration options here
}

lean_lib IncompleteMatchings {
  -- add any library configuration options here
}

lean_lib SyntacticSimilarity {
  -- add any library configuration options here
}