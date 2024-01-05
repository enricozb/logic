import Lake
open Lake DSL

package «logic» where
  -- add package configuration options here

lean_lib «Logic» where
  -- add library configuration options here

@[default_target]
lean_exe «logic» where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"
