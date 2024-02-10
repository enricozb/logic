import Lake
open Lake DSL

package «logic» where
  -- add package configuration options here

lean_lib «Logic» where
  -- add library configuration options here

@[default_target]
lean_exe «logic» where
  root := `Main

-- a mathlib version that uses lean-toolchain 4.5.0
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "feec58a7"
