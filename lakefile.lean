import Lake
open Lake DSL

package «OSforGFF» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "6dc31c12d6f"

require BochnerMinlos from git
  "https://github.com/mrdouglasny/bochner.git" @ "3a5c8fc"

@[default_target]
lean_lib «OSforGFF» where
  -- add any library configuration options here
