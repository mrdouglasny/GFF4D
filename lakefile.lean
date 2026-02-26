import Lake
open Lake DSL

package «OSforGFF» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "19564be93e1"

require GaussianField from git
  "https://github.com/mrdouglasny/gaussian-field.git" @ "b83d0bb1b75"

@[default_target]
lean_lib «OSforGFF» where
  -- add any library configuration options here
