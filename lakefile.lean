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

@[default_target]
lean_lib «OSforGFF» where
  -- add any library configuration options here

lean_lib «certificates» where
  roots := #[`certificates.CertificateSchema,
             `certificates.import.SchwartzIsHilbertNuclear,
             `certificates.import.SchwartzSeparableSpace,
             `certificates.import.MinlosTheorem,
             `certificates.import.MinlosUniqueness]
