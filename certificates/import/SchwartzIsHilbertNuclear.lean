import OSforGFF.GaussianFieldBridge
import certificates.CertificateSchema

/-!
# Import Certificate: schwartz_isHilbertNuclear

## Metadata
- **Axiom**: `schwartz_isHilbertNuclear`
- **Role**: Import
- **Status**: Verified
- **Method**: LeanProof
- **Date**: 2026-03-04

## Source
- **Repository**: https://github.com/mrdouglasny/gaussian-field
- **Commit**: 8bf42cd4a027e3176a3a679d02dee68be4cba0e1
- **File**: SchwartzNuclear/HermiteNuclear.lean
- **Declaration**: `GaussianField.schwartz_isHilbertNuclear`

## Proof Summary
Schwartz space is Hilbert-nuclear via the chain:
  DyninMityaginSpace (Hermite basis on SchwartzMap D ℝ)
  → NuclearSpace (Pietsch nuclear dominance)
  → IsNuclear (bochner bridge: ‖·‖ = |·| for ℝ)
  → IsHilbertNuclear (Hilbertian lift + Bessel inequality)
transferred along SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq.

## Type Correspondence
The axiom specializes the generic `IsHilbertNuclear (SchwartzMap D ℝ)` instance
to `TestFunction = SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℝ`.

## Migration Targets
- **mathlib4**: expected as part of Schwartz space nuclearity theory

## SHA-256
HASH: c95ade54d00d7f34f870ed5a9652f22fd1caaaa9c7d2bb88ea2afbca9e0d9ca8
-/

open GaussianFieldBridge in
-- Restate the axiom's type — compilation fails if the axiom declaration changes
example : IsHilbertNuclear TestFunction := schwartz_isHilbertNuclear

def schwartz_isHilbertNuclear_cert : CertificateInfo where
  axiomName      := "schwartz_isHilbertNuclear"
  statement      := "IsHilbertNuclear TestFunction"
  role           := .Import
  status         := .Verified
  method         := .LeanProof
  sources        := [{
    repo         := some "https://github.com/mrdouglasny/gaussian-field",
    commit       := some "8bf42cd4a027e3176a3a679d02dee68be4cba0e1",
    file         := some "SchwartzNuclear/HermiteNuclear.lean",
    leanName     := some "GaussianField.schwartz_isHilbertNuclear"
  }]
  proofSummary   := some "DyninMityaginSpace → NuclearSpace → IsNuclear → IsHilbertNuclear, via CLE transfer"
  date           := "2026-03-04"
  migrationTargets := [{
    repo     := "https://github.com/leanprover-community/mathlib4",
    leanName := some "SchwartzMap.isHilbertNuclear"
  }]
