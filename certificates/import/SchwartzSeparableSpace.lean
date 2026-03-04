import OSforGFF.GaussianFieldBridge
import certificates.CertificateSchema

/-!
# Import Certificate: schwartz_separableSpace

## Metadata
- **Axiom**: `schwartz_separableSpace`
- **Role**: Import
- **Status**: Verified
- **Method**: LeanProof
- **Date**: 2026-03-04

## Source
- **Repository**: https://github.com/mrdouglasny/gaussian-field
- **Commit**: 8bf42cd4a027e3176a3a679d02dee68be4cba0e1
- **File**: SchwartzNuclear/HermiteNuclear.lean
- **Declaration**: `GaussianField.schwartz_separableSpace`

## Proof Summary
RapidDecaySeq is separable because the countable set {basisVec m | m ∈ ℕ} spans
a dense subspace (every element is the limit of finite linear combinations by
hasSum_basisVec). Schwartz space inherits separability via the CLE
schwartzRapidDecayEquiv, since a homeomorphism preserves separability.

## Type Correspondence
The axiom specializes the generic `SeparableSpace (SchwartzMap D ℝ)` instance
to `TestFunction = SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℝ`.

## SHA-256
HASH: e36d94161fd64b1e07676486b89a706a38f60ca5de91728e24d9eead3ef7b2e8
-/

open GaussianFieldBridge TopologicalSpace in
-- Restate the axiom's type — compilation fails if the axiom declaration changes
example : SeparableSpace TestFunction := schwartz_separableSpace

def schwartz_separableSpace_cert : CertificateInfo where
  axiomName      := "schwartz_separableSpace"
  statement      := "SeparableSpace TestFunction"
  role           := .Import
  status         := .Verified
  method         := .LeanProof
  sources        := [{
    repo         := some "https://github.com/mrdouglasny/gaussian-field",
    commit       := some "8bf42cd4a027e3176a3a679d02dee68be4cba0e1",
    file         := some "SchwartzNuclear/HermiteNuclear.lean",
    leanName     := some "GaussianField.schwartz_separableSpace"
  }]
  proofSummary   := some "Hermite basis spans dense subspace of RapidDecaySeq → separable, transferred via CLE"
  date           := "2026-03-04"
  migrationTargets := [{
    repo     := "https://github.com/leanprover-community/mathlib4",
    leanName := some "SchwartzMap.separableSpace"
  }]
