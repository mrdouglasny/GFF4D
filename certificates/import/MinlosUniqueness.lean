import OSforGFF.BochnerDefs
import certificates.CertificateSchema

/-!
# Import Certificate: minlos_uniqueness

## Metadata
- **Axiom**: `minlos_uniqueness`
- **Role**: Import
- **Status**: Verified
- **Method**: LeanProof
- **Date**: 2026-03-04

## Source
- **Repository**: https://github.com/mrdouglasny/bochner
- **Commit**: 3a5c8fc
- **File**: Minlos/Main.lean
- **Declaration**: `minlos_uniqueness`

## Proof Summary
Uniqueness of the probability measure follows from injectivity of the characteristic
functional on probability measures over nuclear spaces (Lévy continuity theorem
generalized to infinite dimensions).

## Type Correspondence
The axiom uses `BochnerPD` (= bochner's `IsPositiveDefinite`) and `IsHilbertNuclear`
(= bochner's class), both defined locally in `OSforGFF.BochnerDefs` with matching types.

## SHA-256
HASH: 256104b7a493474a95f442097381f8e6f2f8dbfd853cf487a5e3b30cdad287b8
-/

open MeasureTheory Complex TopologicalSpace in
set_option checkBinderAnnotations false in
-- Restate the axiom's type — compilation fails if the axiom declaration changes
example {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [IsHilbertNuclear E] [SeparableSpace E] [Nonempty E]
    {Φ : E → ℂ} (hΦ_cont : Continuous Φ)
    (hΦ_pd : BochnerPD Φ) (hΦ_norm : Φ 0 = 1)
    {μ₁ μ₂ : ProbabilityMeasure (WeakDual ℝ E)}
    (h₁ : ∀ f : E, ∫ ω, exp (I * ((ω : E →L[ℝ] ℝ) f)) ∂μ₁.toMeasure = Φ f)
    (h₂ : ∀ f : E, ∫ ω, exp (I * ((ω : E →L[ℝ] ℝ) f)) ∂μ₂.toMeasure = Φ f) :
    μ₁ = μ₂ :=
  minlos_uniqueness hΦ_cont hΦ_pd hΦ_norm h₁ h₂

def minlos_uniqueness_cert : CertificateInfo where
  axiomName      := "minlos_uniqueness"
  statement      := "μ₁ = μ₂ (same char functional → same measure)"
  role           := .Import
  status         := .Verified
  method         := .LeanProof
  sources        := [{
    repo         := some "https://github.com/mrdouglasny/bochner",
    commit       := some "3a5c8fc",
    file         := some "Minlos/Main.lean",
    leanName     := some "minlos_uniqueness"
  }]
  proofSummary   := some "Injectivity of characteristic functional on probability measures over nuclear spaces"
  date           := "2026-03-04"
  sourceHash     := some "5edcbac6101490370c7469e28321de758f837a2d33111dcefcdb10290b4d92d1"
  migrationTargets := [{
    repo     := "https://github.com/leanprover-community/mathlib4",
    leanName := some "minlos_uniqueness"
  }]
