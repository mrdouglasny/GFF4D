import OSforGFF.BochnerDefs
import certificates.CertificateSchema

/-!
# Import Certificate: minlos_theorem

## Metadata
- **Axiom**: `minlos_theorem`
- **Role**: Import
- **Status**: Verified
- **Method**: LeanProof
- **Date**: 2026-03-04

## Source
- **Repository**: https://github.com/mrdouglasny/bochner
- **Commit**: 3a5c8fc
- **File**: Minlos/Main.lean
- **Declaration**: `minlos_theorem`

## Proof Summary
Minlos theorem proved via projective limit construction on cylinder sets of the
nuclear dual space, using Kolmogorov extension and Hilbert-Schmidt nuclearity
conditions to verify the σ-additivity (Bochner-Minlos conditions).

## Type Correspondence
The axiom uses `BochnerPD` (= bochner's `IsPositiveDefinite`) and `IsHilbertNuclear`
(= bochner's class), both defined locally in `OSforGFF.BochnerDefs` with matching types.

## SHA-256
HASH: c815af08200ab69f02a3a889c5a44010ec870366f14664039a4cc01052d71272
-/

open MeasureTheory Complex TopologicalSpace in
set_option checkBinderAnnotations false in
-- Restate the axiom's type — compilation fails if the axiom declaration changes
example {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [IsHilbertNuclear E] [SeparableSpace E] [Nonempty E]
    (Φ : E → ℂ) (h_continuous : Continuous Φ)
    (h_positive_definite : BochnerPD Φ) (h_normalized : Φ 0 = 1) :
    ∃! μ : ProbabilityMeasure (WeakDual ℝ E),
      ∀ f : E, Φ f = ∫ ω, exp (I * ((ω : E →L[ℝ] ℝ) f)) ∂μ.toMeasure :=
  minlos_theorem Φ h_continuous h_positive_definite h_normalized

def minlos_theorem_cert : CertificateInfo where
  axiomName      := "minlos_theorem"
  statement      := "∃! μ : ProbabilityMeasure (WeakDual ℝ E), ∀ f, Φ f = ∫ ω, exp(i·ω(f)) dμ"
  role           := .Import
  status         := .Verified
  method         := .LeanProof
  sources        := [{
    repo         := some "https://github.com/mrdouglasny/bochner",
    commit       := some "3a5c8fc",
    file         := some "Minlos/Main.lean",
    leanName     := some "minlos_theorem"
  }]
  proofSummary   := some "Projective limit on cylinder sets + Kolmogorov extension + Hilbert-Schmidt nuclearity"
  date           := "2026-03-04"
  sourceHash     := some "3500270934dac553678d495c2584a3fff71233e0fa9236e445f2b0421e27237e"
  migrationTargets := [{
    repo     := "https://github.com/leanprover-community/mathlib4",
    leanName := some "minlos_theorem"
  }]
