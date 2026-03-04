/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import OSforGFF.PositiveDefinite
import OSforGFF.GaussianRBF
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
-- Bochner/Minlos imports (proven theorems, replacing former axioms)
import Minlos.Main
import Minlos.PietschBridge

/-!
Minlos Theorem and Bochner's Theorem

This file connects the GFF4D project to the bochner library's proven Minlos theorem.
The `minlos_theorem` and `minlos_uniqueness` axioms that were previously in this file
have been replaced by imports from the bochner library, which provides fully proven
versions (0 sorries, 0 axioms).

Key results:
- Bridge lemmas converting GFF4D's types to bochner's types
- gaussian_characteristic_functional: Gaussian CF definition
- gaussian_positive_definite_via_embedding: PD of Gaussian CF
- minlos_gaussian_construction: Minlos applied to Gaussian measures
- gaussian_measure_symmetry: Symmetry transfer via uniqueness
-/

open Complex MeasureTheory Matrix
open BigOperators

noncomputable section

/-! ## Axioms in this file

This file contains the following axioms (see `texts/axioms.txt` for justification):
- `schwartz_nuclear`: Schwartz space is nuclear (Gel'fand-Vilenkin, Trèves)
- `bochner_Rn`: Bochner's theorem in finite dimensions
- `levy_cf_uniqueness_Rn`: Lévy uniqueness for ℝⁿ

Previously axioms, now proven via bochner library:
- `minlos_theorem`: Minlos theorem for nuclear spaces (bochner: Minlos.Main)
- `minlos_uniqueness`: uniqueness for Minlos measures (bochner: Minlos.Main)

Previously an axiom, now proven in GaussianRBF.lean:
- `gaussian_rbf_pd_innerProduct_proof`: Gaussian RBF kernel is positive definite
  (NOTE: Requires inner product space, NOT just normed space - see Schoenberg's theorem)
-/

/-! ## Positive Definiteness -/

-- `GFF4D.IsPositiveDefinite` (nonneg-only) is defined in `OSforGFF.PositiveDefinite`
-- `IsPositiveDefinite` (hermitian + nonneg, structure) comes from bochner's `Bochner.PositiveDefinite`

/-! ## Bridge: GFF4D's nonneg PD → bochner's full PD for real-valued functions

For real-valued positive definite functions φ : α → ℝ (viewed as φ : α → ℂ via cast),
the hermitian condition φ(-x) = conj(φ(x)) is automatic because conj acts as identity
on reals. More generally, for functions of the form exp(r(x)) where r : α → ℝ,
the hermitian condition follows from r(-x) = r(x) (even function). -/

/-- For a function φ : α → ℂ that is real-valued (im = 0) and satisfies φ(-x) = φ(x),
    GFF4D's nonneg PD implies bochner's full PD. -/
lemma gff4d_to_bochner_pd {α : Type*} [AddGroup α] (φ : α → ℂ)
    (h_nonneg : GFF4D.IsPositiveDefinite φ)
    (h_hermitian : ∀ x : α, φ (-x) = starRingEnd ℂ (φ x)) :
    IsPositiveDefinite φ where
  hermitian := h_hermitian
  nonneg := h_nonneg

/-! ## Minlos Theorem

The Minlos theorem is now imported from bochner's `Minlos.Main`:
- `minlos_theorem`: existence and uniqueness (requires `IsHilbertNuclear`, `SeparableSpace`, `Nonempty`)
- `minlos_uniqueness`: derived uniqueness result

Nuclear space types:
- bochner uses `IsHilbertNuclear` (Gel'fand-Vilenkin: Hilbertian seminorms + HS embeddings)
- gaussian-field uses `NuclearSpace` (Pietsch: nuclear dominance)
- Bridge: `isHilbertNuclear_of_nuclear` in bochner's PietschBridge.lean
-/

/-! ## MeasurableSpace bridge

GFF4D's `MeasurableSpace FieldConfiguration` uses `comap (fun ω f => ω f) pi`,
while bochner uses `⨆ f, (borel ℝ).comap (eval f)`. Both are cylinder σ-algebras
and propositionally equal, but not definitionally equal. This bridge allows converting
between the two. -/

/-- The comap-pi cylinder σ-algebra on WeakDual equals bochner's ⨆-comap definition. -/
lemma measurableSpace_comap_eq_bochner {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] :
    MeasurableSpace.comap (fun ω : WeakDual ℝ E => fun f : E => ω f) MeasurableSpace.pi =
    (⨆ (f : E), (borel ℝ).comap (fun l : WeakDual ℝ E => (l : E →L[ℝ] ℝ) f)) := by
  unfold MeasurableSpace.pi
  rw [MeasurableSpace.comap_iSup]
  congr 1; ext φ
  rw [MeasurableSpace.comap_comp]

/-! ## Applications to Gaussian Free Fields -/

/-- For Gaussian measures, the characteristic functional has the special form
    Φ(f) = exp(-½⟨f, Cf⟩) where C is a nuclear covariance operator. -/
def gaussian_characteristic_functional
  {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  (covariance_form : E → E → ℝ) (f : E) : ℂ :=
  Complex.exp (-(1/2 : ℂ) * (covariance_form f f))

-- `GFF4D.isPositiveDefinite_precomp_linear` is in `OSforGFF.PositiveDefinite`

/-- **Gaussian RBF kernel is positive definite on inner product spaces.**

    For an inner product space H, the function φ(h) = exp(-½‖h‖²) is positive definite.

    **PROVEN** in `OSforGFF/GaussianRBF.lean` using:
    - The inner product kernel is PD
    - Exponential preserves PD (via Hadamard series and Schur product theorem)
    - Factorization: exp(-½|x-y|²) = exp(-½|x|²)·exp(-½|y|²)·exp(⟨x,y⟩) -/
theorem gaussian_rbf_pd_innerProduct
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
  GFF4D.IsPositiveDefinite (fun h : H => Complex.exp (-(1/2 : ℂ) * (‖h‖^2 : ℝ))) :=
  gaussian_rbf_pd_innerProduct_proof

/-- The Gaussian RBF exp(-½‖h‖²) satisfies bochner's full PD condition
    (hermitian + nonneg) on inner product spaces.

    Hermiticity: exp(-½‖-h‖²) = exp(-½‖h‖²) (since ‖-h‖ = ‖h‖),
    and conj(exp(-½‖h‖²)) = exp(-½‖h‖²) (since the exponent is real). -/
theorem gaussian_rbf_pd_bochner
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
  IsPositiveDefinite (fun h : H => Complex.exp (-(1/2 : ℂ) * (‖h‖^2 : ℝ))) := by
  apply gff4d_to_bochner_pd
  · exact gaussian_rbf_pd_innerProduct_proof
  · intro h
    rw [norm_neg, ← Complex.exp_conj]
    congr 1
    -- Rewrite the argument as a single real cast, then conj_ofReal
    have : (-(1/2 : ℂ) * (‖h‖^2 : ℝ)) = ((-(1/2 : ℝ) * ‖h‖^2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.conj_ofReal]

/-- If covariance is realized as a squared norm via a linear embedding T into
    a real inner product space H, then the Gaussian characteristic functional
    is positive definite (in GFF4D's nonneg sense).

    **Note**: We require H to be an inner product space (not just normed space)
    because the Gaussian RBF kernel is only guaranteed positive definite for
    Hilbert spaces, not general Banach spaces. -/
lemma gaussian_positive_definite_via_embedding
  {E H : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (T : E →ₗ[ℝ] H)
  (covariance_form : E → E → ℝ)
  (h_eq : ∀ f, covariance_form f f = (‖T f‖^2 : ℝ)) :
  GFF4D.IsPositiveDefinite (fun f => Complex.exp (-(1/2 : ℂ) * (covariance_form f f))) := by
  -- Reduce to Gaussian RBF on H and precomposed with T
  have hPD_H := gaussian_rbf_pd_innerProduct (H := H)
  -- Compose with T and rewrite using h_eq
  intro m x c
  have repl : ∀ i j,
      covariance_form (x i - x j) (x i - x j)
      = (‖T (x i - x j)‖^2 : ℝ) := by
    intro i j; simpa using h_eq (x i - x j)
  have hlin : ∀ i j, T (x i - x j) = T (x i) - T (x j) := by
    intro i j; simp [LinearMap.map_sub]
  have hnorm : ∀ i j, (‖T (x i - x j)‖^2 : ℝ) = (‖T (x i) - T (x j)‖^2 : ℝ) := by
    intro i j; simp [hlin i j]
  -- Apply PD of Gaussian on H precomposed with T
  have hPD_comp :
    0 ≤ (∑ i, ∑ j,
      (starRingEnd ℂ) (c i) * c j *
        Complex.exp (-(1/2 : ℂ) * ((‖T (x i) - T (x j)‖^2 : ℝ)))).re := by
    simpa using (GFF4D.isPositiveDefinite_precomp_linear
      (ψ := fun h : H => Complex.exp (-(1/2 : ℂ) * (‖h‖^2 : ℝ))) hPD_H T) m x c
  -- Rewrite differences inside T using linearity
  have hPD_comp1 :
    0 ≤ (∑ i, ∑ j,
      (starRingEnd ℂ) (c i) * c j *
        Complex.exp (-(1/2 : ℂ) * ((‖T (x i - x j)‖^2 : ℝ)))).re := by
    simpa [LinearMap.map_sub] using hPD_comp
  -- Finally rewrite norm-squared via covariance_form equality
  have : 0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
      Complex.exp (-(1/2 : ℂ) * (covariance_form (x i - x j) (x i - x j)))).re := by
    simpa [repl] using hPD_comp1
  exact this

/-- The Gaussian CF satisfies bochner's full PD condition when covariance
    is realized via a linear embedding into a Hilbert space.
    This is the version needed by bochner's `minlos_theorem`. -/
lemma gaussian_positive_definite_bochner
  {E H : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (T : E →ₗ[ℝ] H)
  (covariance_form : E → E → ℝ)
  (h_eq : ∀ f, covariance_form f f = (‖T f‖^2 : ℝ))
  (h_symm_covar : ∀ f, covariance_form (-f) (-f) = covariance_form f f) :
  IsPositiveDefinite (fun f => Complex.exp (-(1/2 : ℂ) * (covariance_form f f))) := by
  apply gff4d_to_bochner_pd
  · exact gaussian_positive_definite_via_embedding T covariance_form h_eq
  · intro x
    simp only [h_symm_covar]
    rw [← Complex.exp_conj]
    congr 1
    have : (-(1/2 : ℂ) * (covariance_form x x : ℂ)) = ((-(1/2 : ℝ) * covariance_form x x : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.conj_ofReal]

/-- Application of Minlos theorem to Gaussian measures.
    If the covariance form can be realized as a squared norm via a linear embedding T into
    a real inner product space H, then the Gaussian characteristic functional Φ(f) = exp(-½⟨f, Cf⟩)
    satisfies the conditions of Minlos theorem, yielding a Gaussian probability measure on E'.

    **Note**: We require H to be an inner product space (not just normed) because the
    Gaussian RBF kernel is only positive definite for Hilbert spaces. -/
theorem minlos_gaussian_construction
  {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [IsHilbertNuclear E] [TopologicalSpace.SeparableSpace E] [Nonempty E]

  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (T : E →ₗ[ℝ] H)
  (covariance_form : E → E → ℝ)
  (h_eq : ∀ f, covariance_form f f = (‖T f‖^2 : ℝ))
  (_h_nuclear : True)
  (h_zero : covariance_form 0 0 = 0)
  (h_continuous : Continuous (fun f => covariance_form f f))
  : ∃ μ : Measure (WeakDual ℝ E), IsProbabilityMeasure μ ∧
    (∀ f : E, gaussian_characteristic_functional covariance_form f =
              ∫ ω, Complex.exp (I * (ω f)) ∂μ) := by
  -- Build bochner's PD from the embedding
  have h_pd : IsPositiveDefinite (gaussian_characteristic_functional covariance_form) := by
    apply gff4d_to_bochner_pd
    · exact gaussian_positive_definite_via_embedding T covariance_form h_eq
    · intro x
      simp only [gaussian_characteristic_functional]
      -- covariance_form (-x) (-x) = ‖T(-x)‖² = ‖-(Tx)‖² = ‖Tx‖² = covariance_form x x
      have h_neg : covariance_form (-x) (-x) = covariance_form x x := by
        rw [h_eq, h_eq, map_neg, norm_neg]
      simp only [h_neg]
      rw [← Complex.exp_conj]
      congr 1
      have : (-(1/2 : ℂ) * (covariance_form x x : ℂ)) = ((-(1/2 : ℝ) * covariance_form x x : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, Complex.conj_ofReal]
  -- Apply bochner's Minlos theorem
  have h_cont : Continuous (gaussian_characteristic_functional covariance_form) := by
    have h_covar_continuous : Continuous (fun f => (covariance_form f f : ℂ)) :=
      Continuous.comp continuous_ofReal h_continuous
    have h_scaled_continuous : Continuous (fun f => -(1/2 : ℂ) * (covariance_form f f : ℂ)) :=
      Continuous.mul continuous_const h_covar_continuous
    exact Continuous.comp continuous_exp h_scaled_continuous
  have h_norm : gaussian_characteristic_functional covariance_form 0 = 1 := by
    simp [gaussian_characteristic_functional, h_zero]
  obtain ⟨μ, hμ⟩ := (minlos_theorem
    (gaussian_characteristic_functional covariance_form) h_cont h_pd h_norm).exists
  exact ⟨μ.toMeasure, μ.property, hμ⟩

/-- The measure constructed by Minlos theorem for a Gaussian characteristic functional
    indeed has that functional as its characteristic function. -/
theorem gaussian_measure_characteristic_functional
  {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [IsHilbertNuclear E] [TopologicalSpace.SeparableSpace E] [Nonempty E]

  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (T : E →ₗ[ℝ] H)
  (covariance_form : E → E → ℝ)
  (h_eq : ∀ f, covariance_form f f = (‖T f‖^2 : ℝ))
  (h_nuclear : True)
  (h_zero : covariance_form 0 0 = 0)
  (h_continuous : Continuous (fun f => covariance_form f f))
  : ∃ μ : ProbabilityMeasure (WeakDual ℝ E),
    (∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ.toMeasure =
              gaussian_characteristic_functional covariance_form f) := by
  -- Get the measure from minlos_gaussian_construction
  have h_minlos := minlos_gaussian_construction T covariance_form h_eq h_nuclear h_zero h_continuous
  obtain ⟨μ, hprob, hchar⟩ := h_minlos
  -- Convert to ProbabilityMeasure and apply the result
  use ⟨μ, hprob⟩
  intro f
  exact (hchar f).symm

/-! ## Symmetry Transfer from Characteristic Functional to Measure

The key insight: if a linear transformation preserves the characteristic functional,
then by Minlos uniqueness, the corresponding measure is invariant under the induced
action on the dual space.

This is crucial for establishing Euclidean invariance (OS2) of the GFF:
if the covariance is Euclidean-invariant, then exp(-½⟨gf, C(gf)⟩) = exp(-½⟨f, Cf⟩),
and by uniqueness the measure is Euclidean-invariant. -/

/-- Corollary for Gaussian measures: if the covariance form is invariant under g,
    then the Gaussian measure is invariant under the dual action of g.

    This directly implies OS2 (Euclidean invariance) for the GFF when g is a
    Euclidean transformation and the covariance satisfies C(gf, gh) = C(f, h). -/
theorem gaussian_measure_symmetry
  {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [IsHilbertNuclear E] [TopologicalSpace.SeparableSpace E] [Nonempty E]

  (covariance_form : E → E → ℝ)
  (μ : ProbabilityMeasure (WeakDual ℝ E))
  (h_char : ∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ.toMeasure =
                     gaussian_characteristic_functional covariance_form f)
  (g : E →L[ℝ] E)
  (h_covar_symm : ∀ f : E, covariance_form (g f) (g f) = covariance_form f f)
  -- Properties needed for Minlos uniqueness (Gaussian CF is continuous, PD, normalized)
  (h_cf_cont : Continuous (gaussian_characteristic_functional covariance_form))
  (h_cf_pd : IsPositiveDefinite (gaussian_characteristic_functional covariance_form))
  (h_cf_norm : gaussian_characteristic_functional covariance_form 0 = 1)
  -- The pushforward measure under the dual action
  (μ_push : ProbabilityMeasure (WeakDual ℝ E))
  (h_push_char : ∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ_push.toMeasure =
                          ∫ ω, Complex.exp (I * (ω (g f))) ∂μ.toMeasure)
  : μ_push = μ := by
  -- The Gaussian CF is g-invariant when covariance is
  have h_Φ_symm : ∀ f, gaussian_characteristic_functional covariance_form (g f) =
                       gaussian_characteristic_functional covariance_form f := by
    intro f
    simp only [gaussian_characteristic_functional, h_covar_symm]
  -- Apply bochner's minlos_uniqueness with the Gaussian CF as Φ
  exact minlos_uniqueness h_cf_cont h_cf_pd h_cf_norm
    (fun f => (h_push_char f).trans ((h_char (g f)).trans (h_Φ_symm f)))
    h_char

end
