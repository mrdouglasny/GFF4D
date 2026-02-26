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
import Nuclear.NuclearSpace
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Minlos Theorem and Bochner's Theorem

This file contains foundational results for constructing infinite-dimensional Gaussian measures,
including Bochner's theorem for finite dimensions and the Minlos theorem for nuclear spaces.

Key results:
- IsPositiveDefinite: Definition of positive-definite functions
- bochner_Rn: Bochner's theorem in finite dimensions (characteristic functions)
- Future: Minlos theorem for infinite-dimensional construction
-/

open Complex MeasureTheory Matrix GaussianField
open BigOperators

noncomputable section

/-! ## Axioms in this file

This file contains the following axioms (see `texts/axioms.txt` for justification):
- `schwartz_nuclear`: Schwartz space is nuclear (Gel'fand-Vilenkin, Trèves)
- `minlos_theorem`: Minlos theorem for nuclear spaces
- `minlos_uniqueness`: uniqueness for Minlos measures (used locally)
- `bochner_Rn`: Bochner's theorem in finite dimensions
- `levy_cf_uniqueness_Rn`: Lévy uniqueness for ℝⁿ

Previously an axiom, now proven in GaussianRBF.lean:
- `gaussian_rbf_pd_innerProduct_proof`: Gaussian RBF kernel is positive definite
  (NOTE: Requires inner product space, NOT just normed space - see Schoenberg's theorem)
-/

/-! ## Positive Definiteness -/

-- `IsPositiveDefinite` is now defined in `OSforGFF.PositiveDefinite`

/-! ## Minlos Theorem

Nuclear space definitions (`NuclearSpace`, `IsNuclearMap`, `schwartz_nuclear`, etc.)
are in `OSforGFF.NuclearSpace`. -/

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [MeasurableSpace (WeakDual ℝ E)]

/-- **Minlos Theorem**: Existence of infinite-dimensional probability measures.

    Let E be a nuclear locally convex space and let Φ : E → ℂ be a characteristic functional.
    If Φ is:
    1. Continuous (with respect to the nuclear topology on E)
    2. Positive definite (in the sense of Bochner)
    3. Normalized: Φ(0) = 1

    Then there exists a unique probability measure μ on the topological dual E'
    (equipped with the weak* topology) such that:

    Φ(f) = ∫_{E'} exp(i⟨f,ω⟩) dμ(ω)

    **Applications**:
    - For E = S(ℝᵈ) (Schwartz space), E' = S'(ℝᵈ) (tempered distributions)
    - Gaussian measures: Φ(f) = exp(-½⟨f, Cf⟩) with nuclear covariance C
    - Construction of the Gaussian Free Field

    **Historical Note**: This theorem, proved by R.A. Minlos in 1959, is fundamental
    to the construction of infinite-dimensional Gaussian measures in quantum field theory. -/
axiom minlos_theorem
  {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NuclearSpace E] [MeasurableSpace (WeakDual ℝ E)]
  (Φ : E → ℂ)
  (h_continuous : Continuous Φ)
  (h_positive_definite : IsPositiveDefinite Φ)
  (h_normalized : Φ 0 = 1) :
  ∃ μ : Measure (WeakDual ℝ E), IsProbabilityMeasure μ ∧
    (∀ f : E, Φ f = ∫ ω, Complex.exp (I * (ω f)) ∂μ)

/-- **Minlos Uniqueness**: If two probability measures on the weak dual have the same
    characteristic functional, then they are equal.
    Note: Used locally in `measure_push_symmetry` and `gaussian_measure_symmetry`,
    but those theorems are not in the master theorem dependency chain. -/
axiom minlos_uniqueness
  {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NuclearSpace E] [MeasurableSpace (WeakDual ℝ E)]
  (μ₁ μ₂ : ProbabilityMeasure (WeakDual ℝ E)) :
  (∀ f : E,
    ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ₁.toMeasure =
    ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ₂.toMeasure) →
  μ₁ = μ₂

/-! ## Applications to Gaussian Free Fields -/

/-- For Gaussian measures, the characteristic functional has the special form
    Φ(f) = exp(-½⟨f, Cf⟩) where C is a nuclear covariance operator. -/
def gaussian_characteristic_functional
  (covariance_form : E → E → ℝ) (f : E) : ℂ :=
  Complex.exp (-(1/2 : ℂ) * (covariance_form f f))

-- `isPositiveDefinite_precomp_linear` is now in `OSforGFF.PositiveDefinite`

/-- **Gaussian RBF kernel is positive definite on inner product spaces.**

    For an inner product space H, the function φ(h) = exp(-½‖h‖²) is positive definite.

    **Proof sketch** (not yet formalized):
    Using the inner product identity ‖x-y‖² = ‖x‖² + ‖y‖² - 2⟨x,y⟩, we get:
      exp(-½‖x-y‖²) = exp(-½‖x‖²) · exp(-½‖y‖²) · exp(⟨x,y⟩)

    The function exp(⟨x,y⟩) is positive definite because:
    1. The inner product ⟨·,·⟩ is a positive semidefinite kernel
    2. Exponentials of PSD kernels are PSD (via Taylor expansion and Schur product theorem)
    3. Products of PSD kernels are PSD

    **Note**: This is FALSE for general normed spaces. The Gaussian RBF exp(-‖x‖²)
    is positive definite on V iff V embeds isometrically into a Hilbert space
    (Schoenberg's theorem / Bretagnolle-Dacunha-Castelle-Krivine theorem).

    **PROVEN** in `OSforGFF/GaussianRBF.lean` using:
    - The inner product kernel is PD
    - Exponential preserves PD (via Hadamard series and Schur product theorem)
    - Factorization: exp(-½|x-y|²) = exp(-½|x|²)·exp(-½|y|²)·exp(⟨x,y⟩) -/
theorem gaussian_rbf_pd_innerProduct
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
  IsPositiveDefinite (fun h : H => Complex.exp (-(1/2 : ℂ) * (‖h‖^2 : ℝ))) :=
  gaussian_rbf_pd_innerProduct_proof

/-- If covariance is realized as a squared norm via a linear embedding T into
    a real inner product space H, then the Gaussian characteristic functional
    is positive definite.

    **Note**: We require H to be an inner product space (not just normed space)
    because the Gaussian RBF kernel is only guaranteed positive definite for
    Hilbert spaces, not general Banach spaces. -/
lemma gaussian_positive_definite_via_embedding
  {E H : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (T : E →ₗ[ℝ] H)
  (covariance_form : E → E → ℝ)
  (h_eq : ∀ f, covariance_form f f = (‖T f‖^2 : ℝ)) :
  IsPositiveDefinite (fun f => Complex.exp (-(1/2 : ℂ) * (covariance_form f f))) := by
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
    simpa using (isPositiveDefinite_precomp_linear
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

/-- Application of Minlos theorem to Gaussian measures.
    If the covariance form can be realized as a squared norm via a linear embedding T into
    a real inner product space H, then the Gaussian characteristic functional Φ(f) = exp(-½⟨f, Cf⟩)
    satisfies the conditions of Minlos theorem, yielding a Gaussian probability measure on E'.

    **Note**: We require H to be an inner product space (not just normed) because the
    Gaussian RBF kernel is only positive definite for Hilbert spaces. -/
theorem minlos_gaussian_construction
  {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NuclearSpace E] [MeasurableSpace (WeakDual ℝ E)]
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
  -- Apply Minlos theorem to the Gaussian characteristic functional
  apply minlos_theorem (gaussian_characteristic_functional covariance_form)
  -- 1. Continuity: composition of continuous maps
  · have h_covar_continuous : Continuous (fun f => (covariance_form f f : ℂ)) := by
      exact Continuous.comp continuous_ofReal h_continuous
    have h_scaled_continuous : Continuous (fun f => -(1/2 : ℂ) * (covariance_form f f : ℂ)) := by
      apply Continuous.mul
      · exact continuous_const
      · exact h_covar_continuous
    exact Continuous.comp continuous_exp h_scaled_continuous
  -- 2. Positive definiteness via embedding
  · exact gaussian_positive_definite_via_embedding T covariance_form h_eq
  -- 3. Normalization at 0
  · simp [gaussian_characteristic_functional, h_zero]

/-- The measure constructed by Minlos theorem for a Gaussian characteristic functional
    indeed has that functional as its characteristic function.

    This theorem makes explicit that the Gaussian measure μ constructed via Minlos
    satisfies: for any test function f,
    ∫ ω, exp(i⟨f,ω⟩) dμ(ω) = exp(-½⟨f,Cf⟩)

    This is the fundamental property connecting the abstract Minlos construction
    to the concrete Gaussian generating functional used in quantum field theory.

    **Note**: Requires H to be an inner product space for the Gaussian RBF positivity. -/
theorem gaussian_measure_characteristic_functional
  {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NuclearSpace E] [MeasurableSpace (WeakDual ℝ E)]
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
  [NuclearSpace E] [MeasurableSpace (WeakDual ℝ E)]
  (covariance_form : E → E → ℝ)
  (μ : ProbabilityMeasure (WeakDual ℝ E))
  (h_char : ∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ.toMeasure =
                     gaussian_characteristic_functional covariance_form f)
  (g : E →L[ℝ] E)
  (h_covar_symm : ∀ f : E, covariance_form (g f) (g f) = covariance_form f f)
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
  -- Apply uniqueness
  apply minlos_uniqueness μ_push μ
  intro f
  rw [h_push_char, h_char, h_Φ_symm, h_char]

end
