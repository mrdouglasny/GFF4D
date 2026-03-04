/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Data.Complex.Basic
--import Mathlib.Topology.Algebra.Module.Complex
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

import OSforGFF.Basic
import OSforGFF.Minlos
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
Minlos Analyticity — Entire characteristic functionals on nuclear spaces

This file sets up the complex-analytic side needed to apply Minlos' theorem
with analyticity (entire extension to the complexification) and the
exponential-moment criteria, following the notes in `texts/minlos_analytic.txt`.

Highlights
- Define a notion of "entire on the complexification" for a characteristic functional χ : E → ℂ
- State the equivalence: entire extension ↔ local uniform exponential moments
- Provide a complexified Gaussian characteristic functional and prove it is entire

We keep some parts as stubs (sorry) pending detailed functional-analytic development.
-/

open Classical
open TopologicalSpace MeasureTheory Complex Filter

-- Use bochner's MeasurableSpace instance on FieldConfiguration (= WeakDual ℝ TestFunction)
-- in this file, so that minlos_uniqueness can be applied directly.
-- Basic.lean's comap-pi instance is propositionally equal (see measurableSpace_comap_eq_bochner)
-- but not definitionally equal, causing type mismatches with bochner's theorems.
attribute [-instance] instMeasurableSpaceFieldConfiguration

/-! ## Contents

This file provides infrastructure for Gaussian measures via Minlos.
See `texts/axioms.txt` for justification of axioms.

**Items in this file:**
- `CovarianceForm` (structure): Real symmetric bilinear form for covariance
- `negMap`, `negMap_measurable`: Negation map for symmetry arguments
- `integral_neg_invariance`: Symmetry under sign flip (uses Minlos uniqueness)
- `moment_zero_from_realCF`: Zero mean from symmetry

**Removed 2025-12-16:**
The `twoD_line_from_realCF` axiom and its proof chain (Qc, pairingC, Zc, gaussian_CF_complex, etc.)
were removed after being superseded by `gff_complex_characteristic_OS0` in GFFIsGaussian.lean,
which uses OS0 + identity theorem directly.
-/

noncomputable section

namespace MinlosAnalytic

-- Note: FieldConfiguration uses the cylindrical σ-algebra (defined in Basic.lean).

/-- A real symmetric, positive semidefinite covariance form on real test functions. -/
structure CovarianceForm where
  Q : TestFunction → TestFunction → ℝ
  symm : ∀ f g, Q f g = Q g f
  psd  : ∀ f, 0 ≤ Q f f
  cont_diag : Continuous fun f => Q f f
  -- New: ℝ-bilinearity (specified on the left; right follows from symmetry)
  add_left : ∀ f₁ f₂ g, Q (f₁ + f₂) g = Q f₁ g + Q f₂ g
  smul_left : ∀ (c : ℝ) f g, Q (c • f) g = c * Q f g

/-- The negation map on field configurations: T(ω) = -ω -/
def negMap : FieldConfiguration → FieldConfiguration := fun ω => -ω

/-- The negation map is measurable -/
lemma negMap_measurable : Measurable negMap := by
  -- With bochner's instance (⨆ φ, (borel ℝ).comap (eval φ)), negMap is measurable
  -- because each evaluation (-ω)(φ) = -(ω(φ)) is measurable
  apply measurable_iff_comap_le.mpr
  show (⨆ (φ : TestFunction), (borel ℝ).comap
    (fun l : FieldConfiguration => (l : TestFunction →L[ℝ] ℝ) φ)).comap negMap ≤ _
  rw [MeasurableSpace.comap_iSup]
  exact iSup_le fun φ =>
    (le_of_eq MeasurableSpace.comap_comp).trans
      (measurable_neg.comp (WeakDual.eval_measurable φ)).comap_le

/-- Symmetry under global sign flip induced by the real Gaussian CF.
    Uses bochner's `minlos_uniqueness` (proven, not axiomatic) to conclude
    that the pushforward under negation equals the original measure.

    The Gaussian CF's bochner-PD property (hermitian + nonneg) is taken as a
    hypothesis. Hermiticity follows from bilinearity of Q; nonneg-PD follows
    from the GNS construction or from the CF being an actual characteristic
    functional (∑∑ c̄ᵢcⱼ ∫ exp(iω(xᵢ-xⱼ)) = ∫ |∑ cᵢ exp(iωxᵢ)|² ≥ 0). -/
lemma integral_neg_invariance
  [IsHilbertNuclear TestFunction] [SeparableSpace TestFunction] [Nonempty TestFunction]
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f)))
  (h_cf_pd : BochnerPD
    (fun f : TestFunction => Complex.exp (-(1/2 : ℂ) * (C.Q f f : ℂ)))) :
  ∀ (f : FieldConfiguration → ℂ), Integrable f μ.toMeasure →
    ∫ ω, f ω ∂μ.toMeasure = ∫ ω, f (-ω) ∂μ.toMeasure := by
  intro f hInt
  classical
  -- Plan:
  -- 1) Consider T(ω) = -ω and the pushforward μneg := μ ◦ T^{-1}.
  -- 2) Show μneg has the same characteristic functional as μ using h_realCF and (-ω) a = -ω a.
  -- 3) Conclude μneg = μ by Minlos uniqueness.
  -- 4) Use the change-of-variables for map to get the desired integral identity.

  -- Step 1: Define the pushforward measure
  let μneg := μ.toMeasure.map negMap
  have hμneg_prob : IsProbabilityMeasure μneg := by
    exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable negMap_measurable)

  -- Step 2: Show characteristic functionals are equal
  have hCF_equal : ∀ g : TestFunction,
      ∫ ω, Complex.exp (Complex.I * (distributionPairing ω g)) ∂μneg
        = ∫ ω, Complex.exp (Complex.I * (distributionPairing ω g)) ∂μ.toMeasure := by
    intro g
    -- Use the change of variables formula for the map
    have h_aestrongly_measurable : AEStronglyMeasurable (fun ω => Complex.exp (Complex.I * (distributionPairing ω g))) μneg := by
      -- Inner map: ω ↦ distributionPairing ω g is measurable via continuous linear map
      have h_inner_meas : Measurable (fun ω : FieldConfiguration => distributionPairing ω g) :=
        WeakDual.eval_measurable g
      -- Outer map: x ↦ exp(I * x) is continuous hence measurable
      have h_cont_mulI : Continuous (fun x : ℝ => (Complex.I : ℂ) * (x : ℂ)) :=
        continuous_const.mul continuous_ofReal
      have h_cont_exp : Continuous (fun z : ℂ => Complex.exp z) := Complex.continuous_exp
      have h_outer_meas : Measurable (fun x : ℝ => Complex.exp ((Complex.I : ℂ) * (x : ℂ))) :=
        (h_cont_exp.comp h_cont_mulI).measurable
      -- Composition is measurable, hence AEStronglyMeasurable
      exact (h_outer_meas.comp h_inner_meas).aestronglyMeasurable
    rw [integral_map (Measurable.aemeasurable negMap_measurable) h_aestrongly_measurable]
    -- The integrand becomes: exp(I * ((-ω) g)) = exp(I * (-(ω g))) = exp(-I * (ω g))
    have h_neg_pairing : (fun ω => Complex.exp (Complex.I * (distributionPairing (negMap ω) g))) =
                         (fun ω => Complex.exp (Complex.I * (distributionPairing (-ω) g))) := by
      simp [negMap]
    rw [h_neg_pairing]
    -- Step 1: (-ω) g = -(ω g) by linearity (negation is scalar multiplication by -1)
    have h_neg_eq : ∀ ω : FieldConfiguration, distributionPairing (-ω) g = -distributionPairing ω g := by
      intro ω
      have h_neg_smul : -ω = (-1 : ℝ) • ω := (neg_one_smul ℝ ω).symm
      rw [h_neg_smul, distributionPairing_smul]
      ring
    -- Step 2: Rewrite the LHS using h_neg_eq
    have h_lhs_eq : (fun ω => Complex.exp (Complex.I * (distributionPairing (-ω) g : ℂ))) =
                    (fun ω => Complex.exp (-(Complex.I * (distributionPairing ω g : ℂ)))) := by
      funext ω
      rw [h_neg_eq]
      simp only [ofReal_neg, mul_neg]
    conv_lhs => rw [h_lhs_eq]
    -- Step 3: exp(-I*x) = conj(exp(I*x)) for real x
    have h_exp_neg_conj : ∀ x : ℝ, Complex.exp (-(Complex.I * (x : ℂ))) = starRingEnd ℂ (Complex.exp (Complex.I * (x : ℂ))) := by
      intro x
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have h_integrand_conj : (fun ω => Complex.exp (-(Complex.I * (distributionPairing ω g : ℂ)))) =
                            (fun ω => starRingEnd ℂ (Complex.exp (Complex.I * (distributionPairing ω g : ℂ)))) := by
      funext ω
      exact h_exp_neg_conj (distributionPairing ω g)
    conv_lhs => rw [h_integrand_conj]
    -- Step 4: Use integral_conj and that the CF is real
    -- The integral ∫ conj(f) = conj(∫ f), and the CF value is real, so conj(CF) = CF
    rw [integral_conj]
    -- The CF h_realCF says ∫ exp(I*ωg) = exp(-½Q(g,g)) which is real
    -- Since exp of a real number is real, conj(exp(-½Q(g,g))) = exp(-½Q(g,g))
    -- First unfold distributionPairing to match h_realCF
    simp only [distributionPairing] at *
    rw [h_realCF g]
    -- exp(-½Q(g,g)) is exp of a real, so conj = self
    have h_CF_is_real : (Complex.exp (-(1/2 : ℂ) * (C.Q g g : ℂ))).im = 0 := by
      -- Rewrite as exp of a real cast to ℂ
      have h_eq : (-(1/2 : ℂ) * (C.Q g g : ℂ)) = ((-(1/2 : ℝ) * C.Q g g : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h_eq]
      exact Complex.exp_ofReal_im (-(1/2) * C.Q g g)
    rw [Complex.conj_eq_iff_im.mpr h_CF_is_real]

  -- Step 3: Apply uniqueness of measures (bochner's minlos_uniqueness)
  -- Two probability measures with the same characteristic functional are equal.
  let μneg_prob : ProbabilityMeasure FieldConfiguration := ⟨μneg, hμneg_prob⟩
  -- Define the Gaussian CF as Φ and prove its properties
  let Φ : TestFunction → ℂ := fun f => Complex.exp (-(1/2 : ℂ) * (C.Q f f : ℂ))
  have h_cf_cont : Continuous Φ := by
    apply Continuous.comp continuous_exp
    apply Continuous.mul continuous_const
    exact Continuous.comp continuous_ofReal C.cont_diag
  have h_cf_norm : Φ 0 = 1 := by
    show Complex.exp (-(1/2 : ℂ) * (C.Q 0 0 : ℂ)) = 1
    have : C.Q 0 0 = 0 := by
      have h := C.smul_left 0 0 0; simp at h; linarith [C.psd 0, h]
    simp [this]
  have hμeq_prob : μneg_prob = μ := by
    apply minlos_uniqueness (Φ := Φ) h_cf_cont h_cf_pd h_cf_norm
    · intro g
      exact (hCF_equal g).trans (h_realCF g)
    · intro g
      exact h_realCF g
  have hμeq : μneg = μ.toMeasure := by
    have h := congrArg ProbabilityMeasure.toMeasure hμeq_prob
    exact h

  -- Step 4: Use the equality of measures to get the integral identity
  have hf_aestrongly_measurable : AEStronglyMeasurable f μneg := by
    rw [hμeq]
    exact hInt.aestronglyMeasurable
  have h_cov : ∫ ω, f ω ∂μneg = ∫ ω, f (negMap ω) ∂μ.toMeasure := by
    exact integral_map (Measurable.aemeasurable negMap_measurable) hf_aestrongly_measurable
  rw [hμeq] at h_cov
  rw [h_cov]
  simp [negMap]

/-- Zero mean from the real Gaussian characteristic functional, via symmetry and L¹. -/
lemma moment_zero_from_realCF
  [IsHilbertNuclear TestFunction] [SeparableSpace TestFunction] [Nonempty TestFunction]
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f)))
  (h_cf_pd : BochnerPD
    (fun f : TestFunction => Complex.exp (-(1/2 : ℂ) * (C.Q f f : ℂ))))
  (a : TestFunction)
  (hInt1 : Integrable (fun ω => (ω a : ℂ)) μ.toMeasure) :
  ∫ ω, (ω a : ℂ) ∂μ.toMeasure = 0 := by
  classical
  -- Symmetry: ∫ f(ω) = ∫ f(-ω)
  have hInv := integral_neg_invariance C μ h_realCF h_cf_pd (fun ω => (ω a : ℂ)) hInt1
  -- Flip integrand: ((-ω) a : ℂ) = - (ω a : ℂ)
  have hflip : (fun ω : FieldConfiguration => ((-ω) a : ℂ)) = (fun ω => - (ω a : ℂ)) := by
    funext ω
    rw [ContinuousLinearMap.neg_apply]
    simp
  -- Hence ∫ X = ∫ -X = -∫ X
  have : ∫ ω, (ω a : ℂ) ∂μ.toMeasure = - ∫ ω, (ω a : ℂ) ∂μ.toMeasure := by
    simpa [hflip, integral_neg, hInt1] using hInv
  -- 2 · ∫ X = 0 ⇒ ∫ X = 0
  have hsum : (2 : ℂ) • (∫ ω, (ω a : ℂ) ∂μ.toMeasure) = 0 := by
    simpa [two_smul] using congrArg (fun z => z + ∫ ω, (ω a : ℂ) ∂μ.toMeasure) this
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  exact (smul_eq_zero.mp hsum).resolve_left htwo

end MinlosAnalytic
