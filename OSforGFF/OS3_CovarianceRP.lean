/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import OSforGFF.Basic
import OSforGFF.QFTHilbertSpace
import OSforGFF.PositiveTimeTestFunction_real
import OSforGFF.FourierTransforms
import OSforGFF.CovarianceMomentum
import OSforGFF.OS3_MixedRep
import OSforGFF.OS3_MixedRepInfra
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Direct Reflection Positivity (No Spatial Regulator)

Self-contained proof of reflection positivity for the free scalar field,
without importing `CovarianceRP.lean`. All needed definitions and theorems
are transferred here.

## Proof Structure

1. Define `rpInnerProduct m f = ∫∫ conj(f(Θx)) C(x,y) f(y)`
2. Change of variables → `∫∫ conj(f(x)) C(Θx,y) f(y)`
3. Mixed representation → `(1/(2(2π)^{d-1})) ∫_{k_sp} ∫∫ (1/ω) exp(-ω|t|) ...`
4. Factorization using positive-time support: `exp(-ω|t|) = exp(-ω(x₀+y₀))`
5. Result: `(1/(2(2π)^{d-1})) ∫_{k_sp} (1/ω) |F_ω(-k_sp)|²`
6. Non-negativity of integrand and prefactor → `Re(...) ≥ 0`

**Key insight:** The mixed representation from `bessel_bilinear_eq_mixed_representation`
already contains the factorizable form `(1/ω) exp(-ω|t|)`. For positive-time test
functions, `|t| = |-x₀-y₀| = x₀+y₀`, so the exponential factorizes directly.
No Lorentzian inversion (converting back to k₀ integral) is needed.
-/

namespace BlueprintAlt

open MeasureTheory Complex Real
open scoped ComplexConjugate

/-! ## Part 1: Core Definitions -/

noncomputable def timeReflection (x : SpaceTime) : SpaceTime :=
  (WithLp.equiv 2 _).symm (Function.update x.ofLp 0 (-x.ofLp 0))

lemma timeReflection_involutive : Function.Involutive timeReflection := by
  intro x
  simp only [timeReflection]
  apply PiLp.ext
  intro i
  simp only [WithLp.equiv_symm_apply]
  by_cases hi : i = 0 <;> simp [hi, Function.update]

noncomputable def spatialDot (k_spatial x_spatial : SpatialCoords) : ℝ :=
  ∑ i, k_spatial i * x_spatial i

noncomputable def freeCovarianceℂ_bilinear (m : ℝ) (f g : TestFunctionℂ) : ℂ :=
  ∫ x, ∫ y, (f x) * (_root_.freeCovariance m x y) * (g y)

noncomputable def weightedLaplaceFourier (m : ℝ) (f : TestFunctionℂ) (k_sp : SpatialCoords) : ℂ :=
  let ω := Real.sqrt (‖k_sp‖^2 + m^2)
  ∫ x : SpaceTime, f x * Complex.exp (-ω * x 0) *
    Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x))

noncomputable def rpInnerProduct (m : ℝ) (f : TestFunctionℂ) : ℂ :=
  freeCovarianceℂ_bilinear m (star f) f

/-! ## Part 2: Change of Variables -/

variable (m : ℝ) [Fact (0 < m)]

lemma star_apply (f : TestFunctionℂ) (x : SpaceTime) :
    (star f) x = starRingEnd ℂ (f (timeReflection x)) := rfl

omit [Fact (0 < m)] in
theorem rpInnerProduct_eq_bessel_reflected (f : TestFunctionℂ) :
    rpInnerProduct m f =
      ∫ x : SpaceTime, ∫ y : SpaceTime,
        (starRingEnd ℂ (f x)) * (_root_.freeCovariance m (timeReflection x) y : ℂ) * f y := by
  unfold rpInnerProduct freeCovarianceℂ_bilinear
  have h_star : ∀ x, (star f) x = starRingEnd ℂ (f (timeReflection x)) := star_apply f
  simp_rw [h_star]
  have h_mp := QFT.timeReflection_measurePreserving
  have h_inv : ∀ x, timeReflection (timeReflection x) = x := fun x => by
    simp [timeReflection, Function.update]
  let G := fun x => ∫ y, (starRingEnd ℂ (f (timeReflection x))) *
      (_root_.freeCovariance m x y : ℂ) * f y
  have h_cov : ∫ x, G x = ∫ x, G (timeReflection x) :=
    (h_mp.integral_comp QFT.timeReflectionLE.toMeasurableEquiv.measurableEmbedding G).symm
  conv_lhs => rw [h_cov]
  congr 1; ext x; simp only [G]; congr 1; ext y; rw [h_inv x]

/-! ## Part 3: Mixed Representation (Direct Approach) -/

/-- The mixed representation from the Schwinger pathway.
    This is more direct than the k₀-inside form for proving reflection positivity,
    because `(1/ω) exp(-ω|t|)` already factorizes for positive-time test functions. -/
theorem mixed_representation (f : TestFunctionℂ)
    (hf_supp : ∀ x, x 0 ≤ 0 → f x = 0) :
    rpInnerProduct m f =
    (1 / (2 * (2 * Real.pi) ^ (STDimension - 1)) : ℝ) *
    ∫ k_sp : SpatialCoords, ∫ x : SpaceTime, ∫ y : SpaceTime,
      let ω := Real.sqrt (‖k_sp‖^2 + m^2)
      (starRingEnd ℂ (f x)) * f y *
      (1 / ω : ℝ) *
      Complex.exp (-(|-(x 0) - y 0| : ℝ) * ω) *
      Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
  rw [rpInnerProduct_eq_bessel_reflected]
  exact bessel_bilinear_eq_mixed_representation m f hf_supp

/-! ## Part 4: Key Lemmas -/

lemma energy_pos (k_sp : SpatialCoords) : 0 < Real.sqrt (‖k_sp‖^2 + m^2) := by
  apply Real.sqrt_pos_of_pos
  have hm : 0 < m := Fact.out
  nlinarith [sq_nonneg ‖k_sp‖]

/-! ## Part 5: Factorization Helpers -/

omit [Fact (0 < m)] in
lemma abs_neg_sum_nonneg (x0 y0 : ℝ) (hx : 0 ≤ x0) (hy : 0 ≤ y0) :
    |-x0 - y0| = x0 + y0 := by
  rw [abs_of_nonpos (by linarith : -x0 - y0 ≤ 0)]; ring

omit [Fact (0 < m)] in
lemma spatialDot_sub (k_sp x_sp y_sp : SpatialCoords) :
    spatialDot k_sp (x_sp - y_sp) = spatialDot k_sp x_sp - spatialDot k_sp y_sp := by
  simp only [spatialDot]
  have h : ∀ i, k_sp i * (x_sp - y_sp) i = k_sp i * x_sp i - k_sp i * y_sp i := by
    intro i; simp only [PiLp.sub_apply, mul_sub]
  simp_rw [h, Finset.sum_sub_distrib]

omit [Fact (0 < m)] in
lemma exp_spatial_phase_factor (k_sp : SpatialCoords) (x_sp y_sp : SpatialCoords) :
    Complex.exp (-Complex.I * spatialDot k_sp (x_sp - y_sp)) =
    Complex.exp (-Complex.I * spatialDot k_sp x_sp) *
    Complex.exp (Complex.I * spatialDot k_sp y_sp) := by
  rw [← Complex.exp_add, spatialDot_sub]; congr 1; push_cast; ring

noncomputable def xIntegralFactor (f : TestFunctionℂ) (ω : ℝ) (k_sp : SpatialCoords) : ℂ :=
  ∫ x : SpaceTime, (starRingEnd ℂ (f x)) *
    Complex.exp (-(ω * x 0)) * Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x))

noncomputable def yIntegralFactor (f : TestFunctionℂ) (ω : ℝ) (k_sp : SpatialCoords) : ℂ :=
  ∫ y : SpaceTime, f y *
    Complex.exp (-(ω * y 0)) * Complex.exp (Complex.I * spatialDot k_sp (spatialPart y))

omit [Fact (0 < m)] in
lemma norm_neg_eq (k_sp : SpatialCoords) : ‖-k_sp‖ = ‖k_sp‖ := norm_neg k_sp

omit [Fact (0 < m)] in
lemma spatialDot_neg_left (k_sp x_sp : SpatialCoords) :
    spatialDot (-k_sp) x_sp = -spatialDot k_sp x_sp := by
  simp only [spatialDot]
  have h : ∀ i, (-k_sp) i * x_sp i = -(k_sp i * x_sp i) := by
    intro i; simp only [PiLp.neg_apply, neg_mul]
  simp_rw [h, Finset.sum_neg_distrib]

omit [Fact (0 < m)] in
lemma xIntegralFactor_eq_conj_neg (f : TestFunctionℂ) (k_sp : SpatialCoords)
    (_hf_support : ∀ x : SpaceTime, x 0 < 0 → f x = 0) :
    xIntegralFactor f (Real.sqrt (‖k_sp‖^2 + m^2)) k_sp =
    starRingEnd ℂ (weightedLaplaceFourier m f (-k_sp)) := by
  simp only [xIntegralFactor, weightedLaplaceFourier]
  have h_norm : ‖-k_sp‖ = ‖k_sp‖ := norm_neg_eq k_sp
  have h_dot : ∀ x_sp, spatialDot (-k_sp) x_sp = -spatialDot k_sp x_sp := spatialDot_neg_left k_sp
  simp only [h_norm, h_dot, Complex.ofReal_neg]
  have h_exp_neg : ∀ (a : ℝ), Complex.exp (-Complex.I * -↑a) = Complex.exp (Complex.I * ↑a) := by
    intro a; congr 1; ring
  simp only [h_exp_neg]
  rw [← integral_conj]
  congr 1; ext x; simp only [map_mul]
  have h_star_exp : ∀ z : ℂ, starRingEnd ℂ (Complex.exp z) = Complex.exp (starRingEnd ℂ z) := by
    intro z
    have h1 : starRingEnd ℂ (Complex.exp z) = conj (Complex.exp z) := rfl
    have h2 : starRingEnd ℂ z = conj z := rfl
    rw [h1, h2, ← Complex.exp_conj]
  simp only [h_star_exp]
  congr 1
  · simp only [map_neg, map_mul, Complex.conj_ofReal]; congr 1; ring_nf
  · simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]

omit [Fact (0 < m)] in
lemma yIntegralFactor_eq_neg (f : TestFunctionℂ) (k_sp : SpatialCoords) :
    yIntegralFactor f (Real.sqrt (‖k_sp‖^2 + m^2)) k_sp =
    weightedLaplaceFourier m f (-k_sp) := by
  simp only [yIntegralFactor, weightedLaplaceFourier]
  have h_norm : ‖-k_sp‖ = ‖k_sp‖ := norm_neg_eq k_sp
  have h_dot : ∀ x_sp, spatialDot (-k_sp) x_sp = -spatialDot k_sp x_sp := spatialDot_neg_left k_sp
  simp only [h_norm]; congr 1; ext x; simp only [h_dot, Complex.ofReal_neg]
  congr 1
  · congr 1; ring_nf
  · congr 1; simp only [neg_mul_neg]

/-! ## Part 6: Factorization to Squared Norm (Direct Approach) -/

/-- **Direct factorization** from the mixed representation.

    For positive-time test functions, the mixed representation integrand
    `(1/ω) exp(-ω|t|) exp(-ik_sp·r)` factorizes directly because:
    - `|t| = |-x₀-y₀| = x₀+y₀` when `x₀, y₀ ≥ 0`
    - `exp(-ω(x₀+y₀)) = exp(-ωx₀) · exp(-ωy₀)`
    - `exp(-ik_sp·r) = exp(-ik_sp·x_sp) · exp(+ik_sp·y_sp)`

    This avoids the round-trip through k₀ space that the old proof used. -/
theorem factorization_to_squared_norm_direct (f : TestFunctionℂ) (k_sp : SpatialCoords)
    (hf_support : ∀ x : SpaceTime, x 0 < 0 → f x = 0) :
    let ω := Real.sqrt (‖k_sp‖^2 + m^2)
    ∫ x : SpaceTime, ∫ y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
      (1 / ω : ℝ) *
      Complex.exp (-(|-(x 0) - y 0| : ℝ) * ω) *
      Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
    ((1 / ω * Complex.normSq (weightedLaplaceFourier m f (-k_sp)) : ℝ) : ℂ) := by
  intro ω
  have hω : 0 < ω := energy_pos m k_sp
  -- Step 1: Rearrange using positive-time support
  -- For x₀, y₀ ≥ 0: |−x₀−y₀| = x₀+y₀, so exp(-ω|t|) = exp(-ωx₀)·exp(-ωy₀)
  have h_rearrange : ∀ x y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
        (1 / ω : ℝ) *
        Complex.exp (-(|-(x 0) - y 0| : ℝ) * ω) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
      ((1 / ω : ℝ) : ℂ) *
        ((starRingEnd ℂ (f x)) * Complex.exp (-ω * (x 0)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x))) *
        (f y * Complex.exp (-ω * (y 0)) *
          Complex.exp (Complex.I * spatialDot k_sp (spatialPart y))) := by
    intro x y
    by_cases hx : x 0 < 0
    · simp only [hf_support x hx, map_zero, zero_mul, mul_zero]
    · by_cases hy : y 0 < 0
      · simp only [hf_support y hy, mul_zero, zero_mul]
      · push_neg at hx hy
        have h_abs : |-(x 0) - y 0| = x 0 + y 0 := abs_neg_sum_nonneg (x 0) (y 0) hx hy
        rw [h_abs]
        -- Normalize casts: ↑(a + b) → ↑a + ↑b
        simp only [Complex.ofReal_add]
        -- The mixed rep has exp(-(↑x₀ + ↑y₀) * ω), need to match exp(-ω * x₀) * exp(-ω * y₀)
        have h_exp_factor : Complex.exp (-(↑(x 0) + ↑(y 0)) * ↑ω) =
            Complex.exp (-↑ω * ↑(x 0)) * Complex.exp (-↑ω * ↑(y 0)) := by
          rw [← Complex.exp_add]; congr 1; ring
        rw [exp_spatial_phase_factor k_sp (spatialPart x) (spatialPart y)]
        rw [h_exp_factor]; ring
  simp_rw [h_rearrange]
  -- Step 2: Factor the double integral via Fubini
  let fx := fun x : SpaceTime =>
    (starRingEnd ℂ (f x)) * Complex.exp (-(ω * x 0)) *
      Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x))
  let gy := fun y : SpaceTime =>
    f y * Complex.exp (-(ω * y 0)) *
      Complex.exp (Complex.I * spatialDot k_sp (spatialPart y))
  have hfx_eq : ∫ x : SpaceTime, fx x = xIntegralFactor f ω k_sp := rfl
  have hgy_eq : ∫ y : SpaceTime, gy y = yIntegralFactor f ω k_sp := rfl
  have hX : xIntegralFactor f ω k_sp = starRingEnd ℂ (weightedLaplaceFourier m f (-k_sp)) :=
    xIntegralFactor_eq_conj_neg m f k_sp hf_support
  have hY : yIntegralFactor f ω k_sp = weightedLaplaceFourier m f (-k_sp) :=
    yIntegralFactor_eq_neg m f k_sp
  have h_normSq : ∀ A : ℂ, (starRingEnd ℂ A) * A = (Complex.normSq A : ℂ) := by
    intro A; rw [← Complex.normSq_eq_conj_mul_self]
  have h_fubini : ∫ x : SpaceTime, ∫ y : SpaceTime, (↑(1 / ω) : ℂ) * fx x * gy y =
      (↑(1 / ω) : ℂ) * (∫ x, fx x) * (∫ y, gy y) := by
    have h_pull_const : ∀ (c : ℂ) (g : SpaceTime → ℂ),
        ∫ z : SpaceTime, c * g z = c * ∫ z, g z := by
      intro c g; simp_rw [← smul_eq_mul]; exact MeasureTheory.integral_smul c g
    have h_inner : ∀ x, ∫ y : SpaceTime, (↑(1 / ω) : ℂ) * fx x * gy y =
        (↑(1 / ω) * fx x) * ∫ y, gy y := fun x => h_pull_const (↑(1 / ω) * fx x) gy
    simp_rw [h_inner]
    have h_comm : ∀ x, (↑(1 / ω) * fx x) * ∫ y, gy y = (∫ y, gy y) * (↑(1 / ω) * fx x) := by
      intro x; ring
    simp_rw [h_comm]; rw [h_pull_const, h_pull_const]; ring
  have h_integrand_eq : ∀ x y : SpaceTime,
      (↑(1 / ω) : ℂ) *
        ((starRingEnd ℂ) (f x) * Complex.exp (-↑ω * ↑(x 0)) *
          Complex.exp (-Complex.I * ↑(spatialDot k_sp (spatialPart x)))) *
        (f y * Complex.exp (-↑ω * ↑(y 0)) *
          Complex.exp (Complex.I * ↑(spatialDot k_sp (spatialPart y)))) =
      (↑(1 / ω) : ℂ) * fx x * gy y := by
    intro x y; simp only [fx, gy, neg_mul]
  simp_rw [h_integrand_eq]
  calc ∫ x : SpaceTime, ∫ y : SpaceTime, (↑(1 / ω) : ℂ) * fx x * gy y
      = (↑(1 / ω) : ℂ) * (∫ x, fx x) * (∫ y, gy y) := h_fubini
    _ = (↑(1 / ω) : ℂ) * xIntegralFactor f ω k_sp * yIntegralFactor f ω k_sp := by
        rw [hfx_eq, hgy_eq]
    _ = (↑(1 / ω) : ℂ) * starRingEnd ℂ (weightedLaplaceFourier m f (-k_sp)) *
          weightedLaplaceFourier m f (-k_sp) := by rw [hX, hY]
    _ = (↑(1 / ω) : ℂ) * (starRingEnd ℂ (weightedLaplaceFourier m f (-k_sp)) *
          weightedLaplaceFourier m f (-k_sp)) := by ring
    _ = (↑(1 / ω) : ℂ) * (Complex.normSq (weightedLaplaceFourier m f (-k_sp)) : ℂ) := by
        rw [h_normSq]
    _ = ↑(1 / ω * Complex.normSq (weightedLaplaceFourier m f (-k_sp))) := by
        simp only [Complex.ofReal_mul]

/-! ## Part 7: Final Representation -/

/-- The RP inner product equals `(1/(2(2π)^{d-1})) ∫_{k_sp} (1/ω) |F_ω(-k_sp)|²`.

    This follows directly from the mixed representation + factorization,
    without going through the k₀-inside form. -/
theorem rp_equals_squared_norm_integral (f : TestFunctionℂ)
    (hf_supp : ∀ x : SpaceTime, x 0 ≤ 0 → f x = 0) :
    rpInnerProduct m f =
    (1 / (2 * (2 * Real.pi) ^ (STDimension - 1)) : ℝ) *
    ∫ k_sp : SpatialCoords,
      ((1 / Real.sqrt (‖k_sp‖^2 + m^2) *
        Complex.normSq (weightedLaplaceFourier m f (-k_sp)) : ℝ) : ℂ) := by
  have hf_support : ∀ x : SpaceTime, x 0 < 0 → f x = 0 := fun x hx =>
    hf_supp x (le_of_lt hx)
  rw [mixed_representation m f hf_supp]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with k_sp
  exact factorization_to_squared_norm_direct m f k_sp hf_support

/-! ## Part 8: Direct Reflection Positivity -/

/-- **Theorem**: Direct proof of reflection positivity without spatial regulator.

    For test functions supported on positive time (t > 0), the RP inner product
    ⟨Θf, f⟩_C has non-negative real part.

    Proof: By `rp_equals_squared_norm_integral`,
      ⟨Θf, f⟩_C = (1/(2(2π)^{d-1})) * ∫_{k_sp} (1/ω) |F_ω(-k_sp)|² dk_sp
    Both the prefactor and integrand are non-negative. -/
theorem freeCovariance_reflection_positive_direct (f : TestFunctionℂ)
    (hf_supp : ∀ x : SpaceTime, x 0 ≤ 0 → f x = 0) :
    0 ≤ (rpInnerProduct m f).re := by
  rw [rp_equals_squared_norm_integral m f hf_supp]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply mul_nonneg
  · -- (1/(2(2π)^{d-1})) ≥ 0
    apply one_div_nonneg.mpr
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    apply pow_nonneg
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le
  · -- Re(∫ ↑(real_val)) = ∫ real_val ≥ 0
    have h_integral_real : (∫ k_sp : SpatialCoords,
        ((1 / Real.sqrt (‖k_sp‖ ^ 2 + m ^ 2) *
          Complex.normSq (weightedLaplaceFourier m f (-k_sp)) : ℝ) : ℂ)) =
        ↑(∫ k_sp : SpatialCoords,
          (1 / Real.sqrt (‖k_sp‖ ^ 2 + m ^ 2) *
            Complex.normSq (weightedLaplaceFourier m f (-k_sp)))) :=
      integral_ofReal
    rw [h_integral_real, Complex.ofReal_re]
    apply MeasureTheory.integral_nonneg
    intro k_sp
    apply mul_nonneg
    · exact one_div_nonneg.mpr (Real.sqrt_nonneg _)
    · exact Complex.normSq_nonneg _

end BlueprintAlt
