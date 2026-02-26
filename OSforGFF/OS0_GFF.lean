/-
Copyright (c) 2025-2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# OS0 Analyticity from Gaussian Covariance Structure

This file proves the OS0 (Analyticity) axiom directly from the covariance
structure of the GFF measure, without using the series representation.

## Strategy

For a centered Gaussian measure with covariance C, the complex generating
functional has the closed form:
  Z[f] = exp(-½ C_ℂ(f, f))
where C_ℂ is the complexified covariance bilinear form (freeCovarianceℂ_bilinear).

Since C_ℂ is ℂ-bilinear (proved in Covariance.lean):
  Z[∑ᵢ zᵢ Jᵢ] = exp(-½ ∑ᵢⱼ zᵢ zⱼ C_ℂ(Jᵢ, Jⱼ))
This is exp(quadratic polynomial in z), which is analytic on ℂⁿ.

## Proof strategy for `gff_complex_CF_covariance`

1-parameter analytic continuation: decompose f = f_re + I·f_im, define
L(t) = Z[f_re + t·f_im] and R(t) = exp(-½ Q(t)), show L = R on ℝ (from
`gff_real_characteristic`), extend to ℂ via the identity theorem, evaluate at t = I.

## Key Lemma

- `gff_cf_slice_entire`: t ↦ Z[f_re + t·f_im] is entire.
  Proved via Fernique integrability + parameter-dependent holomorphy of integrals.
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral

import OSforGFF.Basic
import OSforGFF.GFFMconstruct
import OSforGFF.Covariance
import OSforGFF.ComplexTestFunction
import OSforGFF.GFFExponentialIntegrability
import OSforGFF.OS_Axioms

open MeasureTheory Complex QFT ProbabilityTheory
open TopologicalSpace SchwartzMap
open scoped BigOperators

noncomputable section

variable (m : ℝ) [Fact (0 < m)]

/-! ## Complex Characteristic Functional

The complex generating functional of the GFF equals exp(-½ C_ℂ(f,f)) where
C_ℂ(f,g) = ∫∫ f(x) C(x,y) g(y) is the complexified covariance bilinear form.

This follows from the bivariate Gaussian MGF: for (X,Y) = (ω(f_re), ω(f_im))
jointly Gaussian, E[exp(iX - Y)] = exp(½(-Var(X) - 2i Cov(X,Y) + Var(Y)))
which equals exp(-½ C_ℂ(f,f)). -/

/-- The complex generating functional is analytic in a 1-parameter family.
    For fixed real f_re, f_im, the map t ↦ Z[toComplex f_re + t • toComplex f_im]
    is entire (analytic on all of ℂ).

    This follows from: for each ω, the integrand exp(i⟨ω,f_re⟩ + it⟨ω,f_im⟩) is
    entire in t; the modulus is bounded by exp(|Im(t)| · |⟨ω,f_im⟩|), which is
    integrable by Fernique's theorem (gaussianFreeField_pairing_memLp).
    Standard parameter-dependent holomorphy then gives analyticity of the integral. -/
lemma gff_cf_slice_entire (f_re f_im : TestFunction) :
    AnalyticOnNhd ℂ (fun t : ℂ =>
      GJGeneratingFunctionalℂ (μ_GFF m) (toComplex f_re + t • toComplex f_im))
      Set.univ := by
  -- Abbreviations
  set a : FieldConfiguration → ℂ := fun ω => Complex.I * (ω f_re : ℂ)
  set b : FieldConfiguration → ℂ := fun ω => Complex.I * (ω f_im : ℂ)
  set F : ℂ → FieldConfiguration → ℂ := fun t ω => Complex.exp (a ω + t * b ω)
  -- Helper: Re(a(ω) + t * b(ω)) = -t.im * ω(f_im)
  have h_re_formula : ∀ ω t, (a ω + t * b ω).re = -t.im * ω f_im := by
    intro ω t
    simp only [a, b]
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  -- Measurability helpers
  have h_eval_meas_re := fieldConfiguration_eval_measurable f_re
  have h_eval_meas_im := fieldConfiguration_eval_measurable f_im
  have h_ofReal_re : Measurable (fun ω : FieldConfiguration => (ω f_re : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp h_eval_meas_re
  have h_ofReal_im : Measurable (fun ω : FieldConfiguration => (ω f_im : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp h_eval_meas_im
  have h_a_meas : Measurable a := h_ofReal_re.const_mul _
  have h_b_meas : Measurable b := h_ofReal_im.const_mul _
  -- F(t, ·) is AEStronglyMeasurable
  have hF_meas : ∀ t, AEStronglyMeasurable (F t) (μ_GFF m).toMeasure := fun t =>
    (Complex.continuous_exp.measurable.comp
      (h_a_meas.add (h_b_meas.const_mul t))).aestronglyMeasurable
  -- Young's inequality helper: c|x| ≤ c²/(4α) + αx²
  have young : ∀ (c : ℝ) (α : ℝ), 0 < α → ∀ x : ℝ,
      c * |x| ≤ c ^ 2 / (4 * α) + α * x ^ 2 := by
    intro c α hα x
    have h4α_pos : (0 : ℝ) < 4 * α := by positivity
    rw [show c ^ 2 / (4 * α) + α * x ^ 2
        = (c ^ 2 + 4 * α ^ 2 * x ^ 2) / (4 * α) from by field_simp]
    rw [le_div_iff₀ h4α_pos]
    nlinarith [sq_nonneg (c - 2 * α * |x|), sq_abs x]
  -- Fernique domination: exp(c|ω f_im|) is integrable for any c ≥ 0
  have fernique_dom : ∀ (c : ℝ), 0 ≤ c →
      Integrable (fun ω => Real.exp (c * |ω f_im|)) (μ_GFF m).toMeasure := by
    intro c _
    obtain ⟨α, hα_pos, h_fernique⟩ := gaussianFreeField_pairing_expSq_integrable m f_im
    have h_dom : Integrable (fun ω => Real.exp (c ^ 2 / (4 * α) + α * (ω f_im) ^ 2))
        (μ_GFF m).toMeasure := by
      have h := h_fernique.const_mul (Real.exp (c ^ 2 / (4 * α)))
      simp only [distributionPairingCLM_apply, distributionPairing, ← Real.exp_add] at h
      exact h
    apply h_dom.mono
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul (continuous_abs.measurable.comp h_eval_meas_im))
        |>.aestronglyMeasurable)
    filter_upwards with ω
    simp only [Real.norm_eq_abs, Function.comp_def, abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr (young c α hα_pos (ω f_im))
  -- Step 1: rewrite the goal to use ∫ F t ω dμ via AnalyticOnNhd.congr
  -- The generating functional equals the integral of F
  have h_eq : Set.EqOn
      (fun t => ∫ ω, F t ω ∂(μ_GFF m).toMeasure)
      (fun t => GJGeneratingFunctionalℂ (μ_GFF m) (toComplex f_re + t • toComplex f_im))
      Set.univ := by
    intro t _
    simp only [GJGeneratingFunctionalℂ]
    congr 1
    funext ω
    simp only [F, a, b]
    congr 1
    have h1 := pairing_linear_combo ω (toComplex f_re) (toComplex f_im) 1 t
    simp only [one_smul, one_mul, distributionPairingℂ_real_toComplex, distributionPairing] at h1
    rw [h1]; ring
  -- It suffices to prove ∫ F is analytic
  suffices h_analytic : AnalyticOnNhd ℂ (fun t => ∫ ω, F t ω ∂(μ_GFF m).toMeasure) Set.univ from
    h_analytic.congr isOpen_univ h_eq
  -- Step 2: Differentiable ℂ → AnalyticOnNhd (Goursat's theorem)
  suffices h_diff : Differentiable ℂ (fun t => ∫ ω, F t ω ∂(μ_GFF m).toMeasure) by
    intro t₀ _; exact h_diff.analyticAt t₀
  -- For each t₀, apply hasFDerivAt_integral_of_dominated_of_fderiv_le
  intro t₀
  -- d/dt F(t,ω) = b(ω) * F(t,ω)
  have h_hasderiv : ∀ ω t, HasDerivAt (F · ω) (b ω * F t ω) t := by
    intro ω t
    have h1 : HasDerivAt (fun t => a ω + t * b ω) (b ω) t := by
      simpa using (hasDerivAt_mul_const (b ω)).const_add (a ω)
    rw [show b ω * F t ω = Complex.exp (a ω + t * b ω) * b ω from mul_comm _ _]
    exact h1.cexp
  set s := Metric.ball t₀ 1
  -- |t.im| ≤ |t₀.im| + 1 for t ∈ B(t₀, 1)
  have h_im_bound : ∀ t ∈ s, |t.im| ≤ |t₀.im| + 1 := by
    intro t ht
    have h_dist := Metric.mem_ball.mp ht
    rw [dist_eq_norm] at h_dist
    have h1 := Complex.abs_im_le_norm (t - t₀)
    simp only [Complex.sub_im] at h1
    linarith [abs_sub_abs_le_abs_sub t.im t₀.im]
  -- Integrability of F(t₀, ·)
  have hF_int : Integrable (F t₀) (μ_GFF m).toMeasure := by
    apply (fernique_dom (|t₀.im|) (abs_nonneg _)).mono (hF_meas t₀)
    filter_upwards with ω
    simp only [F, Complex.norm_exp, h_re_formula]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_exp.mpr
    calc -t₀.im * ω f_im ≤ |t₀.im * ω f_im| := by
            rw [neg_mul]; exact neg_le.mp (neg_abs_le _)
      _ = |t₀.im| * |ω f_im| := abs_mul _ _
      _ ≤ _ := le_refl _
  -- Fréchet derivative
  have h_fderiv : ∀ ω t, HasFDerivAt (F · ω)
      (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (b ω * F t ω)) t :=
    fun ω t => (h_hasderiv ω t).hasFDerivAt
  -- Derivative measurability at t₀
  have hF'_meas : AEStronglyMeasurable
      (fun ω => ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (b ω * F t₀ ω))
      (μ_GFF m).toMeasure :=
    ((ContinuousLinearMap.smulRightL ℂ ℂ ℂ (1 : ℂ →L[ℂ] ℂ)).continuous.measurable.comp
      (h_b_meas.mul (Complex.continuous_exp.measurable.comp
        (h_a_meas.add (h_b_meas.const_mul t₀))))).aestronglyMeasurable
  -- Bound for derivative norm
  set bound : FieldConfiguration → ℝ := fun ω => |ω f_im| * Real.exp ((|t₀.im| + 1) * |ω f_im|)
  -- Fderiv bound on B(t₀, 1)
  have h_fderiv_bound : ∀ᵐ ω ∂(μ_GFF m).toMeasure, ∀ t ∈ s,
      ‖ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (b ω * F t ω)‖ ≤ bound ω := by
    filter_upwards with ω t ht
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul]
    calc ‖b ω * F t ω‖
        = ‖b ω‖ * ‖F t ω‖ := norm_mul _ _
      _ = |ω f_im| * Real.exp ((a ω + t * b ω).re) := by
          simp only [b, F, Complex.norm_exp, Complex.norm_mul, Complex.norm_I,
            one_mul, Complex.norm_real, Real.norm_eq_abs]
      _ = |ω f_im| * Real.exp (-t.im * ω f_im) := by rw [h_re_formula]
      _ ≤ |ω f_im| * Real.exp ((|t₀.im| + 1) * |ω f_im|) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply Real.exp_le_exp.mpr
          calc -t.im * ω f_im ≤ |t.im * ω f_im| := by
                  rw [neg_mul]; exact neg_le.mp (neg_abs_le _)
            _ = |t.im| * |ω f_im| := abs_mul _ _
            _ ≤ (|t₀.im| + 1) * |ω f_im| := by
                apply mul_le_mul_of_nonneg_right (h_im_bound t ht) (abs_nonneg _)
  -- Bound integrability via Fernique
  have h_bound_integrable : Integrable bound (μ_GFF m).toMeasure := by
    set c := |t₀.im| + 1
    -- bound(ω) = |ω f_im| * exp(c|ω f_im|) ≤ exp((c+1)|ω f_im|) since |x| ≤ exp(|x|)
    apply (fernique_dom (c + 1) (by positivity)).mono
    · exact ((continuous_abs.measurable.comp h_eval_meas_im).aestronglyMeasurable.mul
        ((Real.continuous_exp.measurable.comp
          (measurable_const.mul (continuous_abs.measurable.comp h_eval_meas_im))).aestronglyMeasurable))
    · filter_upwards with ω
      simp only [bound, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)),
        abs_of_nonneg (Real.exp_nonneg _)]
      calc |ω f_im| * Real.exp (c * |ω f_im|)
          ≤ Real.exp |ω f_im| * Real.exp (c * |ω f_im|) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
            calc |ω f_im| ≤ |ω f_im| + 1 := by linarith
              _ ≤ Real.exp |ω f_im| := Real.add_one_le_exp _
        _ = Real.exp ((c + 1) * |ω f_im|) := by rw [← Real.exp_add]; ring_nf
  -- Apply parametric integral differentiation
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le
    (Metric.ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas
    h_fderiv_bound h_bound_integrable
    (by filter_upwards with ω t ht; exact h_fderiv ω t)).differentiableAt

/-- The complex characteristic functional of the GFF.

    For any complex test function f:
    Z[f] = E[exp(i⟨ω,f⟩_ℂ)] = exp(-½ C_ℂ(f, f))

    Proved by 1-parameter analytic continuation: decompose f = f_re + I·f_im,
    show the generating functional and Gaussian formula agree on ℝ (from
    `gff_real_characteristic`), extend to ℂ via the identity theorem. -/
theorem gff_complex_CF_covariance (f : TestFunctionℂ) :
    GJGeneratingFunctionalℂ (μ_GFF m) f =
    cexp (-(1/2 : ℂ) * freeCovarianceℂ_bilinear m f f) := by
  -- Decompose f = toComplex f_re + I • toComplex f_im
  let f_re := (complex_testfunction_decompose f).1
  let f_im := (complex_testfunction_decompose f).2
  have hf : f = toComplex f_re + Complex.I • toComplex f_im := by
    ext x
    simpa [f_re, f_im, toComplex_apply, smul_eq_mul, complex_testfunction_decompose]
      using complex_testfunction_decompose_recompose f x
  -- Define 1-parameter families: L(t) = Z[f_re + t·f_im], R(t) = exp(-½ Q(t))
  let L : ℂ → ℂ := fun t =>
    GJGeneratingFunctionalℂ (μ_GFF m) (toComplex f_re + t • toComplex f_im)
  let R : ℂ → ℂ := fun t =>
    cexp (-(1/2 : ℂ) * ((freeCovarianceFormR m f_re f_re : ℂ) +
      2 * t * (freeCovarianceFormR m f_re f_im : ℂ) +
      t ^ 2 * (freeCovarianceFormR m f_im f_im : ℂ)))
  -- Step 1: L and R agree on ℝ
  have h_agree : ∀ t : ℝ, L (t : ℂ) = R (t : ℂ) := by
    intro t
    simp only [L, R]
    have h_arg : toComplex f_re + (t : ℂ) • toComplex f_im = toComplex (f_re + t • f_im) := by
      ext x; simp [toComplex_apply]
    rw [h_arg, GJGeneratingFunctionalℂ_toComplex, gff_real_characteristic m]
    congr 1; congr 1
    have h_expand : freeCovarianceFormR m (f_re + t • f_im) (f_re + t • f_im)
        = freeCovarianceFormR m f_re f_re + 2 * t * freeCovarianceFormR m f_re f_im
          + t ^ 2 * freeCovarianceFormR m f_im f_im := by
      rw [freeCovarianceFormR_add_left, freeCovarianceFormR_add_right,
          freeCovarianceFormR_add_right,
          freeCovarianceFormR_smul_left, freeCovarianceFormR_smul_right,
          freeCovarianceFormR_smul_left, freeCovarianceFormR_smul_right,
          freeCovarianceFormR_symm m f_im f_re]
      ring
    rw [h_expand]; push_cast; ring
  -- Step 2: R is entire (exp of quadratic polynomial in t)
  have hR_an : AnalyticOnNhd ℂ R Set.univ := by
    apply AnalyticOnNhd.cexp
    apply AnalyticOnNhd.mul analyticOnNhd_const
    apply AnalyticOnNhd.add
    apply AnalyticOnNhd.add
    · exact analyticOnNhd_const
    · -- 2 * t * Q_ri is linear in t
      have : AnalyticOnNhd ℂ (fun t : ℂ =>
          (2 * (freeCovarianceFormR m f_re f_im : ℂ)) * t) Set.univ :=
        AnalyticOnNhd.mul analyticOnNhd_const analyticOnNhd_id
      convert this using 2; ring
    · -- t^2 * Q_ii is polynomial in t
      apply AnalyticOnNhd.mul _ analyticOnNhd_const
      exact (analyticOnNhd_id (𝕜 := ℂ)).pow 2
  -- Step 3: L is entire (from parameter-dependent holomorphy)
  have hL_an : AnalyticOnNhd ℂ L Set.univ := gff_cf_slice_entire m f_re f_im
  -- Step 4: Identity theorem — L = R on all of ℂ
  -- ℝ has accumulation points in ℂ, so agreement on ℝ forces global agreement.
  have h_eq : L = R := by
    apply AnalyticOnNhd.eq_of_frequently_eq hL_an hR_an (z₀ := 0)
    simp only [Filter.Frequently]
    intro hU
    rw [Filter.Eventually, mem_nhdsWithin] at hU
    obtain ⟨V, hV_open, h0_in_V, hV_sub⟩ := hU
    obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hV_open 0 h0_in_V
    -- ε/2 is a nonzero real in V ∩ {0}ᶜ where L = R, contradicting hU
    have h_half_pos : (0 : ℝ) < ε / 2 := half_pos hε_pos
    have h_mem_V : ((ε / 2 : ℝ) : ℂ) ∈ V := hε_ball (by
      simp only [Metric.mem_ball, Complex.dist_eq, sub_zero, Complex.norm_real]
      rw [Real.norm_eq_abs, abs_of_pos h_half_pos]
      linarith)
    have h_ne : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]; linarith
    exact hV_sub ⟨h_mem_V, h_ne⟩ (h_agree (ε / 2))
  -- Step 5: Evaluate at t = I
  have h_eval : L Complex.I = R Complex.I := congrFun h_eq Complex.I
  -- Step 6: Relate L(I) to LHS and R(I) to RHS
  have h_LHS : GJGeneratingFunctionalℂ (μ_GFF m) f = L Complex.I := by
    simp only [L]; congr 1
  have h_RHS : cexp (-(1/2 : ℂ) * freeCovarianceℂ_bilinear m f f) = R Complex.I := by
    simp only [R]; congr 1; congr 1
    -- Expand C_ℂ(f, f) using bilinearity and agrees_on_reals
    conv_lhs => rw [hf]
    rw [freeCovarianceℂ_bilinear_add_left, freeCovarianceℂ_bilinear_add_right,
        freeCovarianceℂ_bilinear_add_right]
    simp only [freeCovarianceℂ_bilinear_smul_left, freeCovarianceℂ_bilinear_smul_right]
    rw [freeCovarianceℂ_bilinear_agrees_on_reals m f_re f_re,
        freeCovarianceℂ_bilinear_agrees_on_reals m f_re f_im,
        freeCovarianceℂ_bilinear_agrees_on_reals m f_im f_re,
        freeCovarianceℂ_bilinear_agrees_on_reals m f_im f_im,
        freeCovarianceFormR_symm m f_im f_re]
    ring
  rw [h_LHS, h_eval, ← h_RHS]

/-! ## Bilinear Expansion for Finite Sums

Using the ℂ-bilinearity of `freeCovarianceℂ_bilinear`, we expand
C_ℂ(∑ᵢ zᵢ Jᵢ, ∑ⱼ zⱼ Jⱼ) = ∑ᵢ ∑ⱼ zᵢ zⱼ C_ℂ(Jᵢ, Jⱼ). -/

/-- C_ℂ(f, 0) = 0, derived from smul_right with c = 0. -/
private lemma freeCovarianceℂ_bilinear_zero_right (f : TestFunctionℂ) :
    freeCovarianceℂ_bilinear m f 0 = 0 := by
  have h := freeCovarianceℂ_bilinear_smul_right m (0 : ℂ) f (0 : TestFunctionℂ)
  simp at h; exact h

/-- C_ℂ(0, g) = 0, derived from smul_left with c = 0. -/
private lemma freeCovarianceℂ_bilinear_zero_left (g : TestFunctionℂ) :
    freeCovarianceℂ_bilinear m 0 g = 0 := by
  have h := freeCovarianceℂ_bilinear_smul_left m (0 : ℂ) (0 : TestFunctionℂ) g
  simp at h; exact h

/-- Right linearity over finite sums for the complexified covariance. -/
private lemma freeCovarianceℂ_sum_right (f : TestFunctionℂ)
    (s : Finset (Fin n)) (z : Fin n → ℂ) (J : Fin n → TestFunctionℂ) :
    freeCovarianceℂ_bilinear m f (∑ i ∈ s, z i • J i) =
    ∑ i ∈ s, z i * freeCovarianceℂ_bilinear m f (J i) := by
  induction s using Finset.cons_induction with
  | empty => simp [freeCovarianceℂ_bilinear_zero_right]
  | cons a s ha ih =>
    rw [Finset.sum_cons, freeCovarianceℂ_bilinear_add_right,
        freeCovarianceℂ_bilinear_smul_right, ih, Finset.sum_cons]

/-- Left linearity over finite sums for the complexified covariance. -/
private lemma freeCovarianceℂ_sum_left
    (s : Finset (Fin n)) (z : Fin n → ℂ) (J : Fin n → TestFunctionℂ)
    (g : TestFunctionℂ) :
    freeCovarianceℂ_bilinear m (∑ i ∈ s, z i • J i) g =
    ∑ i ∈ s, z i * freeCovarianceℂ_bilinear m (J i) g := by
  induction s using Finset.cons_induction with
  | empty => simp [freeCovarianceℂ_bilinear_zero_left]
  | cons a s ha ih =>
    rw [Finset.sum_cons, freeCovarianceℂ_bilinear_add_left,
        freeCovarianceℂ_bilinear_smul_left, ih, Finset.sum_cons]

/-- Full bilinear expansion of C_ℂ(∑ zᵢ Jᵢ, ∑ zⱼ Jⱼ) as a finite double sum. -/
theorem freeCovarianceℂ_bilinear_sum_expansion {n : ℕ}
    (J : Fin n → TestFunctionℂ) (z : Fin n → ℂ) :
    freeCovarianceℂ_bilinear m (∑ i, z i • J i) (∑ j, z j • J j) =
    ∑ i : Fin n, ∑ j : Fin n,
      z i * z j * freeCovarianceℂ_bilinear m (J i) (J j) := by
  rw [freeCovarianceℂ_sum_left m Finset.univ z J]
  congr 1; ext i
  rw [freeCovarianceℂ_sum_right m (J i) Finset.univ z J]
  rw [Finset.mul_sum]; congr 1; ext j; ring

/-- The generating functional for ∑ᵢ zᵢ Jᵢ equals exp of a finite quadratic form. -/
theorem gff_generating_eq_exp_quadratic {n : ℕ}
    (J : Fin n → TestFunctionℂ) (z : Fin n → ℂ) :
    GJGeneratingFunctionalℂ (μ_GFF m) (∑ i, z i • J i) =
    cexp (-(1/2 : ℂ) * ∑ i : Fin n, ∑ j : Fin n,
      z i * z j * freeCovarianceℂ_bilinear m (J i) (J j)) := by
  rw [gff_complex_CF_covariance, freeCovarianceℂ_bilinear_sum_expansion]

/-! ## Analyticity of exp(finite quadratic form)

A finite quadratic form z ↦ ∑ᵢⱼ Aᵢⱼ zᵢ zⱼ is a polynomial, hence analytic.
Composing with exp preserves analyticity. -/

/-- A finite quadratic form ∑ᵢⱼ Aᵢⱼ zᵢ zⱼ is analytic (it's a polynomial). -/
theorem analyticOn_finite_quadratic {n : ℕ} (A : Fin n → Fin n → ℂ) :
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      ∑ i : Fin n, ∑ j : Fin n, z i * z j * A i j) Set.univ := by
  have h_fn_eq : (fun z : Fin n → ℂ => ∑ i : Fin n, ∑ j : Fin n, z i * z j * A i j) =
      ∑ i : Fin n, ∑ j : Fin n, (fun z : Fin n → ℂ => z i * z j * A i j) := by
    ext z; simp [Finset.sum_apply]
  rw [h_fn_eq]
  exact Finset.analyticOn_sum _ fun i _ =>
    Finset.analyticOn_sum _ fun j _ =>
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticOn _|>.mul
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).analyticOn _)).mul
        analyticOn_const

/-- The Gaussian Free Field satisfies the OS0 Analyticity axiom.

    **Direct proof** from the covariance structure: Z[f] = exp(-½ C_ℂ(f,f))
    and C_ℂ is ℂ-bilinear, so Z[∑ zᵢ Jᵢ] = exp(quadratic polynomial in z). -/
theorem gaussianFreeField_satisfies_OS0 : OS0_Analyticity (μ_GFF m) := by
  intro n J
  -- Step 1: Rewrite using the covariance quadratic form
  have h_eq : ∀ z : Fin n → ℂ,
      GJGeneratingFunctionalℂ (μ_GFF m) (∑ i, z i • J i) =
      cexp (-(1/2 : ℂ) * ∑ i : Fin n, ∑ j : Fin n,
        z i * z j * freeCovarianceℂ_bilinear m (J i) (J j)) :=
    fun z => gff_generating_eq_exp_quadratic m J z
  -- Step 2: The quadratic form is analytic
  have h_analytic : AnalyticOn ℂ (fun z : Fin n → ℂ =>
      cexp (-(1/2 : ℂ) * ∑ i : Fin n, ∑ j : Fin n,
        z i * z j * freeCovarianceℂ_bilinear m (J i) (J j))) Set.univ :=
    (analyticOn_const.mul (analyticOn_finite_quadratic
      (fun i j => freeCovarianceℂ_bilinear m (J i) (J j)))).cexp
  -- Step 3: Conclude by pointwise equality
  exact h_analytic.congr (fun z _ => (h_eq z))

end
