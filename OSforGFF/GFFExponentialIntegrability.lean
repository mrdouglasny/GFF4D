/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic

import OSforGFF.Basic
import OSforGFF.ComplexTestFunction
import OSforGFF.GFFMconstruct

/-!
## GFF Exponential Integrability

Shared utility lemmas for the GFF measure: measurability of the complex pairing,
and Fernique-type exponential integrability results.

These are factored out of the old OS0_GFF.lean (now in old/) so that downstream files
(OS4_Ergodicity, OS4_MGF, GFFIsGaussian) can use them without importing the full
old OS0 proof and its dependency on `differentiable_analyticAt_finDim`.
-/

open MeasureTheory Complex QFT
open scoped BigOperators

noncomputable section

namespace QFT

variable (m : ℝ) [Fact (0 < m)]

/-- The complex pairing is continuous in ω.
    This follows from the continuity of the evaluation map on WeakDual. -/
theorem distributionPairingℂ_real_continuous (f : TestFunctionℂ) :
    Continuous (fun ω : FieldConfiguration => distributionPairingℂ_real ω f) := by
  simp only [distributionPairingℂ_real, complex_testfunction_decompose]
  have h_re : Continuous (fun ω : FieldConfiguration => (ω (schwartz_comp_clm f Complex.reCLM) : ℂ)) :=
    Complex.continuous_ofReal.comp (WeakDual.eval_continuous _)
  have h_im : Continuous (fun ω : FieldConfiguration => (ω (schwartz_comp_clm f Complex.imCLM) : ℂ)) :=
    Complex.continuous_ofReal.comp (WeakDual.eval_continuous _)
  exact h_re.add (continuous_const.mul h_im)

/-- The complex pairing is measurable in ω (w.r.t. the cylindrical σ-algebra).
    Since each evaluation ω ↦ ω g is cylindrically measurable, and ofReal, add, mul are
    Borel-measurable, the composition is measurable. -/
@[fun_prop]
theorem distributionPairingℂ_real_measurable (f : TestFunctionℂ) :
    Measurable (fun ω : FieldConfiguration => distributionPairingℂ_real ω f) := by
  simp only [distributionPairingℂ_real, complex_testfunction_decompose]
  exact (Complex.continuous_ofReal.measurable.comp (fieldConfiguration_eval_measurable _)).add
    (measurable_const.mul (Complex.continuous_ofReal.measurable.comp (fieldConfiguration_eval_measurable _)))

/-- exp(|ω f|) is in L^p (for all p < ∞) under the GFF measure.
    This follows from Fernique's theorem: if exp(α x²) is integrable, then exp(|x|)^p is integrable
    for all p < ∞ because |x|^p ≤ C_p * exp(ε x²) for small ε. -/
lemma gff_exp_abs_pairing_memLp (f : TestFunction) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (fun ω : FieldConfiguration => Real.exp |ω f|) p (μ_GFF m).toMeasure := by
  obtain ⟨α, hα_pos, h_fernique⟩ := gaussianFreeField_pairing_expSq_integrable m f
  rcases eq_or_ne p 0 with rfl | hp_pos
  · exact memLp_zero_iff_aestronglyMeasurable.mpr
      (Real.continuous_exp.measurable.comp (continuous_abs.measurable.comp (fieldConfiguration_eval_measurable f))).aestronglyMeasurable
  have h_aesm : AEStronglyMeasurable (fun ω => Real.exp |ω f|) (μ_GFF m).toMeasure :=
    (Real.continuous_exp.measurable.comp (continuous_abs.measurable.comp (fieldConfiguration_eval_measurable f))).aestronglyMeasurable
  have h_young : ∀ x : ℝ, p.toReal * |x| ≤ p.toReal^2 / (4 * α) + α * x^2 := fun x => by
    have hα_ne : α ≠ 0 := ne_of_gt hα_pos
    have h_sqrt_pos : Real.sqrt α > 0 := Real.sqrt_pos.mpr hα_pos
    have h_sqrt_sq : Real.sqrt α ^ 2 = α := Real.sq_sqrt (le_of_lt hα_pos)
    have ha : p.toReal / (2 * Real.sqrt α) = p.toReal / 2 / Real.sqrt α := by ring
    have hb_sq : (Real.sqrt α * |x|)^2 = α * x^2 := by rw [mul_pow, h_sqrt_sq, sq_abs]
    have ha_sq : (p.toReal / (2 * Real.sqrt α))^2 = p.toReal^2 / (4 * α) := by
      rw [div_pow, mul_pow, h_sqrt_sq]; ring
    have hab : 2 * (p.toReal / (2 * Real.sqrt α)) * (Real.sqrt α * |x|) = p.toReal * |x| := by
      field_simp
    have h_sq := sq_nonneg (p.toReal / (2 * Real.sqrt α) - Real.sqrt α * |x|)
    calc p.toReal * |x| = 2 * (p.toReal / (2 * Real.sqrt α)) * (Real.sqrt α * |x|) := hab.symm
      _ ≤ (p.toReal / (2 * Real.sqrt α))^2 + (Real.sqrt α * |x|)^2 := by nlinarith [h_sq]
      _ = p.toReal^2 / (4 * α) + α * x^2 := by rw [ha_sq, hb_sq]
  have h_exp_bound : ∀ x : ℝ,
      Real.exp (p.toReal * |x|) ≤ Real.exp (p.toReal^2 / (4 * α)) * Real.exp (α * x^2) := fun x => by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (h_young x)
  let C := Real.exp (p.toReal^2 / (4 * α))
  have h_dom : Integrable (fun ω => C * Real.exp (α * (ω f)^2)) (μ_GFF m).toMeasure := by
    have h_const_mul : Integrable (fun ω => C * Real.exp (α * (distributionPairingCLM f ω)^2)) (μ_GFF m).toMeasure := by
      exact h_fernique.const_mul C
    simp only [distributionPairingCLM_apply, distributionPairing] at h_const_mul
    exact h_const_mul
  have h_norm_pow_bound : ∀ ω : FieldConfiguration,
      Real.exp (p.toReal * |ω f|) ≤ C * Real.exp (α * (ω f)^2) := fun ω => by
    have h1 := h_exp_bound (ω f)
    exact h1
  have h_exp_p_integrable : Integrable (fun ω => Real.exp (p.toReal * |ω f|)) (μ_GFF m).toMeasure := by
    have h_meas : AEStronglyMeasurable (fun ω => Real.exp (p.toReal * |ω f|)) (μ_GFF m).toMeasure :=
      (Real.continuous_exp.measurable.comp (measurable_const.mul (continuous_abs.measurable.comp
        (fieldConfiguration_eval_measurable f)))).aestronglyMeasurable
    apply h_dom.mono' h_meas
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact h_norm_pow_bound ω
  have h_norm_rpow : ∀ x : ℝ, ‖Real.exp |x|‖ ^ p.toReal = Real.exp (p.toReal * |x|) := fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_mul]
    congr 1
    ring
  have h_eLpNorm_lt : eLpNorm (fun ω => Real.exp |ω f|) p (μ_GFF m).toMeasure < ⊤ := by
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_pos hp]
    have h_eq : ∀ ω : FieldConfiguration,
        (‖Real.exp |ω f|‖ₑ : ENNReal) ^ p.toReal = ENNReal.ofReal (Real.exp (p.toReal * |ω f|)) := by
      intro ω
      have h_pos : 0 < Real.exp |ω f| := Real.exp_pos _
      rw [Real.enorm_eq_ofReal (le_of_lt h_pos)]
      rw [ENNReal.ofReal_rpow_of_nonneg (le_of_lt h_pos) (ENNReal.toReal_nonneg)]
      congr 1
      rw [← Real.exp_mul]
      ring_nf
    simp_rw [h_eq]
    have h_fin := h_exp_p_integrable.hasFiniteIntegral
    rw [HasFiniteIntegral] at h_fin
    convert h_fin using 1
    apply lintegral_congr
    intro ω
    rw [Real.enorm_eq_ofReal (le_of_lt (Real.exp_pos _))]
  exact ⟨h_aesm, h_eLpNorm_lt⟩

/-- Integrability of exp(|ω f|) under the GFF measure.
    This is the L¹ special case of gff_exp_abs_pairing_memLp. -/
lemma gff_exp_abs_pairing_integrable (f : TestFunction) :
    Integrable (fun ω : FieldConfiguration => Real.exp |ω f|) (μ_GFF m).toMeasure :=
  memLp_one_iff_integrable.mp (gff_exp_abs_pairing_memLp m f 1 ENNReal.one_ne_top)

/-- Product of exponentials of absolute pairings is in L².
    If we have k test functions g₁, ..., gₖ, then exp(∑ᵢ |ω gᵢ|) = ∏ᵢ exp(|ω gᵢ|).
    Each exp(|ω gᵢ|) ∈ L^(2k) by gff_exp_abs_pairing_memLp.
    By generalized Hölder (MemLp.prod'), a product of k functions in L^(2k) is in L². -/
lemma gff_exp_abs_sum_memLp {ι : Type*} (s : Finset ι) (g : ι → TestFunction) :
    MemLp (fun ω : FieldConfiguration => Real.exp (∑ i ∈ s, |ω (g i)|)) 2 (μ_GFF m).toMeasure := by
  have h_eq : (fun ω : FieldConfiguration => Real.exp (∑ i ∈ s, |ω (g i)|)) =
              (fun ω : FieldConfiguration => ∏ i ∈ s, Real.exp |ω (g i)|) := by
    ext ω; exact Real.exp_sum s (fun i => |ω (g i)|)
  rw [h_eq]
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [memLp_const]
  let k : ℕ := s.card
  have hk_pos : 0 < k := Finset.card_pos.mpr hs
  have h_each : ∀ i ∈ s, MemLp (fun ω : FieldConfiguration => Real.exp |ω (g i)|)
      (2 * k : ℕ) (μ_GFF m).toMeasure := by
    intro i _
    exact gff_exp_abs_pairing_memLp m (g i) (2 * k : ℕ) (ENNReal.natCast_ne_top _)
  have h_prod := MemLp.prod' (s := s) (p := fun _ => (2 * k : ℕ))
    (f := fun i (ω : FieldConfiguration) => Real.exp |ω (g i)|)
    (fun i hi => h_each i hi)
  convert h_prod using 1
  rw [Finset.sum_const, nsmul_eq_mul]
  have hk_ne_zero : (s.card : ENNReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact hk_pos.ne'
  have hk_ne_top : (s.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top s.card
  simp only [k]
  have h_cast : ((2 * s.card : ℕ) : ENNReal) = 2 * s.card := by norm_cast
  rw [h_cast]
  have h2_ne_zero : (2 : ENNReal) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ENNReal) ≠ ⊤ := by norm_num
  rw [ENNReal.mul_inv (Or.inl h2_ne_zero) (Or.inl h2_ne_top)]
  rw [mul_comm (2 : ENNReal)⁻¹ (s.card : ENNReal)⁻¹]
  rw [← mul_assoc]
  rw [ENNReal.mul_inv_cancel hk_ne_zero hk_ne_top]
  rw [one_mul]
  simp only [inv_inv]

end QFT

end
