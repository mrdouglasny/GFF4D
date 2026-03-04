/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GaussianField Bridge

This file constructs the GFF probability measure on tempered distributions and
establishes its core properties. The measure is constructed via the Minlos theorem
(from the bochner library) applied to the Gaussian characteristic functional
with covariance operator `embeddingMapCLM m`.

## Architecture

The construction has three components:

### 1. Nuclear space axioms
`schwartz_isHilbertNuclear` axioms that Schwartz space 𝓢(ℝ⁴,ℝ) is Hilbert-nuclear
(Gel'fand-Vilenkin, Trèves). `schwartz_separableSpace` axioms that it is separable
(Reed-Simon). Both are required by bochner's Minlos theorem.

### 2. Covariance operator T (concrete — from aqft2)
`embeddingMapCLM m : TestFunction →L[ℝ] L²(ℝ⁴,ℂ)` is fully proved in CovarianceR.lean
with `freeCovarianceFormR_eq_normSq`: C(f,f) = ‖T(f)‖²

### 3. Measure construction (via Minlos theorem)
Given `IsHilbertNuclear TestFunction` and the Gaussian characteristic functional
exp(-½ C(f,f)), the Minlos theorem yields a probability measure on the dual space
with that characteristic functional. The 1D Gaussian pushforward property is
proved from the characteristic functional via Lévy's uniqueness theorem
(`Measure.ext_of_charFun`), and centredness, moments, and Fernique-type bounds
are derived from that.

## Key type identifications

- `FieldConfiguration` is `WeakDual ℝ TestFunction`
- `MeasurableSpace FieldConfiguration` uses `comap (fun ω f => ω f) pi`
- The real inner product on `Lp ℂ 2 volume` comes from `InnerProductSpace.rclikeToReal`
- `@inner ℝ _ _ (T f) (T g) = freeCovarianceFormR m f g` (bridge lemma, by polarization)

## MeasurableSpace transport

The Minlos theorem constructs a measure on bochner's ⨆-comap σ-algebra, while
this project uses comap-pi. These are propositionally equal
(`measurableSpace_comap_eq_bochner`), and the transport is handled by
`integral_cast_ms_prob` (subst + rfl).
-/

import OSforGFF.Basic
import OSforGFF.Covariance
import OSforGFF.CovarianceR
import OSforGFF.Minlos
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Measure.SeparableMeasure

open MeasureTheory ProbabilityTheory TopologicalSpace Complex QFT
open scoped BigOperators NNReal

noncomputable section

namespace GaussianFieldBridge

/-! ## Axioms

This file contains two axioms:
- `schwartz_isHilbertNuclear`: Schwartz space is Hilbert-nuclear (Gel'fand-Vilenkin)
- `schwartz_separableSpace`: Schwartz space is separable (Reed-Simon)

The Gaussian pushforward property (`gfMeasure_pairing_is_gaussian`) is proved
from the characteristic functional via Lévy's uniqueness theorem. -/

/-- Schwartz space 𝓢(ℝ⁴,ℝ) is Hilbert-nuclear (Gel'fand-Vilenkin, Trèves).
    This is the nuclearity condition required by bochner's Minlos theorem. -/
axiom schwartz_isHilbertNuclear : IsHilbertNuclear TestFunction

attribute [instance] schwartz_isHilbertNuclear

/-- Schwartz space is separable (Fréchet space with countable seminorms).
    Standard result (Reed-Simon, Vol. 1); synthesis gap in Mathlib.
    Proved in gaussian-field library (`SchwartzNuclear.HermiteNuclear.schwartz_separableSpace`)
    via the Hermite basis expansion `hasSum_basisVec` + CLE transfer. -/
axiom schwartz_separableSpace : SeparableSpace TestFunction

attribute [instance] schwartz_separableSpace

/-- Schwartz space is nonempty (the zero function is Schwartz). -/
instance schwartz_nonempty : Nonempty TestFunction := ⟨0⟩

/-! ## Instance Setup

We need `InnerProductSpace ℝ (TargetHilbertSpace m)` since the Minlos construction
requires a real inner product space for the Gaussian RBF positive-definiteness proof.
The target `Lp ℂ 2 volume` has `InnerProductSpace ℂ _`; we obtain the real instance
via `InnerProductSpace.rclikeToReal`. -/

/-- Real inner product space structure on the target Hilbert space.
    Under this instance, `@inner ℝ _ _ x y = re ⟪x, y⟫_ℂ` and
    `@inner ℝ _ _ x x = ‖x‖²`. -/
instance instInnerProductSpaceReal (m : ℝ) :
    InnerProductSpace ℝ (TargetHilbertSpace m) :=
  InnerProductSpace.rclikeToReal ℂ _

/-- L²(ℝ⁴, ℂ) is separable (second countable → separable). -/
instance instSeparableSpaceTargetHilbertSpace (m : ℝ) : SeparableSpace (TargetHilbertSpace m) := by
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  haveI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  exact @SecondCountableTopology.to_separableSpace _ _
    (MeasureTheory.Lp.SecondCountableTopology (E := ℂ) (p := 2) (μ := volume))

/-! ## Bridge Lemma: Inner Product = Covariance

The key link between the inner product `@inner ℝ H _ (T f) (T g)` and
`freeCovarianceFormR m f g`. The diagonal case follows from:
  `@inner ℝ _ _ x x = ‖x‖²` and `freeCovarianceFormR_eq_normSq`
The cross-term case follows by polarization of both bilinear forms. -/

/-- Diagonal case: ⟨T(f), T(f)⟩_ℝ = ‖T(f)‖² = C(f,f). -/
theorem inner_embeddingMapCLM_self (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
    @inner ℝ (TargetHilbertSpace m) (instInnerProductSpaceReal m).toInner
      (embeddingMapCLM m f) (embeddingMapCLM m f) =
    freeCovarianceFormR m f f := by
  rw [real_inner_self_eq_norm_sq]
  rw [embeddingMapCLM_apply]
  exact (freeCovarianceFormR_eq_normSq m f).symm

/-- Cross-term case: ⟨T(f), T(g)⟩_ℝ = C(f,g), by polarization.
    Both sides are symmetric bilinear forms agreeing on diagonals,
    so they agree everywhere by the polarization identity
    4⟨x,y⟩ = ‖x+y‖² - ‖x-y‖². -/
theorem inner_embeddingMapCLM_eq_freeCovarianceFormR
    (m : ℝ) [Fact (0 < m)] (f g : TestFunction) :
    @inner ℝ (TargetHilbertSpace m) (instInnerProductSpaceReal m).toInner
      (embeddingMapCLM m f) (embeddingMapCLM m g) =
    freeCovarianceFormR m f g := by
  -- Polarization: 4⟨x,y⟩ = ‖x+y‖² - ‖x-y‖² = C(f+g,f+g) - C(f-g,f-g)
  have h_inner_polar :
      @inner ℝ (TargetHilbertSpace m) (instInnerProductSpaceReal m).toInner
        (embeddingMapCLM m f) (embeddingMapCLM m g) =
      (1/4) * (@inner ℝ (TargetHilbertSpace m) (instInnerProductSpaceReal m).toInner
                  (embeddingMapCLM m (f + g)) (embeddingMapCLM m (f + g)) -
                @inner ℝ (TargetHilbertSpace m) (instInnerProductSpaceReal m).toInner
                  (embeddingMapCLM m (f - g)) (embeddingMapCLM m (f - g))) := by
    set x := embeddingMapCLM m f
    set y := embeddingMapCLM m g
    have hmap_add : embeddingMapCLM m (f + g) = x + y := map_add _ f g
    have hmap_sub : embeddingMapCLM m (f - g) = x - y := map_sub _ f g
    rw [hmap_add, hmap_sub]
    rw [inner_add_left, inner_add_right, inner_add_right,
        inner_sub_left, inner_sub_right, inner_sub_right]
    have hcomm : @inner ℝ (TargetHilbertSpace m)
        (instInnerProductSpaceReal m).toInner y x =
      @inner ℝ (TargetHilbertSpace m)
        (instInnerProductSpaceReal m).toInner x y := by
      simp only [instInnerProductSpaceReal, InnerProductSpace.rclikeToReal,
        Inner.rclikeToReal]
      exact (inner_re_symm (𝕜 := ℂ) x y).symm
    linarith
  have h_cov_polar :
      freeCovarianceFormR m f g =
      (1/4) * (freeCovarianceFormR m (f + g) (f + g) - freeCovarianceFormR m (f - g) (f - g)) := by
    -- Expand C(f+g, f+g)
    have h_plus : freeCovarianceFormR m (f + g) (f + g) =
        freeCovarianceFormR m f f + freeCovarianceFormR m f g +
        freeCovarianceFormR m g f + freeCovarianceFormR m g g := by
      rw [freeCovarianceFormR_add_left, freeCovarianceFormR_add_right,
          freeCovarianceFormR_add_right]
      ring
    -- Express f - g = f + (-1) • g for subtraction
    have hsub : f - g = f + (-1 : ℝ) • g := by ext y; simp [sub_eq_add_neg]
    -- Expand C(f-g, f-g)
    have h_minus : freeCovarianceFormR m (f - g) (f - g) =
        freeCovarianceFormR m f f - freeCovarianceFormR m f g -
        freeCovarianceFormR m g f + freeCovarianceFormR m g g := by
      rw [hsub, freeCovarianceFormR_add_left, freeCovarianceFormR_smul_left,
          freeCovarianceFormR_add_right, freeCovarianceFormR_add_right,
          freeCovarianceFormR_smul_right, freeCovarianceFormR_smul_right]
      ring
    rw [h_plus, h_minus, freeCovarianceFormR_symm m g f]
    ring
  rw [h_inner_polar, h_cov_polar,
      inner_embeddingMapCLM_self, inner_embeddingMapCLM_self]

/-! ## The GFF Measure

The measure is constructed via the Minlos theorem applied to the Gaussian
characteristic functional exp(-½ C(f,f)). The 1D Gaussian pushforward property
is an axiom, from which all other properties are derived. -/

/-- Integral is invariant under propositional MeasurableSpace transport
    through ProbabilityMeasure.toMeasure. -/
private lemma integral_cast_ms_prob {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ms1 ms2 : MeasurableSpace α} (h : ms1 = ms2)
    (pm : @ProbabilityMeasure α ms2) (f : α → E) :
    @integral α E _ _ ms1 (@ProbabilityMeasure.toMeasure α ms1 (h ▸ pm)) f =
    @integral α E _ _ ms2 (@ProbabilityMeasure.toMeasure α ms2 pm) f := by
  subst h; rfl

private def gfMeasure_aux (m : ℝ) [Fact (0 < m)] :
    { μ : ProbabilityMeasure FieldConfiguration //
      ∀ f : TestFunction,
        ∫ ω, Complex.exp (Complex.I * ↑(ω f))
          ∂μ.toMeasure =
        gaussian_characteristic_functional (freeCovarianceFormR m) f } := by
  letI := instInnerProductSpaceReal m
  letI := instSeparableSpaceTargetHilbertSpace m
  -- Get the Minlos measure (on bochner's ⨆-comap σ-algebra)
  have h_minlos := gaussian_measure_characteristic_functional
    (embeddingMapCLM m).toLinearMap
    (freeCovarianceFormR m)
    (fun f => by
      rw [freeCovarianceFormR_eq_normSq]; congr 2; exact (embeddingMapCLM_apply m f).symm)
    trivial
    (freeCovarianceFormR_zero_left m 0)
    (freeCovarianceFormR_continuous m)
  -- Transport from bochner's σ-algebra to ours
  have h_ms_eq : instMeasurableSpaceFieldConfiguration =
    (⨆ (f : TestFunction), (borel ℝ).comap
      (fun l : WeakDual ℝ TestFunction => (l : TestFunction →L[ℝ] ℝ) f)) :=
    measurableSpace_comap_eq_bochner
  refine ⟨h_ms_eq ▸ h_minlos.choose, fun f => ?_⟩
  rw [integral_cast_ms_prob h_ms_eq]
  exact h_minlos.choose_spec f

/-- The GFF measure, constructed via the Minlos theorem applied to the Gaussian
    characteristic functional with covariance `freeCovarianceFormR m`. -/
def gfMeasure (m : ℝ) [Fact (0 < m)] : ProbabilityMeasure FieldConfiguration :=
  (gfMeasure_aux m).val

/-- The characteristic functional of gfMeasure: E[exp(i⟨ω,f⟩)] = exp(-½ C(f,f)).

    Follows from `gaussian_measure_characteristic_functional` + σ-algebra transport. -/
theorem gfMeasure_charFun (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
    ∫ ω, Complex.exp (Complex.I * ↑(distributionPairing ω f))
      ∂(gfMeasure m).toMeasure =
    Complex.exp (-(1/2 : ℂ) * ↑(freeCovarianceFormR m f f)) := by
  have h := (gfMeasure_aux m).property f
  simp only [gaussian_characteristic_functional, gfMeasure, distributionPairing] at h ⊢
  exact h

/-- Pushforward by ω ↦ ω(φ) is N(0, C(φ,φ)).

    Proof: By Lévy's uniqueness theorem (`Measure.ext_of_charFun`), it suffices to
    match characteristic functions. The charFun of the pushforward μ.map(eval_φ) at t
    equals the char functional applied to t·φ (linearity), which by `gfMeasure_charFun`
    equals exp(-½ t² C(φ,φ)) — exactly `charFun_gaussianReal` of N(0, C(φ,φ)). -/
theorem gfMeasure_pairing_is_gaussian (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
    (gfMeasure m).toMeasure.map (distributionPairingCLM φ)
      = gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal := by
  -- The pushforward is a probability measure
  haveI : IsProbabilityMeasure ((gfMeasure m).toMeasure.map (distributionPairingCLM φ)) :=
    Measure.isProbabilityMeasure_map (fieldConfiguration_eval_measurable φ).aemeasurable
  -- By Lévy uniqueness: same char functions → same measures
  apply Measure.ext_of_charFun
  funext t
  -- LHS: charFun of the pushforward. Unfold only the LHS.
  conv_lhs => rw [charFun_apply_real]
  -- Change of variables via integral_map
  have h_map : ∫ x, cexp (↑t * ↑x * I)
      ∂((gfMeasure m).toMeasure.map (distributionPairingCLM φ))
    = ∫ ω, cexp (↑t * ↑(distributionPairingCLM φ ω) * I)
      ∂(gfMeasure m).toMeasure :=
    integral_map (fieldConfiguration_eval_measurable φ).aemeasurable (by fun_prop)
  rw [h_map]
  -- Use char functional at t • φ
  have h_char := gfMeasure_charFun m (t • φ)
  simp only [map_smul, smul_eq_mul, distributionPairing] at h_char
  -- Match integrands: t * (ω φ) * I = I * ↑(t * ω(φ))
  simp_rw [distributionPairingCLM_apply, distributionPairing]
  simp_rw [show ∀ (ω : FieldConfiguration), (↑t : ℂ) * ↑(ω φ) * I = I * ↑(t * ω φ)
    from fun ω => by push_cast; ring]
  rw [h_char]
  -- RHS: unfold charFun of gaussianReal 0 σ²
  rw [charFun_gaussianReal]
  -- Both sides are complex exponentials; show the arguments match
  congr 1
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [freeCovarianceFormR_smul_left, freeCovarianceFormR_smul_right]
  rw [Real.coe_toNNReal _ (freeCovarianceFormR_pos m φ)]
  push_cast; ring

/-! ## Derived properties

All of the following are derived from `gfMeasure_pairing_is_gaussian` using
Mathlib's `gaussianReal` API. -/

/-- The measure is centered: E[ω(f)] = 0.
    Derived from: the mean of gaussianReal 0 σ² is 0. -/
theorem gfMeasure_centered (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
    ∫ ω, distributionPairingCLM f ω ∂(gfMeasure m).toMeasure = 0 := by
  simp only [distributionPairingCLM_apply, distributionPairing]
  have h_gauss : (gfMeasure m).toMeasure.map (fun ω : FieldConfiguration => ω f)
      = gaussianReal 0 (freeCovarianceFormR m f f).toNNReal := by
    have := gfMeasure_pairing_is_gaussian m f
    simp only [distributionPairingCLM_apply, distributionPairing] at this
    exact this
  have h_map := integral_map (fieldConfiguration_eval_measurable f).aemeasurable
    (measurable_id.aestronglyMeasurable
      (μ := (gfMeasure m).toMeasure.map (fun ω : FieldConfiguration => ω f)))
  simp only [id] at h_map
  rw [h_map.symm, h_gauss, integral_id_gaussianReal]

/-- Second moment: E[ω(f)²] = C(f,f).
    Derived from: the variance of gaussianReal 0 σ² is σ². -/
theorem gfMeasure_second_moment (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
    ∫ ω, (distributionPairingCLM φ ω)^2 ∂(gfMeasure m).toMeasure =
    freeCovarianceFormR m φ φ := by
  simp only [distributionPairingCLM_apply, distributionPairing]
  -- Convert the Gaussian pushforward to use the lambda form
  have h_gauss : (gfMeasure m).toMeasure.map (fun ω : FieldConfiguration => ω φ)
      = gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal := by
    have := gfMeasure_pairing_is_gaussian m φ
    simp only [distributionPairingCLM_apply, distributionPairing] at this
    exact this
  set σ := (freeCovarianceFormR m φ φ).toNNReal with hσ_def
  -- variance = second moment since mean = 0
  have h_var : Var[fun ω : FieldConfiguration => ω φ; (gfMeasure m).toMeasure] =
      ∫ ω, (ω φ) ^ 2 ∂(gfMeasure m).toMeasure :=
    variance_of_integral_eq_zero
      (fieldConfiguration_eval_measurable φ).aemeasurable
      (gfMeasure_centered m φ)
  -- Compute variance via pushforward
  have h_var2 : Var[fun ω : FieldConfiguration => ω φ; (gfMeasure m).toMeasure] = σ := by
    have h : Var[fun x : ℝ => x;
        (gfMeasure m).toMeasure.map (fun ω : FieldConfiguration => ω φ)] =
        Var[fun ω : FieldConfiguration => ω φ; (gfMeasure m).toMeasure] :=
      variance_map aemeasurable_id (fieldConfiguration_eval_measurable φ).aemeasurable
    rw [← h, h_gauss, variance_fun_id_gaussianReal]
  rw [← h_var, h_var2, hσ_def]
  exact Real.coe_toNNReal _ (freeCovarianceFormR_pos m φ)

/-- Fernique-type: pairings are in Lᵖ for all finite p.
    Derived from: gaussianReal has all finite moments. -/
theorem gfMeasure_pairing_memLp (m : ℝ) [Fact (0 < m)]
    (φ : TestFunction) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (distributionPairingCLM φ) p (gfMeasure m).toMeasure := by
  -- Convert to lambda form for compatibility with map lemmas
  suffices h : MemLp (fun ω : FieldConfiguration => ω φ) p (gfMeasure m).toMeasure by
    exact h
  have h_gauss : (gfMeasure m).toMeasure.map (fun ω : FieldConfiguration => ω φ)
      = gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal := by
    have := gfMeasure_pairing_is_gaussian m φ
    simp only [distributionPairingCLM_apply, distributionPairing] at this
    exact this
  have hp' : (p.toNNReal : ENNReal) = p := ENNReal.coe_toNNReal hp
  rw [← hp']
  have h_memLp : MemLp id p.toNNReal
      (gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal) :=
    memLp_id_gaussianReal p.toNNReal
  rw [← h_gauss] at h_memLp
  rwa [memLp_map_measure_iff h_memLp.aestronglyMeasurable
    (fieldConfiguration_eval_measurable φ).aemeasurable] at h_memLp

/-- Fernique exponential form: ∃ α > 0, exp(α·ω(f)²) is integrable.
    Derived from the Gaussian pushforward: the pairing has distribution N(0, σ²)
    where σ² = C(φ,φ), so exp(α·x²) is integrable for any α < 1/(2σ²). -/
theorem gfMeasure_pairing_expSq_integrable (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
    ∃ α : ℝ, 0 < α ∧
      Integrable (fun ω => Real.exp (α * (distributionPairingCLM φ ω)^2))
        (gfMeasure m).toMeasure := by
  -- The pushforward by ω ↦ ω(φ) is gaussianReal, which is IsGaussian
  have h_push := gfMeasure_pairing_is_gaussian m φ
  set ν := (gfMeasure m).toMeasure.map (distributionPairingCLM φ) with hν_def
  haveI : ProbabilityTheory.IsGaussian ν := h_push ▸ inferInstance
  -- Fernique's theorem on ℝ: ∃ C > 0, exp(C * ‖x‖²) integrable under ν
  obtain ⟨C, hC_pos, hC_int⟩ := IsGaussian.exists_integrable_exp_sq ν
  -- On ℝ, ‖x‖² = x², so this is exp(C * x²) integrable under the pushforward
  have h_eq : (fun x : ℝ => Real.exp (C * ‖x‖ ^ 2)) = (fun x => Real.exp (C * x ^ 2)) := by
    ext x; simp [Real.norm_eq_abs, sq_abs]
  rw [h_eq] at hC_int
  -- Pull back: integrable on pushforward → integrable on original
  refine ⟨C, hC_pos, ?_⟩
  rw [hν_def] at hC_int
  exact hC_int.comp_measurable (fieldConfiguration_eval_measurable φ)

/-! ## Derived theorems

These connect gfMeasure to aqft2's existing interface definitions
(GJGeneratingFunctional, GJMean) so it can serve as a drop-in replacement
for μ_GFF in the OS axiom proofs. -/

/-- GJ generating functional has the Gaussian form. -/
theorem gfMeasure_real_characteristic (m : ℝ) [Fact (0 < m)] :
    ∀ f : TestFunction,
      GJGeneratingFunctional (gfMeasure m) f =
      Complex.exp (-(1/2 : ℂ) * ↑(freeCovarianceFormR m f f)) := by
  intro f
  unfold GJGeneratingFunctional distributionPairing
  exact gfMeasure_charFun m f

/-- gfMeasure is centered in the GJ sense. -/
theorem gfMeasure_isCenteredGJ (m : ℝ) [Fact (0 < m)] :
    ∀ (f : TestFunction), GJMean (gfMeasure m) f = 0 := by
  intro f
  unfold GJMean distributionPairing
  exact gfMeasure_centered m f

/-- The square of the pairing is integrable. -/
theorem gfMeasure_pairing_square_integrable (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
    Integrable (fun ω => (distributionPairing ω φ) ^ 2)
      (gfMeasure m).toMeasure := by
  have h_memLp := gfMeasure_pairing_memLp m φ ((2 : ℕ) : ENNReal) (by simp)
  have h_integrable_CLM := h_memLp.integrable_sq
  simpa [distributionPairingCLM_apply] using h_integrable_CLM

end GaussianFieldBridge
