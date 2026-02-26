/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GaussianField Bridge

This file connects the aqft2 covariance operator to the GaussianField library's
measure construction. All former axioms are now theorems, derived from the
generic construction in gaussian-field applied to `embeddingMapCLM m`.

## Architecture

The construction has three components:

### 1. NuclearSpace instance (from gaussian-field)
`NuclearSpace TestFunction` comes from `schwartz_nuclearSpace` in gaussian-field's
Axioms.lean, which provides `NuclearSpace (SchwartzMap D F)` for any finite-dimensional
domain D and normed codomain F. Since `TestFunction = SchwartzMap SpaceTime ℝ` and
`SpaceTime = EuclideanSpace ℝ (Fin 4)` is finite-dimensional, this applies directly.

### 2. Covariance operator T (concrete — from aqft2)
`embeddingMapCLM m : TestFunction →L[ℝ] L²(ℝ⁴,ℂ)` is fully proved in CovarianceR.lean
with `freeCovarianceFormR_eq_normSq`: C(f,f) = ‖T(f)‖²

### 3. Measure construction (from gaussian-field)
Given NuclearSpace E and T : E →L[ℝ] H, GaussianField.measure produces a probability
measure with characteristic functional exp(-½⟨T(f), T(f)⟩_H). The inner product
form connects to freeCovarianceFormR via the bridge lemma
`inner_embeddingMapCLM_eq_freeCovarianceFormR`.

## Key type identifications

- `FieldConfiguration = GaussianField.Configuration TestFunction` (both are `WeakDual ℝ TestFunction`)
- `MeasurableSpace FieldConfiguration` = `GaussianField.instMeasurableSpaceConfiguration`
  (both are `MeasurableSpace.comap (fun ω f => ω f) MeasurableSpace.pi`)
- The real inner product on `Lp ℂ 2 volume` comes from `InnerProductSpace.rclikeToReal`
- `@inner ℝ _ _ (T f) (T g) = freeCovarianceFormR m f g` (bridge lemma, by polarization)
-/

import OSforGFF.Basic
import OSforGFF.Covariance
import OSforGFF.CovarianceR
import GaussianField
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Measure.SeparableMeasure

open MeasureTheory ProbabilityTheory TopologicalSpace Complex QFT
open scoped BigOperators NNReal

noncomputable section

namespace GaussianFieldBridge

/-! ## Instance Setup

We need `InnerProductSpace ℝ (TargetHilbertSpace m)` since gaussian-field's construction
requires a real inner product space. The target `Lp ℂ 2 volume` has
`InnerProductSpace ℂ _`; we obtain the real instance via `InnerProductSpace.rclikeToReal`. -/

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

The key link between gaussian-field's `@inner ℝ H _ (T f) (T g)` and aqft2's
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

All former axioms are now theorems, derived from gaussian-field's generic
construction applied to `embeddingMapCLM m`. -/

/-- The GFF measure from GaussianField, using `embeddingMapCLM m` as the
    covariance operator. -/
def gfMeasure (m : ℝ) [Fact (0 < m)] : ProbabilityMeasure FieldConfiguration :=
  letI := instInnerProductSpaceReal m
  letI := instSeparableSpaceTargetHilbertSpace m
  ⟨GaussianField.measure (embeddingMapCLM m),
   GaussianField.measure_isProbability (embeddingMapCLM m)⟩

/-- The underlying measure of gfMeasure is GaussianField.measure. -/
theorem gfMeasure_toMeasure (m : ℝ) [Fact (0 < m)] :
    (gfMeasure m).toMeasure =
    letI := instInnerProductSpaceReal m
    letI := instSeparableSpaceTargetHilbertSpace m
    GaussianField.measure (embeddingMapCLM m) := rfl

/-- Characteristic functional: E[exp(i⟨ω,f⟩)] = exp(-½ C(f,f)). -/
theorem gfMeasure_charFun (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
    ∫ ω, Complex.exp (Complex.I * ↑(distributionPairing ω f))
      ∂(gfMeasure m).toMeasure =
    Complex.exp (-(1/2 : ℂ) * ↑(freeCovarianceFormR m f f)) := by
  letI := instInnerProductSpaceReal m
  letI := instSeparableSpaceTargetHilbertSpace m
  rw [gfMeasure_toMeasure]
  have h := GaussianField.charFun (embeddingMapCLM m) f
  rw [inner_embeddingMapCLM_self] at h
  exact h

/-- Pushforward by ω ↦ ω(f) is N(0, C(f,f)). -/
theorem gfMeasure_pairing_is_gaussian (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
    (gfMeasure m).toMeasure.map (distributionPairingCLM φ)
      = gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal := by
  letI := instInnerProductSpaceReal m
  letI := instSeparableSpaceTargetHilbertSpace m
  rw [gfMeasure_toMeasure]
  have h := GaussianField.pairing_is_gaussian (embeddingMapCLM m) φ
  rw [inner_embeddingMapCLM_self] at h
  exact h

/-- Fernique-type: pairings are in Lᵖ for all finite p. -/
theorem gfMeasure_pairing_memLp (m : ℝ) [Fact (0 < m)]
    (φ : TestFunction) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (distributionPairingCLM φ) p (gfMeasure m).toMeasure := by
  letI := instInnerProductSpaceReal m
  letI := instSeparableSpaceTargetHilbertSpace m
  -- gaussian-field's pairing_memLp takes ℝ≥0, so we need to cast
  have hp' : (p.toNNReal : ENNReal) = p := ENNReal.coe_toNNReal hp
  rw [← hp']
  exact GaussianField.pairing_memLp (embeddingMapCLM m) φ p.toNNReal

/-- The measure is centered: E[ω(f)] = 0. -/
theorem gfMeasure_centered (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
    ∫ ω, distributionPairingCLM f ω ∂(gfMeasure m).toMeasure = 0 := by
  letI := instInnerProductSpaceReal m
  letI := instSeparableSpaceTargetHilbertSpace m
  -- distributionPairingCLM f ω = ω f by definition
  simp only [distributionPairingCLM_apply, distributionPairing]
  exact GaussianField.measure_centered (embeddingMapCLM m) f

/-- Second moment: E[ω(f)²] = C(f,f). -/
theorem gfMeasure_second_moment (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
    ∫ ω, (distributionPairingCLM φ ω)^2 ∂(gfMeasure m).toMeasure =
    freeCovarianceFormR m φ φ := by
  letI := instInnerProductSpaceReal m
  letI := instSeparableSpaceTargetHilbertSpace m
  simp only [distributionPairingCLM_apply, distributionPairing]
  have h := GaussianField.second_moment_eq_covariance (embeddingMapCLM m) φ
  rw [inner_embeddingMapCLM_self] at h
  exact h

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
