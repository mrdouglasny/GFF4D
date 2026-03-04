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

### 1. Nuclear space axiom
`schwartz_isHilbertNuclear` axioms that Schwartz space 𝓢(ℝ⁴,ℝ) is Hilbert-nuclear
(Gel'fand-Vilenkin, Trèves). This is the type class required by bochner's Minlos theorem.

### 2. Covariance operator T (concrete — from aqft2)
`embeddingMapCLM m : TestFunction →L[ℝ] L²(ℝ⁴,ℂ)` is fully proved in CovarianceR.lean
with `freeCovarianceFormR_eq_normSq`: C(f,f) = ‖T(f)‖²

### 3. Measure construction (via Minlos theorem)
Given `IsHilbertNuclear TestFunction` and the Gaussian characteristic functional
exp(-½ C(f,f)), the Minlos theorem yields a probability measure on the dual space
with that characteristic functional. The 1D Gaussian pushforward property is
an axiom (`gff_pairing_is_gaussian_axiom`), from which centredness, moments,
and Fernique-type bounds are derived.

## Key type identifications

- `FieldConfiguration` is `WeakDual ℝ TestFunction`
- `MeasurableSpace FieldConfiguration` uses `comap (fun ω f => ω f) pi`
- The real inner product on `Lp ℂ 2 volume` comes from `InnerProductSpace.rclikeToReal`
- `@inner ℝ _ _ (T f) (T g) = freeCovarianceFormR m f g` (bridge lemma, by polarization)

## Sorries in this file

The `sorry` markers in `gfMeasure` and `gfMeasure_charFun` are for the
MeasurableSpace transport: bochner's Minlos theorem constructs a measure on the
⨆-comap σ-algebra, while this project uses comap-pi. These are propositionally
equal (`measurableSpace_comap_eq_bochner`), but the dependent type transport is
technically complex.

The `sorry` markers in `gfMeasure_centered`, `gfMeasure_second_moment`, and
`gfMeasure_pairing_memLp` are for deriving properties from the Gaussian
pushforward axiom via Mathlib's `gaussianReal` API.
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
- `gff_pairing_is_gaussian_axiom`: pushforward of GFF measure by test function pairing is Gaussian

See `texts/axioms.txt` for justification. -/

/-- Schwartz space 𝓢(ℝ⁴,ℝ) is Hilbert-nuclear (Gel'fand-Vilenkin, Trèves).
    This is the nuclearity condition required by bochner's Minlos theorem. -/
axiom schwartz_isHilbertNuclear : IsHilbertNuclear TestFunction

attribute [instance] schwartz_isHilbertNuclear

/-- Schwartz space is separable (Fréchet space with countable seminorms).
    Standard result (Reed-Simon, Vol. 1); synthesis gap in Mathlib. -/
instance schwartz_separableSpace : SeparableSpace TestFunction := by
  sorry

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

/-- The GFF measure, constructed via the Minlos theorem applied to the Gaussian
    characteristic functional with covariance `freeCovarianceFormR m`.

    **sorry**: MeasurableSpace transport from bochner's ⨆-comap to our comap-pi.
    These are propositionally equal (`measurableSpace_comap_eq_bochner`) but the
    dependent type transport is technically complex. -/
def gfMeasure (m : ℝ) [Fact (0 < m)] : ProbabilityMeasure FieldConfiguration := by
  letI := instInnerProductSpaceReal m
  letI := instSeparableSpaceTargetHilbertSpace m
  -- Minlos theorem provides existence on bochner's σ-algebra (⨆-comap).
  -- Our σ-algebra (comap-pi) is propositionally equal (measurableSpace_comap_eq_bochner).
  -- The transport is mathematically trivial but the dependent type cast is complex.
  exact sorry

/-- The characteristic functional of gfMeasure: E[exp(i⟨ω,f⟩)] = exp(-½ C(f,f)).

    Follows from `minlos_gaussian_construction` + σ-algebra transport. -/
theorem gfMeasure_charFun (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
    ∫ ω, Complex.exp (Complex.I * ↑(distributionPairing ω f))
      ∂(gfMeasure m).toMeasure =
    Complex.exp (-(1/2 : ℂ) * ↑(freeCovarianceFormR m f f)) := by
  -- Follows from Minlos construction + σ-algebra transport
  sorry

/-- **Axiom**: Pushforward by ω ↦ ω(φ) is N(0, C(φ,φ)).

    This follows from: the characteristic functional of the pushforward measure
    μ.map ⟨·,φ⟩ equals exp(-½ σ² t²) (from Minlos), which is the characteristic
    function of gaussianReal 0 σ². By Lévy's uniqueness theorem, the measures
    are equal. Currently an axiom because Lévy inversion is not yet in Mathlib. -/
axiom gff_pairing_is_gaussian_axiom (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
    (gfMeasure m).toMeasure.map (distributionPairingCLM φ)
      = gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal

/-- Pushforward by ω ↦ ω(f) is N(0, C(f,f)). -/
theorem gfMeasure_pairing_is_gaussian (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
    (gfMeasure m).toMeasure.map (distributionPairingCLM φ)
      = gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal :=
  gff_pairing_is_gaussian_axiom m φ

/-! ## Derived properties

All of the following are derived from `gff_pairing_is_gaussian_axiom` using
Mathlib's `gaussianReal` API. -/

/-- The measure is centered: E[ω(f)] = 0.
    Derived from: the mean of gaussianReal 0 σ² is 0. -/
theorem gfMeasure_centered (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
    ∫ ω, distributionPairingCLM f ω ∂(gfMeasure m).toMeasure = 0 := by
  -- ∫ ω, ω(f) dμ = ∫ x, x d(μ.map(eval f)) = ∫ x, x d(gaussianReal 0 σ²) = 0
  simp only [distributionPairingCLM_apply, distributionPairing]
  sorry

/-- Second moment: E[ω(f)²] = C(f,f).
    Derived from: the variance of gaussianReal 0 σ² is σ². -/
theorem gfMeasure_second_moment (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
    ∫ ω, (distributionPairingCLM φ ω)^2 ∂(gfMeasure m).toMeasure =
    freeCovarianceFormR m φ φ := by
  -- ∫ ω, ω(φ)² dμ = ∫ x, x² d(gaussianReal 0 σ²) = 0² + σ² = C(φ,φ)
  simp only [distributionPairingCLM_apply, distributionPairing]
  sorry

/-- Fernique-type: pairings are in Lᵖ for all finite p.
    Derived from: gaussianReal has all finite moments. -/
theorem gfMeasure_pairing_memLp (m : ℝ) [Fact (0 < m)]
    (φ : TestFunction) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (distributionPairingCLM φ) p (gfMeasure m).toMeasure := by
  -- The pushforward is gaussianReal, which is IsGaussian, hence has all finite moments.
  sorry

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
