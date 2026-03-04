/-
Copyright (c) 2025-2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

import OSforGFF.Basic
import OSforGFF.Schwinger
import OSforGFF.GaussianFieldBridge
import OSforGFF.Covariance
import OSforGFF.CovarianceR
import OSforGFF.ComplexTestFunction

/-!
## Gaussian Free Field: Interface Layer

This file provides the GFF probability measure on field configurations and its
core properties. The measure is constructed via the Minlos theorem (from the
bochner library), applied to the Gaussian characteristic functional with
covariance operator `embeddingMapCLM m : TestFunction →L[ℝ] L²(ℝ⁴,ℂ)`.

### Core Framework:

**Covariance Structure:**
- `CovarianceFunction`: Symmetric, bilinear, positive semidefinite covariance with boundedness
- `SchwingerFunctionℂ₂`: Complex 2-point correlation function ⟨φ(f)φ(g)⟩

**Gaussian Characterization:**
- `isCenteredGJ`: Zero mean condition for Gaussian measures
- `isGaussianGJ`: Generating functional Z[J] = exp(-½⟨J, CJ⟩) for centered Gaussian

### Main Results:

- `gaussianFreeField_free`: The GFF ProbabilityMeasure (via Minlos construction)
- `gff_real_characteristic`: Characteristic functional E[exp(i⟨ω,f⟩)] = exp(-½C(f,f))
- `gff_pairing_is_gaussian`: Pushforward by test function is 1D Gaussian
- `gaussianFreeField_pairing_memLp`: Fernique-type Lᵖ integrability
- `gaussianFreeField_free_centered`: Zero mean
- `gff_second_moment_eq_covariance`: E[⟨ω,φ⟩²] = C(φ,φ)
-/

open MeasureTheory Complex QFT ProbabilityTheory
open TopologicalSpace SchwartzMap

noncomputable section

/-! ## Gaussian Measures on Field Configurations
-/

/-- A covariance function on test functions that determines the Gaussian measure -/
structure CovarianceFunction where
  covar : TestFunctionℂ → TestFunctionℂ → ℂ
  symmetric : ∀ f g, covar f g = (starRingEnd ℂ) (covar g f)
  bilinear_left : ∀ c f₁ f₂ g, covar (c • f₁ + f₂) g = c * covar f₁ g + covar f₂ g
  bilinear_right : ∀ f c g₁ g₂, covar f (c • g₁ + g₂) = (starRingEnd ℂ) c * covar f g₁ + covar f g₂
  positive_semidefinite : ∀ f, 0 ≤ (covar f f).re
  bounded : ∃ M > 0, ∀ f, ‖covar f f‖ ≤ M * (∫ x, ‖f x‖ ∂volume) * (∫ x, ‖f x‖^2 ∂volume)^(1/2)

/-- A measure is centered (has zero mean) -/
def isCenteredGJ (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (f : TestFunction), GJMean dμ_config f = 0

/-- A measure is Gaussian if its generating functional has the Gaussian form.
    For a centered Gaussian measure, Z[J] = exp(-½⟨J, CJ⟩) where C is the covariance. -/
def isGaussianGJ (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  isCenteredGJ dμ_config ∧
  ∀ (J : TestFunctionℂ),
    GJGeneratingFunctionalℂ dμ_config J =
    Complex.exp (-(1/2 : ℂ) * SchwingerFunctionℂ₂ dμ_config J J)

/-! ## GFF Measure from Minlos Construction

The GFF is constructed via the Minlos theorem applied to the Gaussian
characteristic functional exp(-½ C(f,f)). The Schwartz space `TestFunction`
is Hilbert-nuclear (axiom `schwartz_isHilbertNuclear`) and the covariance operator
`embeddingMapCLM m` embeds into the target Hilbert space `L²(ℝ⁴,ℂ)`.

The bridge theorems in `GaussianFieldBridge` connect the construction's
inner-product form to aqft2's `freeCovarianceFormR`. -/

/-- The Gaussian Free Field with mass m > 0.

    Constructed via the Minlos theorem applied to the Gaussian characteristic
    functional with covariance `freeCovarianceFormR m`. -/
noncomputable def gaussianFreeField_free (m : ℝ) [Fact (0 < m)] : ProbabilityMeasure FieldConfiguration :=
  GaussianFieldBridge.gfMeasure m

/-- Shorthand for the free GFF probability measure used throughout. -/
@[simp] abbrev μ_GFF (m : ℝ) [Fact (0 < m)] := gaussianFreeField_free m

-- Measurability of the pairing CLM from the cylindrical σ-algebra.
@[fun_prop]
private lemma distributionPairingCLM_measurable (φ : TestFunction) :
    Measurable (distributionPairingCLM φ) :=
  fieldConfiguration_eval_measurable φ

/-- Real characteristic functional of the free GFF: for real test functions f, the generating
    functional equals the Gaussian form with the real covariance. -/
theorem gff_real_characteristic (m : ℝ) [Fact (0 < m)] :
  ∀ f : TestFunction,
    GJGeneratingFunctional (gaussianFreeField_free m) f =
      Complex.exp (-(1/2 : ℂ) * (freeCovarianceFormR m f f : ℝ)) :=
  GaussianFieldBridge.gfMeasure_real_characteristic m

/-- The pushforward of the GFF measure by pairing with a test function is a 1D Gaussian. -/
theorem gff_pairing_is_gaussian
  (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
  (gaussianFreeField_free m).toMeasure.map (distributionPairingCLM φ)
    = gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal :=
  GaussianFieldBridge.gfMeasure_pairing_is_gaussian m φ

/-- **Fernique's Theorem for GFF**: Every distribution pairing has finite moments of all orders.
    Derived from the Gaussian pushforward and Mathlib's gaussianReal theory. -/
theorem gaussianFreeField_pairing_memLp
  (m : ℝ) [Fact (0 < m)] (φ : TestFunction) (p : ENNReal) (hp : p ≠ ⊤) :
  MemLp (distributionPairingCLM φ) p (gaussianFreeField_free m).toMeasure :=
  GaussianFieldBridge.gfMeasure_pairing_memLp m φ p hp

/-- The GFF pairing has an integrable square (is in L²). -/
lemma gff_pairing_square_integrable
  (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
  Integrable (fun ω => (distributionPairingCLM φ ω)^2) (gaussianFreeField_free m).toMeasure :=
  (gaussianFreeField_pairing_memLp m φ 2 (by simp)).integrable_sq

/-- The second moment of the GFF pairing equals the covariance form. -/
lemma gff_second_moment_eq_covariance
  (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
  ∫ ω, (distributionPairingCLM φ ω)^2 ∂(gaussianFreeField_free m).toMeasure =
    freeCovarianceFormR m φ φ :=
  GaussianFieldBridge.gfMeasure_second_moment m φ

/-- The GFF has zero mean: the measure is centered. -/
theorem gaussianFreeField_free_centered (m : ℝ) [Fact (0 < m)] :
    isCenteredGJ (gaussianFreeField_free m) :=
  GaussianFieldBridge.gfMeasure_isCenteredGJ m

/-- **Fernique's Theorem for GFF (exponential form)**: For every real test function `φ`,
there exists `α > 0` such that `exp(α * ⟨ω, φ⟩²)` is integrable under the free GFF measure. -/
theorem gaussianFreeField_pairing_expSq_integrable
  (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
  ∃ α : ℝ, 0 < α ∧
    Integrable
      (fun ω =>
        Real.exp (α * (distributionPairingCLM φ ω)^2))
      (gaussianFreeField_free m).toMeasure :=
  GaussianFieldBridge.gfMeasure_pairing_expSq_integrable m φ

/-- For real test functions, the square of the Gaussian pairing is integrable. -/
lemma gaussian_pairing_square_integrable_real
    (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
  Integrable (fun ω => (distributionPairing ω φ) ^ 2)
    (gaussianFreeField_free m).toMeasure :=
  GaussianFieldBridge.gfMeasure_pairing_square_integrable m φ

end
