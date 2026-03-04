/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.RCLike.Extend
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Algebra.Module.WeakDual

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.GroupAction.Basic

-- Import our functional analysis utilities
import OSforGFF.FunctionalAnalysis

/-!
## AQFT Basic Framework

This file provides the foundational definitions for the Glimm-Jaffe approach to Algebraic Quantum Field Theory,
implementing field configurations as tempered distributions and the associated generating functionals.

### Key Definitions & Framework:

**Spacetime Structure:**
- `STDimension`: Spacetime dimension (4D)
- `SpaceTime`: Euclidean 4-space using EuclideanSpace
- `getTimeComponent`: Extracts time coordinate (t = x₄)
- `μ`: Standard Lebesgue measure on spacetime

**Test Function Spaces:**
- `TestFunction`: Real-valued Schwartz functions on spacetime
- `TestFunction𝕜`: Generic Schwartz functions over field 𝕜
- `TestFunctionℂ`: Complex-valued Schwartz functions
- `schwartzMul`: Multiplication operation on complex test functions
- `schwartz_comp_clm`: Composition with continuous linear maps (extends Schwartz regularity)

**Field Configurations as Distributions:**
- `FieldConfiguration`: Tempered distributions (WeakDual of Schwartz space)
- Proper weak-* topology for measure theory
- Measurable space structure via Borel σ-algebra

**Distribution Pairings:**
- `distributionPairing`: Real pairing ⟨ω, f⟩ between distributions and test functions
- `complex_testfunction_decompose`: Efficient real/imaginary decomposition for complex test functions
- `distributionPairingℂ_real`: Complex pairing ⟨ω, f⟩ = ⟨ω, Re f⟩ + i⟨ω, Im f⟩

**Glimm-Jaffe Generating Functionals:**
- `GJGeneratingFunctional`: Real generating functional Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω)
- `GJGeneratingFunctionalℂ`: Complex generating functional for analyticity
- `GJMean`: Mean field ⟨φ⟩ = ∫ ⟨ω, φ⟩ dμ(ω)

**Mathematical Foundation:**
This implements the distribution-based approach where:
1. Field configurations ω are tempered distributions, not L² functions
2. Generating functionals are defined via complex exponential integrals
3. All correlation functions emerge from functional derivatives
4. Complex analyticity (OS0) is naturally incorporated
5. Measure theory is well-defined on the weak-* topology

**Connection to Other Modules:**
- Schwinger functions and correlations → `OSforGFF.Schwinger`
- Osterwalder-Schrader axioms → `OSforGFF.OS_Axioms`
- Gaussian measures and Minlos theorem → `OSforGFF.Minlos`, `OSforGFF.GFFMconstruct`
- Euclidean group actions → `OSforGFF.Euclidean`

This provides the mathematical foundation for constructive quantum field theory
using the Osterwalder-Schrader framework.

Design notes (possible future changes):

- Spacetime model: We currently use Euclidean ℝ^d (here d = STDimension) with Lebesgue measure.
  In some applications it may be preferable to work on a compact Riemannian manifold (M, g).
  This would affect the definitions of `SpaceTime`, the reference measure μ, Fourier-analytic
  tools, and Euclidean invariance statements.

- Distribution class: We currently model field configurations as tempered distributions on
  Schwartz test functions. In the stochastic quantization literature, smaller configuration
  spaces are often used, e.g. negative Hölder/Besov regularity classes C^{-α}. Migrating to
  such classes would change the test-function space, the topology on the dual, and the way
  Minlos/characteristic functionals are formulated.
-/

-- Euclidean geometry definitions are now in OSforGFF.Euclidean
-- but we define basic spacetime here to avoid circular imports
/-- Spacetime dimension. Currently set to 4 (Euclidean ℝ⁴).
    Changing this value requires corresponding changes throughout the project;
    see `docs/dimension_dependence.md` for a detailed inventory. -/
abbrev STDimension := 4
abbrev SpaceTime := EuclideanSpace ℝ (Fin STDimension)

noncomputable instance : InnerProductSpace ℝ SpaceTime := by infer_instance

abbrev getTimeComponent (x : SpaceTime) : ℝ :=
 x ⟨0, by simp +arith⟩

open MeasureTheory NNReal ENNReal Complex
open TopologicalSpace Measure

-- Also open FunLike for SchwartzMap function application
open DFunLike (coe)

noncomputable section

variable {𝕜 : Type} [RCLike 𝕜]

abbrev μ : Measure SpaceTime := volume    -- Lebesgue, just named “μ”

/- Distributions and test functions -/

abbrev TestFunction : Type := SchwartzMap SpaceTime ℝ
abbrev TestFunction𝕜 : Type := SchwartzMap SpaceTime 𝕜
abbrev TestFunctionℂ := TestFunction𝕜 (𝕜 := ℂ)

example : AddCommGroup TestFunctionℂ := by infer_instance
example : Module ℂ TestFunctionℂ := by infer_instance

/- Space-time and test function setup -/

variable (x : SpaceTime)

/- Probability distribution over field configurations (distributions) -/
def pointwiseMulCLM : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ

/-- Multiplication lifted to the Schwartz space. -/
def schwartzMul (g : TestFunctionℂ) : TestFunctionℂ →L[ℂ] TestFunctionℂ :=
  (SchwartzMap.bilinLeftCLM pointwiseMulCLM (SchwartzMap.hasTemperateGrowth_general g))



/-! ## Glimm-Jaffe Distribution Framework

The proper mathematical foundation for quantum field theory uses
tempered distributions as field configurations, following Glimm and Jaffe.
This section adds the distribution-theoretic definitions alongside
the existing L2 framework for comparison and gradual transition.
-/

/-- Field configurations as tempered distributions (dual to Schwartz space).
    This follows the Glimm-Jaffe approach where the field measure is supported
    on the space of distributions, not L2 functions.

    Using WeakDual gives the correct weak-* topology on the dual space. -/
abbrev FieldConfiguration := WeakDual ℝ (SchwartzMap SpaceTime ℝ)

-- Measurable space instance: the **cylindrical σ-algebra** generated by evaluation maps.
-- This is the standard choice for measures on duals of nuclear spaces (Gel'fand-Vilenkin,
-- Bogachev §7.14). For separable E, it equals the Borel σ-algebra of the weak-* topology,
-- but the cylindrical definition avoids needing to prove that equivalence.
--
-- Note: This instance is definitionally equal to GaussianField.instMeasurableSpaceConfiguration
-- (both use comap-pi). Bochner's Minlos.NuclearSpace uses a propositionally equal but
-- definitionally different ⨆-based definition; the bridge is in OSforGFF/Minlos.lean.
instance instMeasurableSpaceFieldConfiguration : MeasurableSpace FieldConfiguration :=
  MeasurableSpace.comap (fun ω : FieldConfiguration => fun φ : TestFunction => ω φ)
    MeasurableSpace.pi

/-- Evaluation at a test function is measurable from the cylindrical σ-algebra. -/
@[fun_prop]
theorem fieldConfiguration_eval_measurable (φ : TestFunction) :
    Measurable (fun ω : FieldConfiguration => ω φ) :=
  (measurable_pi_apply φ).comp (comap_measurable _)

/-- A function into FieldConfiguration is measurable iff each evaluation is measurable.
    This is immediate from the cylindrical σ-algebra definition. -/
theorem fieldConfiguration_measurable_of_eval_measurable
    {α : Type*} [MeasurableSpace α] {f : α → FieldConfiguration}
    (h : ∀ (φ : TestFunction), Measurable (fun x => f x φ)) :
    Measurable f := by
  show @Measurable _ _ _ (MeasurableSpace.comap _ MeasurableSpace.pi) f
  rw [measurable_comap_iff (g := fun ω : FieldConfiguration => fun φ : TestFunction => ω φ)]
  exact measurable_pi_iff.mpr h

/-- The fundamental pairing between a field configuration (distribution) and a test function.
    This is ⟨ω, f⟩ in the Glimm-Jaffe notation.

    Note: FieldConfiguration = WeakDual ℝ (SchwartzMap SpaceTime ℝ) has the correct
    weak-* topology, making evaluation maps x ↦ ω(x) continuous for each test function x. -/
def distributionPairing (ω : FieldConfiguration) (f : TestFunction) : ℝ := ω f

@[simp] lemma distributionPairing_add (ω₁ ω₂ : FieldConfiguration) (a : TestFunction) :
    distributionPairing (ω₁ + ω₂) a = distributionPairing ω₁ a + distributionPairing ω₂ a := rfl

@[simp] lemma distributionPairing_smul (s : ℝ) (ω : FieldConfiguration) (a : TestFunction) :
    distributionPairing (s • ω) a = s * distributionPairing ω a :=
  -- This follows from the definition of scalar multiplication in WeakDual
  rfl

@[simp] lemma pairing_smul_real (ω : FieldConfiguration) (s : ℝ) (a : TestFunction) :
  ω (s • a) = s * (ω a) :=
  -- This follows from the linearity of the dual pairing
  map_smul ω s a

@[simp] def distributionPairingCLM (a : TestFunction) : FieldConfiguration →L[ℝ] ℝ where
  toFun ω := distributionPairing ω a
  map_add' ω₁ ω₂ := by
    -- WeakDual addition is pointwise: (ω₁ + ω₂) a = ω₁ a + ω₂ a
    rfl
  map_smul' s ω := by
    -- WeakDual scalar multiplication is pointwise: (s • ω) a = s * (ω a)
    rfl
  cont := by
    -- The evaluation map is continuous by definition of WeakDual topology
    exact WeakDual.eval_continuous a

@[simp] lemma distributionPairingCLM_apply (a : TestFunction) (ω : FieldConfiguration) :
    distributionPairingCLM a ω = distributionPairing ω a := rfl

variable [SigmaFinite μ]

/-! ## Glimm-Jaffe Generating Functional

The generating functional in the distribution framework:
Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω)
where the integral is over field configurations ω (distributions).
-/

/-- The Glimm-Jaffe generating functional: Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω)
    This is the fundamental object in constructive QFT. -/
def GJGeneratingFunctional (dμ_config : ProbabilityMeasure FieldConfiguration)
  (J : TestFunction) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairing ω J : ℂ)) ∂dμ_config.toMeasure

/-- Helper function to create a Schwartz map from a complex test function by applying a continuous linear map.
    This factors out the common pattern for extracting real/imaginary parts. -/
def schwartz_comp_clm (f : TestFunctionℂ) (L : ℂ →L[ℝ] ℝ) : TestFunction :=
  SchwartzMap.mk (fun x => L (f x)) (by
    -- L is a continuous linear map, hence smooth
    exact ContDiff.comp L.contDiff f.smooth'
  ) (by
    -- Polynomial growth: since |L(z)| ≤ ||L|| * |z|, derivatives are controlled
    intro k n
    obtain ⟨C, hC⟩ := f.decay' k n
    use C * ‖L‖
    intro x
    -- The function (fun x => L (f x)) equals (L ∘ f.toFun)
    have h_eq : (fun y => L (f y)) = L ∘ f.toFun := rfl
    -- Key: iteratedFDeriv of L ∘ f equals L.compContinuousMultilinearMap (iteratedFDeriv f)
    have h_deriv : iteratedFDeriv ℝ n (L ∘ f.toFun) x =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ n f.toFun x) :=
      ContinuousLinearMap.iteratedFDeriv_comp_left L f.smooth'.contDiffAt (WithTop.coe_le_coe.mpr le_top)
    rw [h_eq, h_deriv]
    -- Use the norm bound: ‖L.compContinuousMultilinearMap m‖ ≤ ‖L‖ * ‖m‖
    calc ‖x‖ ^ k * ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ n f.toFun x)‖
        ≤ ‖x‖ ^ k * (‖L‖ * ‖iteratedFDeriv ℝ n f.toFun x‖) := by
          apply mul_le_mul_of_nonneg_left
          exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le L _
          exact pow_nonneg (norm_nonneg _) _
      _ = ‖L‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun x‖) := by ring
      _ ≤ ‖L‖ * C := by
          apply mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
      _ = C * ‖L‖ := by ring
  )

omit [SigmaFinite μ]

/-- Evaluate `schwartz_comp_clm` pointwise. -/
@[simp] lemma schwartz_comp_clm_apply (f : TestFunctionℂ) (L : ℂ →L[ℝ] ℝ) (x : SpaceTime) :
  (schwartz_comp_clm f L) x = L (f x) := rfl

/-- Decompose a complex test function into its real and imaginary parts as real test functions.
    This is more efficient than separate extraction functions. -/
def complex_testfunction_decompose (f : TestFunctionℂ) : TestFunction × TestFunction :=
  (schwartz_comp_clm f Complex.reCLM, schwartz_comp_clm f Complex.imCLM)

/-- First component of the decomposition evaluates to the real part pointwise. -/
@[simp] lemma complex_testfunction_decompose_fst_apply
  (f : TestFunctionℂ) (x : SpaceTime) :
  (complex_testfunction_decompose f).1 x = (f x).re := by
  simp [complex_testfunction_decompose]

/-- Second component of the decomposition evaluates to the imaginary part pointwise. -/
@[simp] lemma complex_testfunction_decompose_snd_apply
  (f : TestFunctionℂ) (x : SpaceTime) :
  (complex_testfunction_decompose f).2 x = (f x).im := by
  simp [complex_testfunction_decompose]

/-- Coerced-to-ℂ version (useful for complex-side algebra). -/
@[simp] lemma complex_testfunction_decompose_fst_apply_coe
  (f : TestFunctionℂ) (x : SpaceTime) :
  ((complex_testfunction_decompose f).1 x : ℂ) = ((f x).re : ℂ) := by
  simp [complex_testfunction_decompose]

/-- Coerced-to-ℂ version (useful for complex-side algebra). -/
@[simp] lemma complex_testfunction_decompose_snd_apply_coe
  (f : TestFunctionℂ) (x : SpaceTime) :
  ((complex_testfunction_decompose f).2 x : ℂ) = ((f x).im : ℂ) := by
  simp [complex_testfunction_decompose]

/-- Recomposition at a point via the decomposition. -/
lemma complex_testfunction_decompose_recompose
  (f : TestFunctionℂ) (x : SpaceTime) :
  f x = ((complex_testfunction_decompose f).1 x : ℂ)
          + Complex.I * ((complex_testfunction_decompose f).2 x : ℂ) := by
  -- Reduce to the standard identity z = re z + i im z
  have h1 : f x = (Complex.re (f x) : ℂ) + (Complex.im (f x) : ℂ) * Complex.I :=
    (Complex.re_add_im (f x)).symm
  have h2 : f x = (Complex.re (f x) : ℂ) + Complex.I * (Complex.im (f x) : ℂ) := by
    simpa [mul_comm] using h1
  -- Rewrite re/im via the decomposition
  simpa using h2

/-- Complex version of the pairing: real field configuration with complex test function
    We extend the pairing by treating the complex test function as f(x) = f_re(x) + i*f_im(x)
    and defining ⟨ω, f⟩ = ⟨ω, f_re⟩ + i*⟨ω, f_im⟩ -/
def distributionPairingℂ_real (ω : FieldConfiguration) (f : TestFunctionℂ) : ℂ :=
  -- Extract real and imaginary parts using our efficient decomposition
  let ⟨f_re, f_im⟩ := complex_testfunction_decompose f
  -- Pair with the real field configuration and combine
  (ω f_re : ℂ) + Complex.I * (ω f_im : ℂ)

/-- Complex version of the generating functional -/
def GJGeneratingFunctionalℂ (dμ_config : ProbabilityMeasure FieldConfiguration)
  (J : TestFunctionℂ) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairingℂ_real ω J)) ∂dμ_config.toMeasure

/-- The mean field in the Glimm-Jaffe framework -/
def GJMean (dμ_config : ProbabilityMeasure FieldConfiguration)
  (φ : TestFunction) : ℝ :=
  ∫ ω, distributionPairing ω φ ∂dμ_config.toMeasure

-- Test the new definitions work correctly
variable (dμ_config : ProbabilityMeasure FieldConfiguration)

#check GJGeneratingFunctional dμ_config
#check GJGeneratingFunctionalℂ dμ_config

end
