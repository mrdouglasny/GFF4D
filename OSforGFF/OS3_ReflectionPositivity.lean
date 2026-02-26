/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import OSforGFF.OS3_CovarianceRP  -- Direct proof (BlueprintAlt namespace)
import OSforGFF.PositiveTimeTestFunction_real
import OSforGFF.Parseval  -- For freeCovarianceℂ_bilinear definition (sorries not in proof chain)
import OSforGFF.Covariance  -- For real_integral_eq_complex_re, compTimeReflection_toComplex_star_eq

/-!
# Proof of Reflection Positivity for the Bessel Covariance

This file contains the proof of reflection positivity (OS3) for the free scalar field
using the unregulated Bessel covariance kernel.

## Main Result

* `freeCovariance_reflection_positive_bilinear` : For any test function f supported on
  positive time, the reflection positivity inner product is non-negative:
  ⟨Θf, f⟩_C = ∫∫ f*(Θx) C(x,y) f(y) dx dy ≥ 0

## Proof Strategy (Direct Momentum Representation)

The proof uses the direct momentum representation from OS3_CovarianceRP.lean:

1. Rewrite rpInnerProduct using `momentum_representation_unregulated`:
   ⟨Θf, f⟩_C = (1/(2π)^d) ∫_{k_sp} (π/ω) |F_ω(-k_sp)|² dk_sp
2. Observe that the integrand and prefactor are non-negative
3. Conclude Re⟨Θf, f⟩_C ≥ 0

No spatial regulator, no limit argument, no DCT. Only standard Lean axioms
(propext, Classical.choice, Quot.sound).
-/

namespace QFT

open MeasureTheory Complex Real Filter
open scoped ENNReal NNReal Topology ComplexConjugate Real InnerProductSpace BigOperators

/-! ## Reflection Positivity Inner Product

The reflection positivity inner product is defined using the distributional bilinear form
composed with the star operation. This is the mathematically correct formulation that
avoids non-convergent pointwise integrals. -/

/-- The reflection positivity inner product using the distributional bilinear form:
    ⟨Θf, f⟩_C = freeCovarianceℂ_bilinear m (star f) f
             = ∫∫ conj(f(Θx)) * C(x,y) * f(y) dx dy

    The star operation on TestFunctionℂ is defined as:
    (star f)(x) = conj(f(Θx))  (time reflection composed with conjugation)

    This is the distributional formulation that is mathematically well-defined
    for Schwartz test functions. -/
noncomputable def rpInnerProduct (m : ℝ) (f : TestFunctionℂ) : ℂ :=
  freeCovarianceℂ_bilinear m (star f) f

/-! ## Bridge to Direct Proof

The main reflection positivity result is proved directly in OS3_CovarianceRP.lean
(BlueprintAlt namespace). We connect the QFT namespace definitions to BlueprintAlt
via a bridge lemma (rfl, since both use the same Bessel kernel). -/

/-- **Bridge Lemma**: The QFT namespace rpInnerProduct equals the BlueprintAlt rpInnerProduct.

    Both are now defined using the same Bessel kernel C(x,y) = (m/(4π²r)) K₁(mr),
    so this equality holds by definition (rfl).

    Previously this was an axiom, but after refactoring BlueprintAlt to use the
    Bessel kernel (Option A), this became a trivial equality. -/
lemma rpInnerProduct_eq_blueprintAlt (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    rpInnerProduct m f = BlueprintAlt.rpInnerProduct m f := by
  -- Both sides expand to the same integral using freeCovariance (Bessel)
  unfold rpInnerProduct BlueprintAlt.rpInnerProduct
  unfold freeCovarianceℂ_bilinear BlueprintAlt.freeCovarianceℂ_bilinear
  rfl

/-- **Main Reflection Positivity Theorem** (Bilinear Form)

    For any complex test function f supported on positive time (x₀ ≥ 0),
    the reflection positivity inner product is non-negative:

    Re⟨Θf, f⟩_C ≥ 0

    where C is the unregulated Bessel covariance kernel.

    **Proof:** Bridge to BlueprintAlt, then apply the direct proof
    via momentum representation and non-negativity of the integrand. -/
theorem freeCovariance_reflection_positive_bilinear (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ)
    (hf_supp : ∀ x : SpaceTime, x 0 ≤ 0 → f x = 0) :
  0 ≤ (rpInnerProduct m f).re := by
  rw [rpInnerProduct_eq_blueprintAlt]
  exact BlueprintAlt.freeCovariance_reflection_positive_direct m f hf_supp

/-! ## Connection to Real Test Functions

The result extends to real test functions via embedding. -/

/-- For real test functions, `star (toComplex f) = compTimeReflection (toComplex f)`.
    This is because conjugation is identity for real-valued functions. -/
lemma star_toComplex_eq_compTimeReflection (f : TestFunction) :
    star (toComplex f) = compTimeReflection (toComplex f) := by
  ext x
  -- star f is defined as starTestFunction f
  -- starTestFunction f x = starRingEnd ℂ ((compTimeReflection f) x)
  simp only [star, starTestFunction]
  -- Now goal: starRingEnd ℂ ((compTimeReflection (toComplex f)) x) = (compTimeReflection (toComplex f)) x
  exact compTimeReflection_toComplex_star_eq f x

/-- The rpInnerProduct of a real test function equals the complex bilinear form
    with compTimeReflection. -/
lemma rpInnerProduct_toComplex_eq (m : ℝ) (f : TestFunction) :
    rpInnerProduct m (toComplex f) =
      freeCovarianceℂ_bilinear m (compTimeReflection (toComplex f)) (toComplex f) := by
  unfold rpInnerProduct
  rw [star_toComplex_eq_compTimeReflection]

/-- For real test functions, the reflection positivity inner product is non-negative. -/
theorem freeCovariance_reflection_positive_bilinear_real (m : ℝ) [Fact (0 < m)] (f : TestFunction)
    (hf_supp : ∀ x : SpaceTime, x 0 ≤ 0 → f x = 0) :
  0 ≤ ∫ x, ∫ y, (QFT.compTimeReflectionReal f) x * freeCovariance m x y * f y := by
  -- Use the complex theorem for toComplex f
  have h_complex := freeCovariance_reflection_positive_bilinear m (toComplex f) (by
    intro x hx
    simp only [toComplex_apply]
    rw [hf_supp x hx]
    simp)
  -- Connect the real integral to the complex one via real_integral_eq_complex_re
  rw [real_integral_eq_complex_re m f]
  -- Show that the complex integral equals rpInnerProduct
  have h_eq : (∫ x, ∫ y, (QFT.compTimeReflection (toComplex f)) x * (freeCovariance m x y : ℂ)
        * (toComplex f) y ∂volume ∂volume)
      = rpInnerProduct m (toComplex f) := by
    rw [rpInnerProduct_toComplex_eq]
    rfl
  rw [h_eq]
  exact h_complex

/-- Alias for `freeCovariance_reflection_positive_bilinear_real` to match expected name. -/
theorem freeCovariance_reflection_positive_real (m : ℝ) [Fact (0 < m)] (f : TestFunction)
    (hf_supp : ∀ x : SpaceTime, x 0 ≤ 0 → f x = 0) :
  0 ≤ ∫ x, ∫ y, (QFT.compTimeReflectionReal f) x * freeCovariance m x y * f y :=
  freeCovariance_reflection_positive_bilinear_real m f hf_supp

end QFT
