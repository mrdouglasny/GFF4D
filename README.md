# Osterwalder-Schrader Axioms for the Gaussian Free Field

We construct the massive Gaussian Free Field (GFF) as a probability measure on
the space of tempered distributions S'(ℝ⁴), and prove that it satisfies all five
Osterwalder-Schrader axioms for a Euclidean quantum field theory. The construction
and proofs are formalized in Lean 4 / Mathlib, following the conventions in
Glimm and Jaffe, *Quantum Physics* (1987).

## Master Theorem

```lean
theorem gaussianFreeField_satisfies_all_OS_axioms (m : ℝ) [Fact (0 < m)] :
  OS0_Analyticity (μ_GFF m) ∧
  OS1_Regularity (μ_GFF m) ∧
  OS2_EuclideanInvariance (μ_GFF m) ∧
  OS3_ReflectionPositivity (μ_GFF m) ∧
  OS4_Clustering (μ_GFF m) ∧
  OS4_Ergodicity (μ_GFF m)
```

**Status:** The master theorem chain has **0 `sorry`** statements and **2 custom axioms**
(`schwartz_isHilbertNuclear`, `gff_pairing_is_gaussian_axiom`).
~31,000 lines of Lean across 50 files in `OSforGFF/`.

## Dependencies

### BochnerMinlos

The [bochner](../bochner) library (local path dependency) provides fully proven
versions of the Bochner and Minlos theorems for nuclear spaces, with 0 sorries
and 0 custom axioms. This project imports:
- **`minlos_theorem`** — existence of a probability measure on the dual of a
  nuclear space with a given continuous positive-definite characteristic functional
- **`minlos_uniqueness`** — uniqueness of such a measure
- **`IsPositiveDefinite`** — hermitian + nonneg-definite structure for characteristic functionals
- **`IsHilbertNuclear`** — Gel'fand-Vilenkin nuclearity (Hilbertian seminorms + HS embeddings)

These replace the former `minlos_theorem` and `minlos_uniqueness` axioms that were
in `OSforGFF/Minlos.lean`. Bridge lemmas in that file handle the type class
differences between GFF4D (`NuclearSpace`, comap-pi MeasurableSpace) and bochner
(`IsHilbertNuclear`, ⨆-comap MeasurableSpace).

## Project Structure

The library files are organized into layers, with imports flowing from
earlier to later sections.

---

### 1. General Mathematics

Results that do not depend on any project-specific definitions. Pure extensions
of Mathlib.

#### Functional Analysis

| File | Contents |
|------|----------|
| [FunctionalAnalysis](OSforGFF/FunctionalAnalysis.lean) | L² Fourier transform infrastructure, Plancherel identity |
| [FrobeniusPositivity](OSforGFF/FrobeniusPositivity.lean) | Frobenius inner product, positive semidefinite matrix theory |
| [SchurProduct](OSforGFF/SchurProduct.lean) | Schur product theorem (Hadamard product preserves PSD) |
| [HadamardExp](OSforGFF/HadamardExp.lean) | Hadamard exponential of PD matrices is PD |
| [PositiveDefinite](OSforGFF/PositiveDefinite.lean) | Positive definite functions and kernels |
| [GaussianRBF](OSforGFF/GaussianRBF.lean) | Gaussian RBF kernel exp(-‖x-y‖²) is positive definite |

#### Schwartz Functions and Decay Estimates

| File | Contents |
|------|----------|
| [SchwartzTranslationDecay](OSforGFF/SchwartzTranslationDecay.lean) | Schwartz seminorm bounds under translation |
| [QuantitativeDecay](OSforGFF/QuantitativeDecay.lean) | Quantitative polynomial decay estimates |
| [L2TimeIntegral](OSforGFF/L2TimeIntegral.lean) | L² bounds for time integrals: Cauchy-Schwarz, Fubini, Minkowski |

#### Special Functions and Integrals

| File | Contents |
|------|----------|
| [LaplaceIntegral](OSforGFF/LaplaceIntegral.lean) | Laplace integral identity (Bessel K_{1/2}): ∫ s^{-1/2} e^{-a/s-bs} ds |
| [FourierTransforms](OSforGFF/FourierTransforms.lean) | 1D Fourier identities: Lorentzian ↔ exponential decay, triple Fubini reorder |

---

### 2. Basic Definitions

Core type definitions and infrastructure for the formalization.

#### Spacetime and Symmetries

| File | Contents |
|------|----------|
| [Basic](OSforGFF/Basic.lean) | SpaceTime (ℝ⁴), TestFunction, FieldConfiguration, distribution pairing |
| [QFTHilbertSpace](OSforGFF/QFTHilbertSpace.lean) | L² Hilbert space setup for momentum-space analysis |
| [Euclidean](OSforGFF/Euclidean.lean) | Euclidean group E(d) and its action on test functions |
| [DiscreteSymmetry](OSforGFF/DiscreteSymmetry.lean) | Time reflection Θ and discrete symmetries |
| [SpacetimeDecomp](OSforGFF/SpacetimeDecomp.lean) | Measure-preserving SpaceTime ≃ ℝ × ℝ³ decomposition |
| [BesselFunction](OSforGFF/BesselFunction.lean) | Modified Bessel function K₁ via integral representation |

#### Test Function Spaces

| File | Contents |
|------|----------|
| [ComplexTestFunction](OSforGFF/ComplexTestFunction.lean) | Complex-valued Schwartz test functions and conjugation |
| [PositiveTimeTestFunction_real](OSforGFF/PositiveTimeTestFunction_real.lean) | Subtype of test functions supported at positive time |
| [TimeTranslation](OSforGFF/TimeTranslation.lean) | Time translation operators T_s on Schwartz space (continuity proved) |

#### Schwartz Space Integration

| File | Contents |
|------|----------|
| [SchwartzProdIntegrable](OSforGFF/SchwartzProdIntegrable.lean) | Integrability of Schwartz function products |
| [SchwartzTonelli](OSforGFF/SchwartzTonelli.lean) | Tonelli/Fubini for Schwartz integrands on spacetime |

#### Generating Functionals

| File | Contents |
|------|----------|
| [Schwinger](OSforGFF/Schwinger.lean) | Generating functional Z[J] = ∫ e^{i⟨φ,J⟩} dμ, Schwinger functions |
| [SchwingerTwoPointFunction](OSforGFF/SchwingerTwoPointFunction.lean) | Two-point function S₂(x) as mollifier limit |

---

### 3. Free Covariance

The free scalar field propagator C(x,y) = ∫ e^{ik·(x-y)}/(k²+m²) d⁴k/(2π)⁴
and its properties.

| File | Contents |
|------|----------|
| [CovarianceMomentum](OSforGFF/CovarianceMomentum.lean) | Momentum-space propagator 1/(k²+m²), decay bounds |
| [Parseval](OSforGFF/Parseval.lean) | Parseval identity: ⟨f,Cf⟩ = ∫\|f̂(k)\|² P(k) dk |
| [Covariance](OSforGFF/Covariance.lean) | Position-space covariance C(x,y), Euclidean invariance, bounds |
| [CovarianceR](OSforGFF/CovarianceR.lean) | Real covariance bilinear form, square root propagator embedding |

---

### 4. Gaussian Measure Construction

Construction of the GFF probability measure on tempered distributions,
using the Minlos theorem (from the bochner library) with the Gaussian
characteristic functional and two axioms: `schwartz_isHilbertNuclear`
(Schwartz space is nuclear) and `gff_pairing_is_gaussian_axiom`
(1D marginals are Gaussian).

| File | Contents |
|------|----------|
| [GaussianFieldBridge](OSforGFF/GaussianFieldBridge.lean) | Nuclear axiom, Minlos measure construction, Gaussian axiom, derived properties |
| [GFFMconstruct](OSforGFF/GFFMconstruct.lean) | GFF measure interface: covariance → CLM → μ |
| [GFFExponentialIntegrability](OSforGFF/GFFExponentialIntegrability.lean) | Exponential integrability of GFF linear functionals |
| [GaussianMoments](OSforGFF/GaussianMoments.lean) | Gaussian moments: all n-point functions are integrable |
| [GFFIsGaussian](OSforGFF/GFFIsGaussian.lean) | Verification that GFF satisfies Gaussian moment conditions |
| [GaussianFreeField](OSforGFF/GaussianFreeField.lean) | Main GFF assembly: μ_GFF m as a ProbabilityMeasure |

**Note:** `GFFIsGaussian` imports `OS0` because it uses the proved analyticity of
Z[z₀f + z₁g] in ℂ² to identify the two-point function S₂(f,g) = C(f,g) via the
identity theorem.

#### Minlos infrastructure

| File | Contents |
|------|----------|
| [Minlos](OSforGFF/Minlos.lean) | Bridge to bochner library: proven Minlos theorem + uniqueness, Gaussian PD lemmas |
| [MinlosAnalytic](OSforGFF/MinlosAnalytic.lean) | Zero mean from symmetry, integral sign-flip invariance via Minlos uniqueness |

---

### 5. OS Axiom Definitions

| File | Contents |
|------|----------|
| [OS_Axioms](OSforGFF/OS_Axioms.lean) | Formal Lean definitions of OS0 through OS4 (all formulations) |

---

### 6. OS0 — Analyticity

The generating functional Z[∑ zⱼ Jⱼ] is analytic in the complex parameters zⱼ.

| File | Contents |
|------|----------|
| [OS0_GFF](OSforGFF/OS0_GFF.lean) | Proof via holomorphic integral theorem (differentiation under ∫) |

---

### 7. OS1 — Regularity

The generating functional satisfies exponential bounds |Z[f]| ≤ exp(c(‖f‖₁ + ‖f‖₂²)).

| File | Contents |
|------|----------|
| [OS1_GFF](OSforGFF/OS1_GFF.lean) | Proof via Fourier/momentum-space methods and Gaussian structure |

---

### 8. OS2 — Euclidean Invariance

The measure μ is invariant under the Euclidean group E(4).

| File | Contents |
|------|----------|
| [OS2_GFF](OSforGFF/OS2_GFF.lean) | Proof via Euclidean invariance of the free covariance kernel |

---

### 9. OS3 — Reflection Positivity

For positive-time test functions f₁,...,fₙ and real coefficients c₁,...,cₙ:
∑ᵢⱼ cᵢcⱼ Z[fᵢ - Θfⱼ] ≥ 0.

The proof factorizes through the momentum-space mixed representation where the
exponential e^{-ω|t|} splits for positive-time functions, yielding a manifestly
non-negative integrand via the Schur-Hadamard argument.

| File | Contents |
|------|----------|
| [OS3_MixedRepInfra](OSforGFF/OS3_MixedRepInfra.lean) | Infrastructure: mixed representation, Fubini for spacetime integrals |
| [OS3_MixedRep](OSforGFF/OS3_MixedRep.lean) | Mixed representation of bilinear covariance form |
| [OS3_CovarianceRP](OSforGFF/OS3_CovarianceRP.lean) | Direct reflection positivity proof (no spatial regulator) |
| [OS3_ReflectionPositivity](OSforGFF/OS3_ReflectionPositivity.lean) | Main OS3 theorem: rpInnerProduct ≥ 0 |
| [OS3_GFF](OSforGFF/OS3_GFF.lean) | OS3 for GFF: Schur-Hadamard argument on Gaussian exponentials |

---

### 10. OS4 — Clustering and Ergodicity

Two equivalent formulations:
- **Clustering:** Z[f + T_a g] → Z[f]·Z[g] as |a| → ∞
- **Ergodicity:** (1/T)∫₀ᵀ A(T_s φ) ds → E[A] in L²(μ)

The proof establishes polynomial clustering with rate α = 6 (from the mass gap
in d = 3 spatial dimensions), then derives ergodicity via L² variance bounds.

| File | Contents |
|------|----------|
| [OS4_MGF](OSforGFF/OS4_MGF.lean) | Shared infrastructure: MGF formula, time translation duality, exponential bounds |
| [OS4_Clustering](OSforGFF/OS4_Clustering.lean) | Clustering proof via Gaussian factorization + covariance decay |
| [OS4_Ergodicity](OSforGFF/OS4_Ergodicity.lean) | Ergodicity proof via polynomial clustering → L² convergence |

---

### 11. Master Theorem

| File | Contents |
|------|----------|
| [GFFmaster](OSforGFF/GFFmaster.lean) | Assembles OS0–OS4 into `gaussianFreeField_satisfies_all_OS_axioms` |

---

## Building

```bash
git clone https://github.com/mrdouglasny/aqft2.git
cd aqft2
lake build
```

Requires Lean 4 and Mathlib (pinned via `lake-manifest.json`).

## Authors

Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim

## License

This project is licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for details.

## References

- Glimm, Jaffe: *Quantum Physics* (Springer, 1987), pp. 89–90
- Osterwalder, Schrader: *Axioms for Euclidean Green's functions* I & II (1973, 1975)
- Gel'fand, Vilenkin: *Generalized Functions*, Vol. 4 (Academic Press, 1964)
- Reed, Simon: *Methods of Modern Mathematical Physics*, Vol. II (1975)
