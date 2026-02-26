# Gaussian Measure Construction

Construction of the Gaussian Free Field (GFF) probability measure on distributional field configurations via the `gaussian-field` library's generic nuclear-space construction.

## Mathematical Background

The GFF measure $\mu_{\text{GFF}}$ is the probability measure on $\mathcal{S}'(\mathbb{R}^4)$ characterized by its generating functional:

$$\int e^{i\langle\omega,f\rangle}\,d\mu(\omega) = \exp\!\left(-\tfrac{1}{2}\,C_m(f,f)\right)$$

where $C_m(f,g) = \int\!\!\int f(x)\,G_m(x-y)\,g(y)\,dx\,dy$ is the free covariance with massive propagator $G_m$.

## Construction Method

The measure is constructed as a **pushforward** by the `gaussian-field` library, which provides a generic construction for any nuclear Fréchet space equipped with a continuous linear map into a Hilbert space. No Minlos theorem is needed—the measure is built directly from an infinite product of standard Gaussians.

> For the historical Minlos-based approach previously used in this project, see [old/04_gaussian_measure_minlos.md](old/04_gaussian_measure_minlos.md).

## Architecture

The construction has three layers:

### Layer 1: Covariance Operator (aqft2)

**File:** [CovarianceR.lean](../OSforGFF/CovarianceR.lean)

The embedding map $T : \mathcal{S}(\mathbb{R}^4) \to L^2(\mathbb{R}^4, \mathbb{C})$ is defined as `embeddingMapCLM m`, a continuous linear map satisfying the key identity:

$$\|T(f)\|^2_{L^2} = C_m(f,f)$$

This is the theorem `freeCovarianceFormR_eq_normSq`. The embedding maps test functions into the complex $L^2$ space via the Fourier-space representation of the propagator ("square root" of the propagator).

### Layer 2: Generic Gaussian Measure (gaussian-field library)

**External dependency:** `gaussian-field` at `../gaussian-field`

Given:
- A nuclear Fréchet space $E$ (with `NuclearSpace E`)
- A continuous linear map $T : E \to_L H$ into a real Hilbert space $H$

the library constructs `GaussianField.measure T`, a probability measure on $\text{WeakDual}\;\mathbb{R}\;E$ with characteristic functional $\exp(-\tfrac{1}{2}\langle T(f), T(f)\rangle_H)$.

The `NuclearSpace TestFunction` instance comes from `schwartz_nuclearSpace` in the gaussian-field library, which provides `NuclearSpace (SchwartzMap D F)` for any finite-dimensional domain.

### Layer 3: Bridge (aqft2)

**File:** [GaussianFieldBridge.lean](../OSforGFF/GaussianFieldBridge.lean)

This is the single integration point between gaussian-field and aqft2. It:

1. Provides `InnerProductSpace ℝ (Lp ℂ 2 volume)` via `InnerProductSpace.rclikeToReal`
2. Proves the **bridge lemma** connecting inner products to covariance:

$$\langle T(f), T(g)\rangle_{\mathbb{R}} = C_m(f,g)$$

   by polarization from the diagonal identity $\langle T(f), T(f)\rangle = \|T(f)\|^2 = C_m(f,f)$.

3. Wraps `GaussianField.measure (embeddingMapCLM m)` as `gfMeasure m : ProbabilityMeasure FieldConfiguration`

4. Derives all GFF properties from gaussian-field's generic theorems:

| Property | Bridge theorem | Gaussian-field source |
|----------|---------------|-----------------------|
| Char. functional | `gfMeasure_charFun` | `GaussianField.charFun` |
| Gaussian pushforward | `gfMeasure_pairing_is_gaussian` | `GaussianField.pairing_is_gaussian` |
| $L^p$ integrability | `gfMeasure_pairing_memLp` | `GaussianField.pairing_memLp` |
| Centered | `gfMeasure_centered` | `GaussianField.measure_centered` |
| Second moment | `gfMeasure_second_moment` | `GaussianField.second_moment_eq_covariance` |
| Fernique (exp form) | `gfMeasure_pairing_expSq_integrable` | `IsGaussian.exists_integrable_exp_sq` |

## Key Type Identifications

| aqft2 name | gaussian-field name | Definition |
|------------|---------------------|------------|
| `FieldConfiguration` | `GaussianField.Configuration TestFunction` | `WeakDual ℝ TestFunction` |
| `MeasurableSpace FieldConfiguration` | `GaussianField.instMeasurableSpaceConfiguration` | cylindrical σ-algebra |
| `freeCovarianceFormR m f g` | `@inner ℝ _ _ (T f) (T g)` | bridge lemma equates these |

## Key Declarations

### GaussianFieldBridge.lean

| Declaration | Description |
|-------------|-------------|
| `instInnerProductSpaceReal` | Real inner product on $L^2(\mathbb{R}^4, \mathbb{C})$ via `rclikeToReal` |
| `instSeparableSpaceTargetHilbertSpace` | $L^2$ is separable (from second countability) |
| `inner_embeddingMapCLM_self` | $\langle T(f), T(f)\rangle_{\mathbb{R}} = C_m(f,f)$ |
| `inner_embeddingMapCLM_eq_freeCovarianceFormR` | $\langle T(f), T(g)\rangle_{\mathbb{R}} = C_m(f,g)$ (polarization) |
| `gfMeasure` | `ProbabilityMeasure FieldConfiguration` wrapping `GaussianField.measure` |
| `gfMeasure_charFun` | $E[e^{i\omega(f)}] = e^{-\frac{1}{2}C(f,f)}$ |
| `gfMeasure_pairing_is_gaussian` | Pushforward is $\mathcal{N}(0, C(\phi,\phi))$ |
| `gfMeasure_pairing_memLp` | $\omega(\phi) \in L^p$ for all $p < \infty$ |
| `gfMeasure_centered` | $E[\omega(f)] = 0$ |
| `gfMeasure_second_moment` | $E[\omega(\phi)^2] = C(\phi,\phi)$ |
| `gfMeasure_pairing_expSq_integrable` | $\exists \alpha > 0$, $e^{\alpha\omega(\phi)^2}$ integrable |
| `gfMeasure_real_characteristic` | GJ generating functional form |
| `gfMeasure_isCenteredGJ` | Centered in the GJ interface sense |

### GFFMconstruct.lean

| Declaration | Description |
|-------------|-------------|
| `CovarianceFunction` | Structure packaging covariance data |
| `isCenteredGJ` | Predicate: $\int\langle\omega,f\rangle\,d\mu = 0$ for all $f$ |
| `isGaussianGJ` | Predicate: $Z[J] = e^{-\frac{1}{2}S_2(J,J)}$ |
| `gaussianFreeField_free` | The GFF probability measure (`:= GaussianFieldBridge.gfMeasure m`) |
| `μ_GFF` | Abbreviation for `gaussianFreeField_free` |
| `gff_real_characteristic` | Characteristic functional identity |
| `gff_pairing_is_gaussian` | Pushforward is 1D Gaussian |
| `gaussianFreeField_pairing_memLp` | Fernique-type $L^p$ integrability |
| `gff_second_moment_eq_covariance` | Second moment = covariance |
| `gaussianFreeField_free_centered` | Zero mean |
| `gaussianFreeField_pairing_expSq_integrable` | Exponential square integrability |

## From Measure to Gaussianity

The generating functional identity $Z[J] = e^{-\frac{1}{2}S_2(J,J)}$ for **complex** test functions (the `isGaussianGJ` property) requires extending the real characteristic functional to complex parameters. This is done in two additional files:

### MinlosAnalytic.lean — Symmetry and Centering

| Declaration | Description |
|-------------|-------------|
| `negMap_measurable` | $\omega \mapsto -\omega$ is measurable |
| `integral_neg_invariance` | $\mu$ is invariant under negation |
| `moment_zero_from_realCF` | First moment vanishes |

### GFFIsGaussian.lean — Analytic Continuation

| Declaration | Description |
|-------------|-------------|
| `gff_two_param_analytic` | $(z_0,z_1) \mapsto Z[z_0 f + z_1 g]$ analytic on $\mathbb{C}^2$ |
| `gff_cf_agrees_on_reals_OS0` | Complex $Z$ agrees with real $Z$ on real parameters |
| `gff_complex_characteristic_OS0` | $Z_{\mathbb{C}}[J] = e^{-\frac{1}{2}C(J,J)}$ for complex $J$ |
| `gff_complex_generating` | $Z_{\mathbb{C}}[J] = e^{-\frac{1}{2}S_2(J,J)}$ |
| `isGaussianGJ_gaussianFreeField_free` | The GFF satisfies `IsGaussianGJ` |

**Proof idea:** For fixed real test functions $f, g$, both sides of the identity are entire functions of $(z_0, z_1) \in \mathbb{C}^2$. They agree on $\mathbb{R}^2$ (from the real characteristic functional), so by analytic continuation they agree everywhere. Any complex test function $J = f + ig$ is recovered by setting $z_0 = 1, z_1 = i$.

## Moments and Correlation Functions

### GaussianMoments.lean

| Declaration | Description |
|-------------|-------------|
| `gaussian_complex_pairing_abs_sq_integrable` | $\|\langle\omega,\phi\rangle\|^2$ integrable for complex $\phi$ |
| `gaussian_pairing_product_integrable_free_2point` | $\langle\omega,\phi\rangle\langle\omega,\psi\rangle$ integrable |
| `covariance_bilinear_from_general` | `CovarianceBilinear` holds for the GFF |

## Dependency Chain

```
  gaussian-field library
  ├── NuclearSpace (SchwartzMap D F)     [schwartz_nuclearSpace]
  └── GaussianField.measure T           [generic construction]
          │
          ▼
  CovarianceR.lean
  └── embeddingMapCLM m : TestFunction →L[ℝ] L²(ℝ⁴,ℂ)
      freeCovarianceFormR_eq_normSq : C(f,f) = ‖T(f)‖²
          │
          ▼
  GaussianFieldBridge.lean
  ├── inner_embeddingMapCLM_eq_freeCovarianceFormR  [bridge lemma]
  └── gfMeasure m : ProbabilityMeasure FieldConfiguration
      + charFun, centered, moments, Fernique
          │
          ▼
  GFFMconstruct.lean
  └── gaussianFreeField_free m := gfMeasure m
      + gff_real_characteristic, etc.
          │
          ▼
  GFFIsGaussian.lean
  └── isGaussianGJ_gaussianFreeField_free   [analytic continuation]
          │
          ▼
  GFFmaster.lean
  └── gaussianFreeField_satisfies_all_OS_axioms
```

## References

- Bogachev, V. I. *Gaussian Measures*, AMS Mathematical Surveys and Monographs (1998).
- Glimm, J. and Jaffe, A. *Quantum Physics: A Functional Integral Point of View*, Ch. 6.
- Simon, B. *The $P(\phi)_2$ Euclidean (Quantum) Field Theory*, Ch. I.
