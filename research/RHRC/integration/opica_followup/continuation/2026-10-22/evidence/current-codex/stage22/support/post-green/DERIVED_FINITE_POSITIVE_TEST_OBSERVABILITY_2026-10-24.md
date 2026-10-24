# Derived finite positive-test observability — 2026-10-24

**Status: DERIVED mathematical consequence, not a Lean theorem or compiler receipt. No originality claim.** The generic mechanism is classical finite-dimensional cone separation and positivity of measures. This note identifies a possible application to the actual OPICA zero-jet span and compares it with the earlier finite-detection programme. No production source or compiler process was changed.

Source inspection is pinned to code commit `2440dcde7607baa7bcff2ce9626effa1ae9f3f07`, tree `dee5bc2fa3148ad42e3ef1fef17c4acf6a408f99`. `Zeta23/OPICAFollowup/FiniteSpanSeparation.lean` SHA256 is `69d2d89a32311dec71bc9831b21717097e94a980d7b9dfcd0f8dbf10f8fbb9f5`. The owner's exact current 44-consumer replay was still running when this note was written; this note creates no additional compiler authority. The underlying three finite-span primary roots have separate earlier sealed compiler/expected-type/control evidence. Current optional canonical-pair interfaces remain subject to their own exact owner receipts.

## Exact hypotheses and the proposed conclusion

Fix a **single** dimension `n ≥ 1` and a **single** independent real basis of actual finite normalized zero-jet combinations. Each basis element is constructed from finite valid `JetDatum` lists: actual zeta zeros, strict-strip hypotheses, and jet orders below the actual analytic multiplicity. Let `ν_a` be the genuine canonical Jordan signed measure obtained from the actual realified combination with coefficients `a ∈ ℝⁿ`. The constructor and its real linearity are the existing `zeroJetRealSpan` / `realBasisCombinationData` construction, not an arbitrary measure packet.

Write `U = ℝ \ ℤ`. The already established actual-span inputs give:

1. Every `ν_a` is a real signed Radon measure, locally finite on `ℝ`. Its linear-growth tempered embedding, gap, selfduality and origin properties are proved internally for the actual construction.
2. If the restriction of `ν_a` to `U` is a positive measure, then its canonical negative Jordan part vanishes on `U`. The public finite-span positive-only-zero result gives `ν_a = 0`.
3. Independence of the fixed embedded real basis then gives `a = 0`. This is `independent_real_span_basis_coefficients_zero`, composed from the public qualitative root. Independence must not be silently asserted for every raw Re/Im generator list.
4. Compactly supported real test pairings are genuinely real and linear in `a`: `∫ φ dν_a = Σ_i a_i ∫ φ dν_i`. This follows from the actual distribution/compact-restriction identities already proved for the constructor. All compact tests are integrable; no finite total mass on the whole line is assumed.

**Derived conclusion.** There exist `n+1` real functions

`φ₀, φ₁, …, φₙ ∈ C_c^∞(U)`, each pointwise nonnegative,

viewed as compactly supported Schwartz functions on `ℝ`, such that

`∫ φ_i dν_a = a_i` for `1 ≤ i ≤ n`, and `∫ φ₀ dν_a = −Σ_i a_i`.

Consequently, all `n+1` pairings are nonnegative if and only if `a = 0`. For this fixed choice of tests there is also a `c > 0` such that

`min_{0≤j≤n} ∫ φ_j dν_a ≤ −c ‖a‖₂` for every `a`.

These are **linear integral observations**, not point samples, canonical finite Weil quadratic values, or an effective construction of tests. The tests and their sizes depend on the chosen actual basis. No bound on their support, Schwartz seminorms, coefficient cost, or behaviour as the basis changes is asserted.

## Proof, including the nonclosed-image issue

Let `D₊(U)` be the cone of real, nonnegative, smooth functions with compact support contained in `U`. Define

`L(φ) = (∫ φ dν₁, …, ∫ φ dνₙ) ∈ ℝⁿ`, and `C = L(D₊(U))`.

The set `C` contains zero and is closed under addition and multiplication by every nonnegative real scalar. This uses actual finite sums of test functions: a finite union of compact supports is compact and remains inside `U`. Thus `C` is a convex cone. **We do not assume that this image cone is closed.**

If `a · y ≥ 0` for every `y ∈ C`, then `∫ φ dν_a ≥ 0` for every `φ ∈ D₊(U)`. Such tests characterize positivity of the restriction of a real signed Radon measure to `U`. Here is a local justification rather than an added measure hypothesis. If the negative part on `U` were nonzero, local finiteness and inner regularity give a compact set `K ⊂ U` of positive negative mass on which the positive part is zero. Outer regularity gives a relatively compact open neighbourhood of `K`, still inside `U`, with positive mass smaller than the negative mass of `K`. A smooth nonnegative cutoff equal to one on `K`, bounded by one, and supported in that neighbourhood has strictly negative signed integral, a contradiction. This cutoff is an actual compact Schwartz test on `ℝ`.

The existing actual-span positive-only-zero theorem and real basis independence now give `a = 0`. Hence the polar cone `C* = {a : a·C ≥ 0}` is exactly `{0}`.

Set `K = closure(C)`. Its polar equals `C*` by continuity of finite-dimensional linear functionals. If `K` were a proper closed convex cone, choose `z ∉ K` and a nearest point `p ∈ K`. The projection inequality gives `(p−z)·(y−p) ≥ 0` for all `y ∈ K`. Applying it to `0` and `2p` gives `(p−z)·p = 0`, so the nonzero vector `p−z` is in `K*`, contradicting `K* = {0}`. Therefore `closure(C) = ℝⁿ`.

**Density alone is not the last step.** Because `C` is convex and finite dimensional, it contains an affine simplex with nonempty interior: select `n+1` points of the dense set close enough to the vertices of a nondegenerate simplex. Thus `interior(C)` is nonempty. The convex-set identity `interior(closure C) = interior(C)` then gives `interior(C) = ℝⁿ`, hence `C = ℝⁿ`. Equivalently, one can approximate the vertices of a simplex containing zero in its interior closely enough that their convex hull still contains a ball about zero; that ball lies in `C`, and positive scaling then fills `ℝⁿ`. Neither argument assumes closedness of the image.

Now choose actual preimages under `L` of `e₁,…,eₙ` and `−Σ_i e_i`. These preimages are the desired nonnegative compact smooth tests. Their pairing identities follow from real linearity. If all pairings are nonnegative, every `a_i ≥ 0` and `−Σ_i a_i ≥ 0`, forcing every coefficient to vanish. Conversely zero coefficients give zero pairings.

On the compact Euclidean unit sphere, the continuous function `a ↦ min_j L(φ_j)·a` is strictly negative at every point. Its maximum is therefore a strictly negative number `−c`. Positive homogeneity gives the quantitative inequality; zero coefficients are immediate. No lower bound for `c` with controlled test-function costs follows from this argument.

The convex/interior mechanism is classical; see Rockafellar, *Convex Analysis* (Princeton University Press, 1970), the relative-interior and separation chapters ([publisher's book record](https://www.jstor.org/stable/j.ctt14bs1ff)). For prospective formalization, the pinned Mathlib source already contains `Convex.interior_closure_eq_interior_of_nonempty_interior` ([source at the actual Mathlib pin](https://github.com/leanprover-community/mathlib4/blob/51e6992efd06126df61a496bebf8f49482a4e129/Mathlib/Analysis/Convex/Topology.lean#L268)). This source link is an available formal ingredient, not a claim that this complete application has been compiled.

## Minimal number of one-sided linear tests

For `n ≥ 1`, **no collection of `m ≤ n` real linear observations** can have `F(a) ≥ 0 ⇒ a = 0` componentwise. If the observation map has rank below `n`, its nonzero kernel supplies a counterexample with all values zero. Otherwise `m=n` and the map is invertible; the preimage of the all-ones vector is a nonzero counterexample with all observations positive. Thus `n+1` is sharp for this precise one-sided linear-inequality task. This is not a minimum number of point samples, absolute-value observations, or quadratic tests. For `n=0`, zero tests suffice and the coefficient space is already trivial.

This is the classical geometry of positive spanning sets, not a new cardinality principle. Chandler Davis's original *Theory of Positive Linear Dependence*, *American Journal of Mathematics* 76 (1954), 733–746, is the historical primary reference ([published article record](https://www.jstor.org/stable/2372648), DOI 10.2307/2372648). The published primary research paper by Hare, Jarry-Bolduc and Planiden, *Nicely structured positive bases with maximal cosine measure*, *Optimization Letters* 17 (2023), 1495–1515, explicitly presents the negative-direction detection characterization (Lemma 4), the minimal `n+1` size, and its positive-basis context ([full published text](https://link.springer.com/article/10.1007/s11590-023-01973-2)). The only prospective application here is realization of those familiar covectors by actual **nonnegative compact off-lattice tests** for the OPICA span; even that is a derived source-specific corollary, not a priority claim.

## Comparison with paper 5 and repository history

The full body of *Persistent Finite Detection of Off-Critical Zeros in the Weil–CCM Hierarchy*, 2026-09-03 v0.2, was re-read at its finite-detection and persistence statements. File SHA256 is `79fcbc48e5ad95f25f46eb4285d0b107e11b0bac7ab90ab0d4af918052bfaba1`; finite canonical detection is at lines 503–509 and persistence at 650–673.

| Existing result | Its actual object and quantifiers | Relation to this note |
|---|---|---|
| Paper 5, finite canonical detection | One hypothetical off-critical zero forces some `L,N,u` in the legal boundary-flat centered Fourier hierarchy with negative complete canonical Weil quadratic value. | Already supplies finite detection of an off-critical zero in its canonical hierarchy. This note does not replace or strengthen that theorem's quantifiers. |
| Paper 5, centered persistence | The same physical hard-window `C²` test and the same negative quadratic value persist under exact centered zero extension to all larger `N`. No effective threshold is supplied. | This note gives no centered nesting, canonical finite matrix, or effective threshold. |
| `ExceptionalZero/FiniteNegativeObstruction.lean`, `ConstrainedFiniteObstruction.lean`, `FixedCellWitnessPersistence.lean` | Actual complete Weil negativity, constrained finite negative witnesses, and local aperture persistence. | These old source-level finite-detector results were found; an unqualified claim of a new finite-detection principle would be misleading. |
| `CCM/CanonicalPoleNeutralNesting.lean` and `NestedFinite.lean` | Exact physical-vector, norm, pole-neutral and canonical-quadratic preservation under centered embeddings. | No such embedding is constructed by the positive-test argument. |
| `OPICA/ObservationCompatibility.lean`, `OPICAFollowup/JointObservation.lean` | Recovery is a kernel condition; finite-dimensional observation/recovery maps and their optimal norms are already formalized. | Once the positive tests are constructed, their injective linear observation map can feed these existing interfaces. The missing ingredient is the constrained **positive off-lattice test realization**, not another abstract recovery theorem. |
| `FiniteSpanSeparation.lean` | Actual finite realified zero-jet measures have no nonzero off-lattice-positive combination; a fixed independent basis has a weighted negative-mass norm bound. | Supplies the genuine source-specific cone obstruction. The qualitative positive-only-zero result and independence already suffice; the full quantitative budget is not logically necessary for finite-test existence. |

The difference worth preserving is narrow: **one fixed actual measure span, every nonzero coefficient direction, and a finite family of pointwise nonnegative compact off-lattice tests with linear integral observations**. Paper 5 concerns a negative *quadratic* complete Weil value at a canonical finite Fourier vector, not these positive testing functions or every direction in a fixed zero-jet measure span. No bridge from these adapted integrals to the existing canonical finite matrices or physical point samples has been proved here. No identical constrained positive-test statement was found in the bounded source search, but that is not a worldwide or complete-corpus priority claim. The missing seventeenth manuscript body remains a corpus-completeness limitation already reported elsewhere.

**Novelty disposition:** classical separation/compactness mechanism; at most a source-specific corollary and useful formalization target. Do not call it a new finite-detection theorem or a new originality candidate merely because the actual OPICA instantiation is useful.

## Falsification and next steps

- Removing basis independence allows a zero or duplicate basis vector; then every test annihilates a nonzero coefficient direction.
- Removing the no-positive-combination property allows a nonzero positive measure; every nonnegative test has nonnegative value and the conclusion fails.
- Nonconvex dense sets and infinite-dimensional proper dense linear subspaces show why density cannot be promoted to surjectivity without the finite-dimensional convex-interior argument.
- Varying or colliding spectral bases can make test supports, amplitudes and recovery costs degenerate. Rescaling a basis already changes normalized test costs. No uniform changing-family statement follows.
- For the current canonical Re/Im pair, the explicit independence input is **nonreal spectral κ**, not an unproved blanket claim about every raw realification. Subject to its separate exact compiler receipt, that actual pair would give `n=2` and therefore three adapted nonnegative integral tests. It still does not exclude the zero: nothing supplies nonnegativity of all three source-dependent pairings.

The smallest formalization target is the local real-measure positivity characterization by compact nonnegative Schwartz tests supported in an open set. The existing `LocallyFiniteSignedMeasure.measure_eq_of_schwartz_integral_eq` proof already constructs compact smooth mollifications and can guide it. Next prove the finite-dimensional cone-image lemma, then instantiate with the existing public qualitative span root and actual coefficient linearity. Only after those compiled lemmas should an explicit source-dependent positive-test consumer be considered. A separate bridge and quantitative test-cost control would be needed before using canonical finite sampling, changing dimensions, or an RH exclusion argument. RH and Step 4 remain OPEN.
