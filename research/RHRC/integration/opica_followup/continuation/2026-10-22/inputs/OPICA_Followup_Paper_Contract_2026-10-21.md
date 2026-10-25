# OPICA follow-up paper contract

**Date:** 21 October 2026  
**Scope:** Mathematical handoff after the first OPICA implementation; no new repository implementation in this delivery.  
**Authority:** PAPER / DERIVED, self-audited. RH and the independent Step 4 exclusion remain OPEN.

## 1. What the follow-up package contains

The first OPICA PR targets the original 25 statement families and 76 primary roots. That implementation is assigned to ChatGPT Work and must be inspected at its actual final head before fixing exact follow-up imports or file changes. Its proposed inventory is not compiler evidence.

The paper follow-up has two layers:

| Layer | Completed written content | Not implied |
|---|---|---|
| Round 1 | Eight scoped result/control groups: concrete native words, norm-first transfer, allocation, noncompact mixing, near-gap limits, normalized distributional control, coupled-conditioning control, and the renormalized zero-generated measure | Independent signed upper, all native analytic formalizations, global novelty |
| Round 2 | Fifteen labelled statements, with full written arguments: Q1a/Q1b/Q2/Q3, O1/O2/J1, S1a/S1b/S2, H1/H2a/H2b/H3/S3 | Independent exclusion of off-line zeros, new zero-free region, a finished RH programme |

The original 25 families are dependencies, not counted again among these results. Controls are not all claimed as new mathematical discoveries. Round 2 theorem labels use the `R2-` prefix in the ledger. In particular, `R2-H1` (zero-jet measures) is different from `P0-H1` (the original signed separator).

## 2. Acceptance means exact statements, not easy substitutes

### A. Native finite transformation words

Consume Round 1 NB1 with the original single-Q source, actual finite Euler filters, actual residual powers and current completion. Preserve the affine correction recurrence. No arbitrary local unit is automatically a globally bounded isomorphism. A finite word is not an infinite-limit theorem.

### B. Arithmetic rate interface

Implement Round 1 AT1 in a Hilbert space, including complex-valued fields, the positive part of the real signed quadratic, and the `1+` logarithms. It only needs a subexponential Type I norm and low-mask cost. Do not substitute the stronger absolute difference of squared energies as its definition or assume the complete signed upper.

Round 2 Q1a/Q1b must establish uniform constants before the left contour index is selected. Q2 fixes the source, forward convolution and derivative orders. Its proof must consume the physical transform identification rather than invent a field with that transform.

Q3 must keep:

- fixed factor count `r >= 2` and source order `m >= r-1`;
- `Q_T <= T^eta`, with the palette frozen on the entire window;
- the full palette-delay support `i log Q_T`, not just its mass;
- `K > C + r eta + 2r`, `C > 1`;
- the actual real cutoffs, repeated-prime tuples, and product support;
- both low masks if unconfined factors are absorbed into a forward kernel.

The concrete two-factor instance uses `r=2`, `m=1`, `C=2`, `Q=1`, `K=8`. Its source is `Pj`, a fixed derivative of the original source. It is not silently identified with `j` or the autocorrelation `q*j`.

The source-correct full logarithmic-window theorem J5.2 is an inherited PAPER dependency for the conclusion about Theta. Generic rate comparison may be formalized without it. Do not mark the native Theta equality formal until J5.2 and all its native hypotheses are actually formalized. This fixed-order Q3 application does not need MS1.

### C. Recovery, histories and contour costs

O1 uses the joint observation `(P,C)`, not the contrast alone. Its actual optimal recovery norm must be present. O2 retains measurement and source-history error. The degenerate zero operator has recovery cost zero only when the target is also zero.

J1 concerns a common complex contour and a particular Laurent coefficient. Its coefficient error is `r^(-j) E`; derivative normalization adds `j!`. Increasing completion depth changes `j`. Do not replace this budget by compact-time convergence, a distant half-plane norm, or a bare nonzero finite multiplier.

### D. Renormalized zero measures and their derivatives

Round 1 CP1 is a prerequisite, not an axiom named `isMeasure`. The implementation must identify its distributional construction with its order-zero measure formula through local total-variation convergence of cutoff measures.

Keep `0 < Re rho < 1`, `rho != 1/2`, the exact scalar `b_rho`, the true functional equation, and every origin/continuum/lattice correction. An arbitrary tempered distribution is not a locally finite signed measure. The full parameter family is self-dual, but its gap occurs only at the required zeta-zero orders.

R2-H1 stops at each actual multiplicity minus one. Parameter-derivative and origin/gap arguments must remain explicit. Reflection pairs give the same `kappa=rho(1-rho)`, so independence is asserted only at distinct kappa nodes; conjugacy is retained for real measures.

R2-H2a requires the actual first-cell density and Hermite system. Its explicit determinant includes the kappa factors and uses normalized jets. It gives no uniform bound under collisions. R2-H2b is fixed finite span only, using the original P0-H1 separator with all its growth and sign hypotheses.

### E. Native profile and forcing

S1a derives the actual continuous, self-dual L1/L2 profile `h=1-g`, its integer derivative jumps, and its precise Bernoulli tail. It does not assert `h >= 0`.

S1b must retain the distributional force `kappa(sum delta_n - dx)`. The form-domain identity is not an operator-domain eigenvalue theorem. A proof that removes the atoms from `Lh` has changed the equation.

S2 must keep complex conjugation, the actual sample sums, the undivided identity at conjugate-coincident parameters, and all endpoint terms until their limits are proved. Positive Gram matrices alone do not imply real kappa; the included forced finite-dimensional control verifies this scope.

### F. Nonlinear test

S3 concerns the specified square measure, not all nonlinear maps. Prove the exact Fourier defect before drawing a conclusion. Its positive value at the origin and the lattice-periodicity argument exclude lattice-only repair. The self-dual projection exists, but fills the gap; it is not a successful sharp-gap object.

## 3. Dependency order

```text
Existing OPICA algebra / norms / signed separator / source adapters
  ├─ R1 native-word instantiation ─ R2 robust contour jets
  ├─ R1 norm-first comparison ─ R2 fixed-order arithmetic
  │    ├─ Q1a source-product bound
  │    ├─ Q1b zeta/gamma envelope
  │    └─ Q2 localization ─ Q3 logarithmic balance ─ actual masks
  ├─ R2 joint observation + histories + noise
  └─ R1 CP1 renormalized order-zero measure
       ├─ R2 S1 profile, tails and forced equation
       │    └─ R2 S2 actual multi-zero sampling form
       ├─ R2 H1 multiplicity jets ─ H2 finite independence/cone test
       └─ R2 H3 explicit sign cost / S3 square defect
```

Exact repository paths and theorem declarations must be chosen against the completed first PR, not an assumed future interface. The family names in the main paper are suggestions, not files already created.

## 4. Execution and evidence requirements

Every theorem promoted later needs its exact statement, source commit/tree, full axiom/dependency output, physical-source consumer, and required CI disposition. A generic theorem with a rate hypothesis is not a proof of the native rate. No `sorry`, project axiom, or hidden assertion of the desired source membership is permitted.

The present package has 14,672 new finite exact controls in each of normal and optimized Python; the Round 1 checker replays 18,862 per mode. Fifteen additional numerical consistency cases are not interval certified. These receipts are regression evidence only. Independent review of the analytic proofs is not yet supplied.

## 5. Research completion and remaining discovery

The defined Round 2 theorem tranche has written proofs and self-audit. The larger OPICA programme is not finished: it still seeks an independent source-specific restriction incompatible with the hypothetical obstruction. Neither these proofs nor a later green follow-up PR may mark A-X, B-Y, C-Schur, OPEN-J46, the native heat exclusion, D2/WP4, or RH complete merely by adding them to the package.

The strongest positive preparation is now a fixed-source two-factor region of width only powers of `log X` around `sqrt X`, with an independently negligible Type I field. The strongest negative tests identify the retained forcing in a plausible spectral equation and the exact duality cost of squaring a native gapped profile.

A new signed upper, independent sampling constraint, or different native incompatible object would be new mathematical information. It is not supplied by the preservation/interface proofs themselves.
