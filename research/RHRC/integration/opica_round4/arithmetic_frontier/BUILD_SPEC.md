# Arithmetic frontier — build specification and Increment 1 record

**RH and Step 4 remain OPEN.** This directory turns the PR #299 research into a
source-bound search for an independent signed inequality. Increment 1 narrows
the closing targets, binds them to the exact native objects and supplies sound
finite consumers. It supplies **no new arithmetic sign**.

Parent: PR #299 head `9c517db0befa1131bb60d37cfef2888ed69447a9`, tree
`6d737c3e3f74a607ae1e1a4b958cc1e2cf9854e9`. Lean modules live in
`Zeta23/OPICARound4/ArithmeticFrontier/`; their exact contracts are M43–M49 in
[MADNESS_CONTRACTS.json](../MADNESS_CONTRACTS.json).

## The decisive distinction

“We can represent, compress or verify the target” is not “the actual arithmetic
forces the target inequality.” Every new theorem below is of the first kind. The
arithmetic-supplier node stays OPEN until an independent proof exists.

## Closing contracts (OR branches)

| Branch | Exact premise | Consumer | Status |
| --- | --- | --- | --- |
| **C1** | `CofinalMomentSliceVanishingErrorBounds`: for every `n ≥ 1` some `L ≥ n+2` and one parity have `Q_p(L,x) ≥ -(1/n)‖x‖²` on the **entire** moment slice at `K = ⌈L⁴⌉` | `riemannHypothesis_of_cofinal_moment_slice_bounds` | premise OPEN |
| **Packet** | `EventualDisjointQuarticGroundRestriction`: at late disjoint quartic states both exact ground responses are `< 1` | `riemannHypothesis_of_eventual_disjoint_quartic_ground_restriction`; packet-uniform and one-output consumers | premise OPEN |
| **C2** | eventual `-C ≤ hyperbolaT(…)` on the literal long term | existing `riemannHypothesis_of_actualCorrelationLongTerm_eventual_lower` | premise OPEN |
| **K3** | eventual polynomial lower bound on a literal K3 scalar (`E_ord`) | DERIVED paper reduction, not formalized | OPEN |
| **Causal** | source-preserving causal Gram residual → 0 | none | OPEN |

No branch is a hidden prerequisite of another; one complete branch suffices.

**Strength.** Each consumer proves its premise *sufficient* for RH. The premises
are also expected to be *necessary*: on pole-neutral carriers the native form is
a literal Weil energy, so RH would make it nonnegative and C1 would hold with
zero error (DERIVED, not formalized); an archived external prototype proves C2
equivalent to RH. These contracts are therefore sharp interfaces, not
independent sub-RH progress. Only an independent supplier changes the state.

## What Increment 1 proves (local pinned Linux compile; current-head CI required)

* **Exact carriers.** The even slice is the actual even pole-neutral carrier with
  physical `M4 = 0`; the odd slice has `M3 = M5 = 0`. Boundary-flat and pole
  conditions are inherited. The energy is the literal compressed canonical form;
  the norm is the inherited Euclidean norm used by the negative witnesses.
* **Coordinates and metric.** The existing seed diagonal `β + n²`, `β=(L/4π)²`, is
  the specification chart `L² + 16π²n²` divided by `16π²`. The slices are exactly
  `{y even : M0=M2=M4=M6=0}` and `{y odd : M1=M3=M5=M7=0}`; every bound transports
  through the full Gram `D²`, never the identity. A coordinate tolerance `ε` gives
  only the physical tolerance `ε/β²`; a physical `ε` gives only `ε(β+K²)²`.
* **Dimensions.** `dim = K-3` and `K-4` (natural subtraction) for `K ≥ 2`; both
  slices vanish at `K = 3`, where the bound holds for *every* tolerance. At the
  quartic cutoff the dimensions are at least 13 and 12, so C1 is not vacuous.
* **C1 consumer.** C1 contradicts the existing fixed margin at the same aperture,
  cutoff, parity, carrier and norm. A tolerance sequence tending to zero along
  apertures tending to infinity supplies C1; no rate or interpolation is needed.
* **Packet consumer.** Both Rayleigh bottoms are eigenvalues, so the packet's full
  spectral disjointness forbids every tie. The pointwise consumer then needs only
  the two ground tests; the older all-cutoff wrapper implies the new one.
* **Finite certificates.** (C3): the exact inverse-residual identity and soundness
  of `D - CX - X*C* + X*AX - a⁻¹R*R ≥ 0`, with the scalar inverse-gap surrogate as
  the `X = 0` case. (C4): leakage `η ≤ ε/4` against the whole complement and a core
  margin `-(11ε/12)` give `H + εI ≥ 0`, also in nonorthogonal column form. (E2): a
  trial with margin `d` keeps margin `d - 3η` on its projected core component.

Twelve new semantic controls reject the substitutions listed in
[MODEL_PRESERVATION.json](MODEL_PRESERVATION.json). They are API guards, not
counterexamples. The retained 1079/90/84 scope is hash-bound and mandatory.

## Explicit refinements of the specification

* `SOURCE_CONSTRAINTS.json` is unchanged: its arithmetic-target set and digest are
  protected by the existing contract checks. New constraints live in
  [CONSTRAINT_REGISTER.json](CONSTRAINT_REGISTER.json).
* `EXPECTED_TESTS.json` is unchanged: new assertions extend existing test methods.
* The trace formula `η² = tr H² - tr(G_I⁻¹(H⁴)_II)` is not formalized; (C4) takes
  the operator-norm leakage, which the Frobenius residual dominates.
* Drive reports are DISCOVERED only: their bytes were not persisted, so no hash is
  recorded ([SOURCE_LEDGER.json](SOURCE_LEDGER.json)).

## Not built in this increment

Finite-evidence import and replay (L=4, L=5), the predeclared L=6 horizon, the
leakage modules, checker soundness, the enclosure bridge, the universal kernel
and any arithmetic supplier. See [OPEN_PREMISES.json](OPEN_PREMISES.json) and
[EXPERIMENTS.json](EXPERIMENTS.json).

## Next increments

1. Import the L=4/L=5 evidence with hashes and replay it into `BUDGET_SCHEMA`
   records, preserving every failed surrogate.
2. Run `E-H6` (`n=4`, `L=6`, `K=1296`, dimensions 1293/1292, `ε ≤ 1/4`). In
   unweighted seed coordinates the physical `1/4` needs tolerance `β²/4 ≈ 0.0130`.
3. Compare complete signed budgets at the same states and freeze a candidate law
   before any new scale.
4. Formalize only the reductions that law needs; then seek the independent supplier.

Only a proved supplier composed with these consumers, validated on the final head,
could support a Step 4 claim.
