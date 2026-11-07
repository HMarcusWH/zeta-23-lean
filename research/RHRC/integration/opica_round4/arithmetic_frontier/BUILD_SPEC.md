# Arithmetic frontier — build specification and increment record

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

## Increment 2 — finite evidence replay and the E-H6 horizon

**Scope.** Research certification of finite inequalities at named states. These
results are not Lean theorems. They supply no arithmetic sign for any
unbounded family, and RH and Step 4 remain OPEN. Records are in
[evidence/increment2/](evidence/increment2/SUMMARY.json). Each record is
hash-bound to the engine
[native_slice.py](native_slice.py) and to the repository backend
`research/RHRC/routes/R003_ccm_bridge/canonical_source_arb.py`.

**Engine.** The engine works on the exact Lean carriers: the even slice is
pole-neutral with `M0=M2=M4=0`; the odd slice is pole-neutral with
`M1=M3=M5=0`. It uses `K=⌈L⁴⌉`, `Q=⌊e^L⌋` (prime cell certified) and the
physical inherited norm directly. A floating basis proposal is corrected in
Arb so that every column lies exactly in the slice. Its Gram matrix is
certified `≥ 1/4`, so the basis spans the slice of the proved dimension.

A tolerance holds when a shifted Cholesky certificate passes: `F+εG−τI−RRᵀ`
has its Frobenius norm enclosed below `τ`. A bottom is bracketed by two
bounds: an exact inverse-iteration Rayleigh vector from above, and a certified
margin from below. The floating-point-free checker
[independent_check.py](independent_check.py) re-derives the small states on its
own path: the backend's direct full matrix, an exact elimination basis and
interval LDLᵀ.

| State | Result |
| --- | --- |
| L=2, 9/4, 5/2 (archive) | margins `2⁻⁶⁴, 2⁻¹⁰⁰, 2⁻¹⁴⁶` certified in both parities by both constructions; bottoms match the archive to every printed digit |
| L=4, K=256 (dims 253/252) | 81/81 external principal entries overlap; `ε=1/2, 1/1024` certified; bottoms bracketed in `[2⁻⁸¹⁶, 1.311·10⁻²⁴⁵]` (even) and `[2⁻⁸⁰², 2.174·10⁻²⁴¹]` (odd) |
| L=5, K=625 (dims 622/621) | `ε=1/3` (n=3) and `1/1024` certified |
| **E-H6** L=6, K=1296, Q=403 (dims 1293/1292) | `Q_p ≥ −¼‖x‖²` certified on both full slices, the n=4 checkpoint of (C1) |

**Failures preserved (estimates, never the native form).** At every tested
point the scalar inverse-gap surrogate is refuted, because the complement
block carries near-null directions. The reported `49/100 ≤ A ≤ 9` and the
degree-64 coupled certificate are reproduced at `ε=1/2`, and that certificate
also passes at n=3 and n=4. It fails at `ε=1/1024`, where the native form is
still certified. The fixed `1/4` high-gap law fails, and the upper cap `A ≤ 9`
fails at L=5 and L=6. No Lean consumer needs that cap.

**Structure found.**

* **DERIVED.** The pole kernel is `S(uuᵀ−vvᵀ)`, so the pole energy is
  identically zero on both carriers. The native energy there is exactly
  `−arch−prime`.
* **Signal: channel cancellation.** The two remaining channels cancel at the
  bottom vectors. Bounding them separately is refuted: on the even slice the
  separated loss is `−5.14`, `−6.49` and `−7.45` at L=4, 5, 6.
* **Signal: tiny positive bottoms.** The slice bottoms are positive but
  super-exponentially small: `ln λ_min / K ≈ −2.7 → −2.2`.
* **Signal: near-null count.** The number of near-null directions follows
  `dim − N(2πK/L)`, where N is the zero count. The deficits are 1, 4 and 5
  at L=4, 5, 6. The L=6 instance was frozen with a timing caveat; see
  [E-H6_PREDICTIONS_ADDENDUM.json](evidence/increment2/E-H6_PREDICTIONS_ADDENDUM.json).
  A later scan ([nullcount_scan.py](nullcount_scan.py)) shows the law does not
  depend on the threshold. Below `10⁻²` the count equals `round(dim − N(T))`
  within 1 at all six points, and about one more eigenvalue drops out per two
  decades down to `10⁻¹³`.

**Predeclared E-H6 predictions** ([outcomes](evidence/increment2/E-H6_OUTCOMES.json)):

* P1, P3, P5, P6 and P7 were confirmed.
* P2 was partly refuted: the scalar-gap constant grows with L.
* P4 was refuted: the degree-64 certificate passed at `q⁶⁴/a = 1.29`.

**CI.** The source-numerics lane now runs
`tests/test_arithmetic_frontier_native.py` in both modes. Its CI part is
floating-point free. The engine's planted controls need numpy, which is not in
the hash-locked CI environment, so they are reported as skipped there.

## Not built yet

The leakage modules, checker soundness, the enclosure bridge, the universal
kernel and any arithmetic supplier. See [OPEN_PREMISES.json](OPEN_PREMISES.json)
and [EXPERIMENTS.json](EXPERIMENTS.json).

## Next increments

1. E-D1 completion: record `M(s)=C1_(0,s](A)C*` and the minimal coupled degree
   `m(n,L)` at the checkpoints n=2,3,4, then freeze a degree law before n=5.
2. Test the near-null count law at a new aperture with a predeclared, threshold-
   stable count (E-NULLCOUNT), and relate the near-null space to the zero
   ordinates without assuming RH.
3. Formalize only the reductions a frozen law needs (CR17 is the first
   candidate). Then seek the independent supplier.

Only a proved supplier composed with these consumers, validated on the final head,
could support a Step 4 claim.
