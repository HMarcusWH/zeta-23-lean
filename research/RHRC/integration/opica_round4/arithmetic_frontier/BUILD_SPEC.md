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
* **Signal: tiny positive bottoms** (*corrected in 2B, R1*). Positive brackets
  exist only at L=2, 9/4, 5/2 and L=4. At L=5 and L=6 only shifted lower bounds
  and positive Rayleigh *upper* bounds exist. The earlier "super-exponentially
  small" law is withdrawn: finite brackets establish no asymptotic law.
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

## Increment 2B — acceptance repair, corrections and level-3 replay

The revision-2 review found nine scoped defects (R1–R9) in Increment 2's
evidence semantics. None is a negative vector for the native form. Each has a
scoped entry in [CORRECTIONS.json](evidence/increment2b/CORRECTIONS.json), and the
original records stay bound to their preserved producer bytes.

* **Kernel.** [certificates.py](certificates.py) is floating-point free:
  * a shift `τ > 0` is required, and the input must be symmetric;
  * endpoints are exact, and norms are enclosed in the declared Gram;
  * `FALSIFIED_BOUND` requires an exact witness with a certainly negative value;
  * the three certificate families are distinct.

  Its 24 countercontrols run in the locked CI lane without skips.
* **Engine v2.** [native_slice.py](native_slice.py) only proposes; the kernel
  decides. The basis is the exact `Y_* = Z − E_P(C E_P)⁻¹C Z`, and the full
  physical Gram is carried. Block statements are labelled COORDINATE or
  PHYSICAL. Near-null statistics record absolute and signed counts against
  `N_main(T)`.
* **Revalidation.** All Increment 2 states were regenerated in
  [evidence/increment2b](evidence/increment2b/SUMMARY.json):
  * the archive margins, the L=4 checkpoints and brackets, L=5 and the E-H6 L=6
    quarter bound;
  * the scalar-gap witnesses and brackets reproduce the version-1 values;
  * the historical GEOMETRIC_TAIL degree-64 certificate is certified at L=4,
    `ε=1/2`, and falsified with an exact witness at `1/1024`, at L=5 (`1/3`)
    and at L=6 (`1/4`). P4 is scored on that family, as its `q^m/a` heuristic
    requires, and is therefore **confirmed**, not refuted (R5). The
    INVERSE_RESIDUAL family passes at degree 64 at every checkpoint;
  * the exact high-support unshifted legal subspace with support `|n| > split`
    (dimension 124 at L=4, split 128) has physical Rayleigh values of about
    `2·10⁻⁶`, so the quarter law fails on that support at the named splits.
    This does not falsify a historical certificate on a narrower support, a
    higher support threshold or a different constant (CORRECTIONS R10); the
    historical support and constant are still not imported.
* **Level 3.** The numpy-free
  [independent_check.py](independent_check.py) reconstructs the checkpoints
  with its own exact elimination basis and a blocked interval Schur
  certificate. It covers L=4 at `1/2`, L=5 at `1/3` and L=6 at `1/4`, in both
  parities. The source assembly is shared and disclosed; level 4 (Lean bridge)
  remains OPEN.

## Increment 3A — pole-channel annihilation (Lean)

**PROVED in a local pinned compile; current-head CI is still required.**
[PoleChannel.lean](../../../../../Zeta23/OPICARound4/ArithmeticFrontier/PoleChannel.lean)
(M50) reuses the production two-profile annihilation theorem and the even
corollary. On both actual pole-neutral carriers, and hence on both moment
slices, it proves three statements:

* the full pole output vector is zero;
* the pole sesquilinear form vanishes;
* `evenNativeEnergy = -Re⟨arch u,u⟩ - Re⟨prime u,u⟩`, and likewise for odd.

`EvenMomentSliceLowerBound L K ε` is therefore equivalent to a lower bound on
`-arch - prime` over the slice (`evenMomentSliceLowerBound_iff_arch_prime`), and
likewise for odd. The channels are the unchanged production `canonicalArchMatrix`
(direct equation (4.4), scalar terms included) and `canonicalPrimeMatrix` (every
prime power). No sign is asserted. This compresses the signed budget of every
(C1) checkpoint to the joint prime–Archimedean expression of work package F.

The development math gate PASSES at 94cb6d8, on the pinned Linux compile.
It reports 98 modules and 1186 complete types and axiom sets, with only
`propext`, `Classical.choice` and `Quot.sound`, and 98 intended rejections.
The first run failed because control 13 lacked `open Matrix`; that failure is
recorded in commit 94cb6d8.

## Increment 3B — coupled-response comparison (E-D1)

[evidence/increment3b](evidence/increment3b/SUMMARY.json) compares three
sufficient inequalities on the same shifted pencils. All three use the
`certificates.py` kernel and are tested on a degree ladder 1…256:

* scalar gap;
* geometric tail (exact `P_m(A)`, with a certified upper bound `b`);
* inverse residual (any exact `X`; the Lean consumer).

| Checkpoint | Inverse residual, smallest tested degree | Geometric tail | Near band: directions / coupling mass | Scalar-gap charge |
| --- | --- | --- | --- | --- |
| L=4, `ε=1/2` | 4 | 64 | 1 / `1.3e-6` | 12.4 |
| L=5, `ε=1/3` | 8 | none ≤ 64 (128 unresolved) | 22 / `1–2e-6` | 30–31 |
| L=6, `ε=1/4` | 16 | none ≤ 64 | 90–91 / `0.6–2.7e-6` | 58–62 |

The full Schur form with `X = A⁻¹Cᵀ` is certified at every state, including
L=4 at `ε=1/1024`, where every tested degree of both polynomial families
fails. **Signal:** the scalar-gap failure is an overcharge of a near band
that receives almost no coupling mass. The doubling inverse-residual degree is
frozen, with fixed numerical rules and hashed tools, as the E-H7 law for n=5
([E-H7_PREDICTIONS.json](evidence/increment3b/E-H7_PREDICTIONS.json)). It has
**not been run**.

Neither observation is a sign bound. A convergent inverse approximation
represents a negative Schur complement just as faithfully. The bands use
floating projectors.

## Not built yet

The leakage modules, checker soundness, the enclosure bridge, the universal
kernel and any arithmetic supplier. See [OPEN_PREMISES.json](OPEN_PREMISES.json)
and [EXPERIMENTS.json](EXPERIMENTS.json).

## Next increments

1. **Work package F (critical).** On the compressed carriers `Q = -arch - prime`
   exactly (M50). Seek a decomposition of the joint signed budget into
   independently controlled native terms plus an explicit remainder.
2. Run E-H7 under the frozen rules (P9–P13). A failed prediction is recorded
   as failed.
3. Certified spectral projectors (or a projector-free bound) for the near-band
   coupling mass, which would turn CR23 into a certificate input.
4. `FiniteCertificateSoundness` and the native enclosure bridge, but only if
   the chosen proof consumes numerical certificates.

Only a proved supplier composed with these consumers, validated on the final head,
could support a Step 4 claim.
