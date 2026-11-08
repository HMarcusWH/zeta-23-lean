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

## Increment 3C — certified near-band coupling and synthetic off-line controls

[nearband_bound.py](nearband_bound.py) replaces the floating projectors of
E-D1 by a projector-free certificate. For `b > s` the even power
`φ_k(λ) = ((b − λ)/(b − s))^(2^k)` dominates the indicator of `(−∞, s]` on the
whole real line. Hence, for the same exact `A` (DERIVED),

`M(s) = C·1_(−∞,s](A)·Cᵀ ⪯ C·φ_k(A)·Cᵀ`,

and the right side is computed by `k` Arb squarings of the enclosed native
`A`. Trace and `λ_max` upper bounds are certified at L=4, 5 and 6 in both
parities, at cutoffs `s = ε + 10⁻⁸, 10⁻⁶, 10⁻⁴, 10⁻²`
([evidence/increment3c](evidence/increment3c/SUMMARY.json)). At
`s = ε + 10⁻⁶` the certified traces are about `1.7–2.0e-6` (L=4),
`3.6–4.9e-6` (L=5) and `5.9–9.2e-6` (L=6). The bound is resolution-limited
(recorded per row), so it controls `M(s + resolution)` rather than `M(s)`
sharply.

**Synthetic falsification controls** (SYNTHETIC objects, certified statuses):

* **S1.** A rank-one negative term on the first low coordinate leaves `C`
  and `A` byte-identical, and the pencil is certified negative. Small
  coupling cannot be a sign criterion.
* **S2.** Two adjacent actual zeros are merged into an off-line quartet
  `½ ± δ ± iγ` in the explicit-formula representation of the native form.
  The mode transform reproduces the native pole channel to rounding, and the
  truncated zero sum reproduces `pole − arch − prime` at L=2 (odd error
  `1.7e-5` with 400 zeros).
  * At a common tolerance below threshold, the native pencil is certified
    positive and the low-band synthetic pencil certified negative. Their
    certified coupling bounds agree within 5% at every state (0.004–4.3%).
  * A high-band quartet makes `A` itself indefinite.
  * At the split, coupling responds only at L=6 (`1.2e-2` against `9e-6`).
* **Detection threshold (EXPERIMENTAL).** `ε*(δ) ≈ c(L)·δ²`, with
  `c ≈ 9.4, 17.9, 28.2` in the low band at L=4, 5, 6.
  * The `ε=1/2` and `1/3` checkpoints are certified blind to `δ=1/10`
    quartets.
  * The `ε=1/4` checkpoint at L=6 detects them. This was predicted in the
    session before the L=6 run ([L6_PREDICTION.json](evidence/increment3c/L6_PREDICTION.json)),
    but it was not preregistered.
  * Fixed-margin detection of an actual off-line zero is already proved in
    Lean. This signal adds only the dependence on δ and L.

Near-band smallness explains why the scalar-gap estimate fails. It is not a
positivity mechanism: the sign lives in the coupled Schur complement (CR23,
CR24).

## Increment 3D — the joint signed source `−arch − prime`

M50 makes every slice energy exactly `−Re⟨arch u,u⟩ − Re⟨prime u,u⟩`.
[signed_source.py](signed_source.py) studies that expression on the E-D1
slices ([evidence/increment3d](evidence/increment3d/SUMMARY.json)). The
floating prime channel matches the Arb channel to `2.5e-13`, and the pole
restriction is `1e-58`.

* **Cancellation on the near-null subspace** V (threshold `10⁻²`; dimension
  51/50, 142/141 and 346/345 at L=4, 5, 6). Each channel alone is indefinite
  with O(1) eigenvalues (`−arch` in about `[−2.1, 5.4]`, `−prime` mirrored).
  The joint form lies in `[−5e-15, 7.5e-3]`. Any channel-separable estimate
  loses O(1) (CR25).
* **The archimedean channel alone is not positive.** This is certified with
  exact witnesses at L=4 and 5.
* **The whole prime cell is needed.** Dropping only the largest prime power
  gives certified negative values: q=53 at L=4 (`−1.06e-5` even, `−2.7e-3`
  odd) and q=139 at L=5 (`−0.22`, `−0.27`). At L=6 (q=401) the values are
  floating-negative. The truncated forms are not native objects (CR26).
* **Bottom vector.** `−arch` is an O(1) positive budget (2.0–3.0) consumed by
  the prime atoms with little internal cancellation
  (`Σ|atom|/|Σ atom| = 1.04–1.29`). The partial sums reach zero only at the
  end of the cell.
* **DERIVED family ordering (CR27).** At equal exact degree,
  `S_IR − S_tail = C[(qᵐI − Tᵐ)/a + (a⁻¹I − A⁻¹)(Tᵐ − T²ᵐ)]Cᵀ ⪰ 0`. It is
  certified through the factorization with `Mid ≻ 0` at L=4 and 5 (m = 8, 64)
  and at L=2 in CI, where a perturbed `X` breaks the identity. It is not
  formalized in Lean.

**Reading.** On V the closing inequality is the exact cancellation of two
indefinite O(1) channels across the full prime cell: the explicit-formula
picture, consistent with the zero-sum calibration of Increment 3C. No
decomposition into independently controlled native terms was found. This is
evidence that a (C1) supplier has the strength of Weil positivity on these
slices (a sharp interface), not a sub-RH step. A source-specific inequality
at unbounded apertures remains **OPEN**.

## E-H7 — the frozen n = 5 law, run and scored

E-H7 ran exactly under its hashed rules at L=7 (K=2401, Q=1096), tolerance
`1/5`, split 1200, ladder 1…256 and tail up to 64
([evidence/increment3e](evidence/increment3e/SUMMARY.json)). The committed
numpy-free scorer [eh7_score.py](eh7_score.py) applies each acceptance rule
literally, and CI recomputes the scoring from the records. The two parities
ran concurrently, with no change to any tool or parameter.

| Prediction | Outcome | Rule | Observed | Record |
| --- | --- | --- | --- | --- |
| P9 | CONFIRMED | degree 32 in both parities | even 32, odd 32 | see E-H7_OUTCOMES.json |
| P10 | FAILED | tail FALSIFIED_BOUND at every degree 1–64 | even: 1 F, 2 F, 4 F, 8 F, 16 F, 32 F, 64 U; odd: 1 F, 2 F, 4 F, 8 F, 16 F, 32 F, 64 U | see E-H7_OUTCOMES.json |
| P11 | CONFIRMED | near-band count in [200, 500] | even 240, odd 240 | see E-H7_OUTCOMES.json |
| P12 | CONFIRMED | coupling ≤ 1e-4, response ≤ 1e-3 | coupling 1.05e-06 / 2.06e-06, response 5.27e-06 / 1.03e-05 | see E-H7_OUTCOMES.json |
| P13 | CONFIRMED | checkpoint and full Schur certified, scalar gap falsified with charge ≥ 80 | checkpoint CERTIFIED / CERTIFIED, charge 97.2 / 106.1 | see E-H7_OUTCOMES.json |

F = FALSIFIED_BOUND, U = UNKNOWN_PRECISION. At degree 64 the tail witness is not certainly negative in either parity, so P10 fails as written.

**Confirmed: P9, P11, P12, P13. Failed: P10.** A failed prediction stays failed. P13's "native checkpoint" is scored
through the stated consumer implication: a certified full Schur form together
with `A ⪰ aI` gives the hypotheses of
`blockEnergy_nonneg_of_inverse_residual_certificate`. The statuses are kernel
decisions of the frozen tools (level 2). The frozen tool does not retain
ladder witnesses in its records (receipt limitation, recorded). Separately
from the scoring, `independent_check.py` reconstructs the n = 5 checkpoint
`Q_p ≥ −⅕‖x‖²` at L=7 in both parities at 512 bits (level 3, CERTIFIED,
about 23 minutes each).

## Increment 3F — formal supports, witness receipts and the record of what cannot be built

**Lean (local pinned Linux compile; gate PASS at 101 modules, 1213 complete
types and axiom sets, 100 controls; only `propext`, `Classical.choice` and
`Quot.sound`).**

* `MomentLeakage` (M51, CR28) proves the compressed commutator with every term
  retained: `[Vᴴ D₀ V, Vᴴ E V] = Vᴴ [D₀, E] V + Z Lᴴ - L Zᴴ`, for leakage
  `(1 - V Vᴴ) D₀ V = W Lᴴ` of any finite rank. The one-normal and no-leakage
  cases are included. The native instantiation (actual carrier basis and
  canonical source) is not formalized, and `Vᴴ [D₀, E] V` is not shown to
  vanish.
* `FiniteCertificateSoundness` (M52, CR29) proves, for exact real data:
  * the kernel's shifted-factor rule is sound;
  * `τ > 0` is necessary;
  * an exact negative witness refutes `A ⪰ 0`;
  * a positive pencil `F + εG` gives the checkpoint inequality.

  The native enclosure bridge is not proved, so numerical certificates are not
  Lean facts about the actual source.
* `SourceColumnTrace` (M53, CR30) proves, for `C = H S`:
  * `G = Sᴴ H² S` and `Cᴴ H C = Sᴴ H³ S`;
  * the column projection is a self-adjoint idempotent;
  * `tr(((1 - P) H)ᴴ ((1 - P) H)) = tr(H²) - tr(G⁻¹ Sᴴ H⁴ S)`.
* Two new semantic controls reject the commutator without its leakage terms
  and the certificate with `0 ≤ τ`. The suite stays at 100 because the pinned
  isolated-worker recipe uses Lean's default `maxErrors = 100`. Raising it is
  a recipe-version change.

**Witness receipts.** [ed1_receipts.py](ed1_receipts.py) reruns the E-D1 and
E-H7 pencils and keeps a receipt for every decision:

* for CERTIFIED rows: `τ`, the certified residual bound and the factor
  enclosure hash (consumer `posDef_of_shifted_factor`);
* for FALSIFIED rows: the exact dyadic witness vector and its value enclosure
  ([evidence/increment3f](evidence/increment3f/SUMMARY.json)).

Every status shared with the frozen records agrees, at L=4, 5 and 6 in both
parities, and at L=7 (E-H7) in both parities, with no difference at all. The only differences are tail rows that the
frozen L=6 records never tested (degree 128, beyond their limit 64). CI
rechecks `τ > 0`, the residual bound `< τ²` and every witness sign from the
recorded data.

**Model map and harvest.**

* `MODEL_PRESERVATION.json` adds MP09–MP12:
  * the low-block and off-line synthetic controls;
  * the truncated prime cell;
  * the archimedean-only form.
* `WORKFLOW_HARVEST.json` records 02847b5: 23 of 24 workflows passed and none
  failed. Round4 passed with ACCEPTANCE. Round2's `generated` job was
  cancelled by the 2fc6eee push.

**Not buildable by engineering (recorded in `OPEN_PREMISES.json`).**

* The independent arithmetic supplier (Increment 5 and the acceptance of work
  package F). It is the open closing estimate, a sharp interface with Weil
  positivity.
* `Step4Terminal` and Increment 6.
* The direct C2 alternative.
* The native enclosure bridge.
* The universal approximate-kernel paper audit.

**RH, Step 4 and the closing inequalities remain OPEN.**

## Revision 3 — Increments 4A–4C and 5A (8 November 2026)

The supplied revision-3 plan is imported byte for byte in
[revision3/](revision3/IMPORT_RECORD.json). It was reviewed against the
repository; seven implementation refinements are recorded in
[REVIEW_OF_REVISION3.json](revision3/REVIEW_OF_REVISION3.json). None narrows a
required domain.

**Qualified baseline (U1).** `dab9fbe` is qualified in Round4 run
42438907841, attempt 1. All 24 workflows passed; 95 of 97 checks passed and 2
optional checks were skipped. The gate covered 101 modules, 1213 declarations
and 100 controls. M51–M53 are therefore current-head-qualified in their
general algebraic scope. Human release review is NOT_ESTABLISHED. The compact
index is [QUALIFIED_BASELINE.json](QUALIFIED_BASELINE.json); the full evidence
stays in the CI artifacts.

**4A — sources and registers.**

* [SOURCE_LEDGER.json](SOURCE_LEDGER.json) gains 27 items from a delta
  refresh of the folder:
  * seven reports TEXT_REVIEWED, four with hashes reported by the revision-3
    package;
  * the two L=5 certificates FETCHED with content hashes;
  * the rest DISCOVERED.
* The refresh is a delta, not a full re-listing.
* [WORKFLOW_HARVEST.json](WORKFLOW_HARVEST.json) records the qualified
  `dab9fbe` harvest. The 2fc6eee cancellations were a cascade, not failures.
* New entries:
  * CR31–CR37 (PG, SE, the fixed-rate exclusion, SB/AD, C2-SE, NC and the
    candidate SG);
  * MP13–MP19;
  * the closing leaves PG, SE, SB and C2-SE.

**4A-G — sharded controls.** Lean stops after 100 errors, so the controls run
in two shards. Each shard compiles under the fixed worker source name
`RejectedSemanticMutations.lean`.

* Shard 01 is byte-identical to the pinned 84-control pre-frontier text.
* Shard 02 holds all 25 frontier controls.
* Every control must own exactly one type-mismatch error. Missing, duplicate,
  stray or environmental errors fail closed in the gate, in qualification and
  in the independent verifier.
* The control omitted in 3F is restored (FM17). Eight new controls cover the
  new contracts (FM18–FM25).
* The dab9fbe CI log also satisfies the stricter per-control binding
  (100/100).

**4B — coarse-growth consumers (Lean, local pinned compile).**

* `GrowthClosure` (M54):
  * the finite-phase native witnesses lie in the exact moment slices, with
    depth `-exp(βL)` at arbitrarily late apertures;
  * a fixed-parity bound `-C exp(αL)` at every late aperture excludes
    displacements above `α`;
  * (SE) and (PG) imply Mathlib `RiemannHypothesis`.
* `CofinalSemiboundedClosure` (M55):
  * an explicit-margin reproof of the recentred phase energy;
  * (AD): every `M`, every late aperture, both parities, depth `-M`;
  * (SB) implies RH, and (C1) implies (SB).
* `C2GrowthClosure` (M56): (C2-SE) and its polynomial adapter imply RH. The
  bound in `t = 2a` becomes rate `2α` in `a`, with every explicit-formula term
  retained.

**4C — native displacement (Lean, local pinned compile).**
`NativeMomentDisplacement` (M57) works with the full canonical source.

* NC: `[D₀, A]ᵢⱼ = (nᵢ + nⱼ)(dᵢ - dⱼ)` is rank four, and
  `Vᴴ [D₀, A] V = 0` for boundary-flat columns. This follows from the existing
  displacement theorem, with no pole split.
* Composed with M51: `[Vᴴ D₀ V, Vᴴ A V] = (Vᴴ A W) Λᴴ - Λ (Vᴴ A W)ᴴ`.
* `(D₀ + β) r` is proportional to `1` (even) or to `n` (odd), so `D₀ u`
  stays pole-neutral on the slice. It leaves the slice exactly through `M₆`
  (even) or `M₇` (odd): rank-one leakage in functional form.
* The orthonormal factor `w ℓᴴ` is not built in Lean.

Local evidence: development gate PASS at 105 modules, 1275 complete types and
axiom sets, and 109 controls (84 + 25). Only `propext`, `Classical.choice` and
`Quot.sound` appear. Current-head CI is required.

**5A — the frozen candidate (SG), EXPERIMENTAL SIGNAL.**
[sg_candidate.py](sg_candidate.py) rebuilds the actual parity-reduced source
from the repository Arb primitives. It measures the terms of the candidate
(SG) from the 8 November geometry report (CR37) at L = 4–7
([evidence/increment5a](evidence/increment5a/SUMMARY.json)).

* The report's six-state table is reproduced to every printed digit.
* NC, rank-one leakage and `[J, H] = zℓᴴ - ℓzᴴ` hold to about `1e-14`.
* `‖z‖ ≈ 0.65 L`.
* The reduction loss `2‖ℓ‖‖z‖/g_J` is between `2·10⁴` and `3·10⁶`. The actual
  geometry off-diagonal norm is between 3 and 8, so the Frobenius step
  discards about `K²`.
* Frozen L=7 predictions hit 15 of 18. The misses are operational:
  `λ_max(H)` growth slowed, and the even diagonal minimum rose.
* With non-zeta prime weights every identity survives while the slice turns
  negative. Its growth also looks polynomial at these apertures, so finite
  tables cannot discriminate PG or (SG).

**Status (U8).**

* Completed generic supports: M51–M53 (qualified) and M54–M57 (local).
* Pending native applications:
  * the orthonormal leakage factor;
  * a Lean (SG) → (PG) composition;
  * the enclosure bridge, only if a computational route consumes it.
* Optional assurance: the universal-kernel audit and the metric adapter.
* Open supplier: an actual-source inequality for one OR branch with its exact
  quantifiers.

**RH, Step 4 and every closing inequality remain OPEN.**

## Revision 3 — stage 4D (8 November 2026)

**Lean (local pinned compile; current-head CI required).**

* `NativeLeakageFactor` (M58, CR40) works with a **Riesz slice** `S = F ⊓ ker⟪q, ·⟫`.
  For `x ∈ F` it gives `x = P_S x + c(x) r` with `r = P_F q ⟂ S` and
  `c(x) = ⟪r, x⟫ / ‖r‖²`.
  * Natively, `D₀ u − P_S D₀ u = (M₆(u)/‖r_e‖²) r_e` (even) and
    `(M₇(u)/‖r_o‖²) r_o` (odd). This is the explicit rank-one leakage factor.
  * The ambient slices are proved equal to the existing `evenMomentSlice` and
    `oddMomentSlice`.
  * With NC for the full canonical source, the compressed commutator is exactly
    rank two:
    `⟪u, P D₀ P A v − P A P D₀ v⟫ = c(v) conj⟪r, A u⟫ − conj(c(u)) ⟪r, A v⟫`.
* `GeometryReconstruction` (M59, CR41) proves the reconstruction bound
  `Re x*Hx ≥ (h₀ − 2 n_z n_ℓ / g) ‖x‖²` under the rank-two relation. The
  off-diagonal part is bounded entrywise by Cauchy–Schwarz, so no dimension
  factor appears.
  * Its geometry-eigenbasis form on a Riesz slice takes its relation from M58.
  * A **geometry-response certificate** gives the existing slice bound at its
    floor, on the native energy and physical norm.
  * `FixedParityGeometryResponsePolynomial` (SG with explicit geometry) implies
    PG and Mathlib `RiemannHypothesis`.
  * The certificate premise is OPEN: the gap, diagonal and response numbers at
    every late aperture.

Four new controls bring the suite to 113 (84 + 29). They reject:

* the leakage coefficient read as `M₄`;
* the reconstruction floor without its factor 2;
* the certificate floor replaced by zero;
* cofinal certificates presented as SG.

Local development gate: 107 modules, 1321 complete types and axiom sets, and 113
controls. Only `propext`, `Classical.choice` and `Quot.sound` appear.

**Exact replays** ([evidence/increment4d](evidence/increment4d/SUMMARY.json)).
[exact_controls_r3.py](exact_controls_r3.py) uses exact integers and fractions,
in both Python modes.

* MP15: product kernel −1 against lcm Gram 4 at N = 10, and `Q_N = 2M(Y) − M(N)`
  for N ≤ 100.
* MP14: aligned scalars with `a = 2⁻ᵏ` and `b = 1` have nonbacktracking eigenvalue
  `−(4ᵏ − 1)/2ᵏ`. The determinant identity and the reverse-instability bound are
  also checked.
* MP18: the two-by-two model.
* MP20: the algebra of the comparison-density seeds.
* MP21: the rational causal model.
* MP22: the critical-zero boundary-layer constants.
* MP13: the slice claim of the external L5 core certificate coincides with our
  level-3 certified L5 record. Its core and pencil are BLOCKED (archive not
  retrievable).

**Sources.**

* The folder membership is now complete: 239 items, none deleted.
* Three reports posted this afternoon are TEXT_REVIEWED:
  * *Centered Prime Continuation* (CR38, CR42, CR43, MP20):
    * paid prime powers at most `2L²`;
    * the exact decomposition `Q = R₀ + D_ψ` with `R₀ ≥ c*‖f‖²`;
    * an unconditional explicit-PNT bound at exponential rate ½, which is not PG;
    * a positive PNT-envelope comparison density that fails PG on the exact
      carrier;
    * the remaining supplier (CP) on the centered ordinary-prime discrepancy.
  * *Abel Closure Attempt* (CR39): genuine critical zeros refute the L²
    first-variation shortcut. The sequence-membership criterion stays OPEN.
  * *Methodology Postmortem* (MP21, MP22).

**RH, Step 4 and every closing inequality remain OPEN.**

## Next increments

1. **The supplier (5B/6, OPEN).** One branch with exact quantifiers. The sharpest
   current targets are:
   * (CP), the centered ordinary-prime discrepancy;
   * the (SG) certificate;
   * (C2-SE);
   * the CAUSAL dyadic covariance bound.

   A proof must use a property of the actual primes that the comparison density
   (MP20) lacks.
2. Sharpen the (SG) reduction: bound the Cauchy-structured off-diagonal directly
   (observed `O(L)` against a current `O(K²)` loss). Formalize the polynomial
   geometry gap only when a certificate is in reach.
3. The native enclosure bridge, the detection margin (CR24), CR27 and the
   nonorthogonal trace identity, each only if a chosen proof consumes it.

Only a proved supplier composed with these consumers, validated on the final
head, could support a Step 4 claim.
