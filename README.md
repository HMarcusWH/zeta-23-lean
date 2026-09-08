# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

```text
live main after PR #129 = e1192857afed9f68fa4a13143ce690b62191b997
live main tree = 2f042a3b0b3313e7c67d627a58a32d579d4e7ff7

theorem-state anchor = PR #129 merge e1192857afed9f68fa4a13143ce690b62191b997
validated theorem head = 440be3e5b6bf05e94ae2c65b1704d52d20acc9af
validated theorem tree = 2f042a3b0b3313e7c67d627a58a32d579d4e7ff7
theorem-bearing merged through = PR #129
RHRC #838 = SUCCESS
Permansson #611 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened research-control state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + Lean compiler + CI remain authoritative over prose snapshots. PRs #118/#119/#121/#122/#124/#125/#127/#128/#129 advanced theorem authority; Control-v2 semantics have not changed since #117.

## Current RH-directed theorem ladder

```text
off-line zeta zero
  -> compact C² pole-neutral negative W test                       PROVED
  -> strict aperture + legal finite approximation                 PROVED
  -> canonical finite negative obstruction                        PROVED / #94
  -> constrained algebra / Euclidean sector                       PROVED / #96-#98
  -> exact centered N-flow / fixed-L negative tail                PROVED / #100
  -> reversal/parity geometry / algebraic D-equivalence           PROVED / #102-#103
  -> global first bad + predecessor nonnegative                   PROVED / #105,#112
  -> negative first-bad eigenmode + KKT/cubic channel             PROVED / #107,#109,#110
  -> intrinsic V=W⊕S + safe shifted Schur reduction               PROVED / #112,#113
  -> canonical cubic shell + quotient coordinates                 PROVED / #115,#118
  -> exact quotient secular root iff negative eigenmode           PROVED / #119
  -> exact explicit Schur scalar bridge                           PROVED / #121
  -> projected symmetry/coercivity/resolvent metric control       PROVED / #122
  -> ker(A) cubic-coupling classification                         PROVED / #122
  -> ker/range zero-shift dichotomy + canonical endpoint          PROVED / #124-#125
  -> exact one-dimensional zero-shift shell response              PROVED / #127
  -> Re sigma0 < 0 in regular branch                              PROVED / #128
  -> canonical resonant kernel coordinate and 1/(-lam) pole       PROVED / #128
  -> exact cross-parity secular transfer                          PROVED / #129
  -> cubic defect = canonical quadratic source moment             PROVED / #129
  -> off-line zero -> source-explicit first-bad certificate       PROVED / #129

NOW — E4-A4 CANONICAL-SOURCE BRANCH EXCLUSION
  expose and exploit the actual `canonicalSourceMatrix` formula at the
  source moment / overlap interface theoremized in #129;
  attack the regular and resonant branches separately;
  do not divide by `alpha`, `Gamma`, the overlap, or the source moment
  without a separate nonzeroness theorem.

PARALLEL
  E4-B parity shifted-nullity comparison from rank-at-most-one algebra
  E3-C shifted-resolvent identity / strict secular monotonicity / root uniqueness
  E3-B3 general lower-floor deformation theorem
  deformation-budget falsification lane
  source-faithful G1-B1B -> G1-final -> S-NEG -> G23

TARGET
  source-specific exclusion of the actual canonical global first-bad state
  -> negative-root exclusion
  -> no off-line zero via the existing global reduction
  -> explicit bridge to the terminal RH statement
  RH                                                               OPEN
```

## What PRs #127-#129 changed

Let

```text
A = P_W T|_W,
c = intrinsicCubicShellPart,
b = Bc,
u0 = -x0 + c,
F_p(lam) = cubicSecularScalar p ... lam.
```

PR #127 closes the regular zero-shift shell-response step: for a decoupled solution `Ax0=b`, the specific image `T u0` is pure shell, a canonical scalar `sigma0` satisfies

```text
sigma0 • c = T u0,
S0 = star(sigma0) * <c,c>.
```

This does not prove shell invariance and does not make `u0` an eigenvector.

PR #128 sharpens the same regular branch to `Re sigma0 < 0` at the forced negative root and introduces the canonical kernel coordinate `K` on the predecessor block. For `k=K(b)` it proves the exact denominator-free pole identity

```text
(-lam) • K(R_lam b) = k.
```

Thus the decoupled branch has `k=0`, while the resonant branch has `k!=0` and an exact divided `1/(-lam)` pole formula for `lam<0`.

PR #129 exposes the parity/cubic defect directly on the canonical source side. With the orthogonalized quadratic normal `n2`, it proves

```text
cubicDefectFunctional L K v
  = <n2, canonicalSourceMatrix(L,K) v> / <n2,n2>.
```

It also theoremizes the exact parity transfer

```text
F_- = alpha * F_+ + Gamma * sourceMoment(u_+),
```

with `Gamma` represented by the canonical odd trial/cubic overlap. The exact D-transport decomposition retains an explicit predecessor correction term, but #129 does not separately prove that correction nonzero. At an even root this specializes to an exact overlap-times-source product for `F_-`; at an odd root the full balance is retained without division.

A hypothetical off-line zero therefore forces one global-first-bad finite state carrying this exact source-explicit cross-parity certificate. This is stronger rigidity/exposure, not branch exclusion.

## Current mathematical frontier

The post-#128 countermodel pass changed the route. Generic Hermitian/Schur algebra, one-dimensional shell response, resonance, parity rank-at-most-one structure, KKT geometry and displacement structure are not enough by themselves: synthetic centered-grid countermodels can preserve those structures while retaining a negative successor obstruction.

The next theorem must therefore spend information from the actual canonical source formula, including its diagonal/source-channel values. The immediate high-information questions are:

- what exact decomposition does `<n2, canonicalSourceMatrix u_+>` have in the production source formula?
- can that source moment or its combination with the #129 overlap be forced to a sign or nonvanishing incompatible with the regular branch?
- can the exact resonant kernel pole coexist with the same source-explicit parity identity?
- which proposed source inequality survives the known generic countermodels?

## Permanent firewalls

- RH remains OPEN.
- `V=W⊕S` is proved; shell invariance is not.
- `T u0 ∈ S` for the special zero-shift trial image does not make `u0` an eigenvector.
- D-equivalence is algebraic, not unitary/isometric.
- the predecessor correction term in `D c_+` is explicit theorem data and must be retained in general; its nonzeroness is not theoremized.
- exact cubic factorization gives rank at most one, not automatically exact rank one.
- `ker A` means the kernel of the projected successor predecessor block `P_W T|_W`; it is not the predecessor-size compressed-operator kernel.
- no whole-space or range-only `A^-1` is introduced at zero.
- `Re S0 < 0` and `Re sigma0 < 0` are not branch exclusion.
- resonance and an exact `1/(-lam)` pole are not automatically contradictory.
- #129 does not prove `alpha`, `Gamma`, the overlap or the canonical source moment nonzero or sign-controlled.
- root uniqueness, if proved, is not root absence.
- generic/displacement-preserving countermodels do not refute the actual canonical CCM source matrix; they refute arguments that use too little source-specific information.
- source-normalization, machine claim promotion, negative-root exclusion and RH remain unchanged unless separately theorem-backed.

## Living research records

- `research/RHRC/README.md`
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS_POST_129_DELTA.md`
- `research/RHRC/RESEARCH_LEADS.md` — accumulated historical option ledger; newer deltas supersede stale per-entry currentness
- `research/RHRC/OBSTRUCTION_LEDGER.md`
- `research/RHRC/DEAD_ROUTES.md`
- `research/RHRC/countermodels/POST_129_STRUCTURAL_COUNTERMODELS_2026_09_08.md`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/control_v2/README.md`
- `research/RHRC/CLAIM_REGISTRY.json`
- `research/RHRC/R003_PROMOTED_BINDINGS.json`

Machine claim/binding promotion must not be inferred beyond entries actually present in the registries.

**RH remains OPEN.**
