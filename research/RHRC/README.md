# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

~~~text
theorem-state anchor = PR #113 merge d3b62817711c4c97f0d817c8b4a4ac0bc646d733
validated theorem head = 2da46eed0068613d904bc67e20790f46bc46818e
validated theorem tree = 066f5f51041b302dfa1a66d84a024660a09acbf5
theorem-bearing merged through = PR #113
RHRC #761 = SUCCESS
Permansson #534 = SUCCESS
CCM build = SUCCESS
ExceptionalZero build = SUCCESS
normalization/source firewall = SUCCESS
forbidden-placeholder gate = SUCCESS
RH = OPEN
~~~

## Current theorem-backed internal route

~~~text
F1 finite canonical negative obstruction                              PROVED / #94
constrained algebra / Euclidean sector                                PROVED / #96-#98
exact centered N-flow + fixed-L negative tail                         PROVED / #100
reversal symmetry / even commutator collapse                          PROVED / #102
direct parity geometry + algebraic D-equivalence                      PROVED / #103
least parity bad + one-dimensional ambient successor shell            PROVED / #105
parity compression + negative eigenmode + non-inheritance             PROVED / #107
nonzero ambient shell projection + exact parity normals/KKT           PROVED / #109
cubic parity channel + compressed defect finrank <=1                  PROVED / #110
global first bad + both predecessor parities nonnegative              PROVED / #112
intrinsic predecessor W + intrinsic shell S, dim_C S=1                PROVED / #112
exact cubic defect factorization through nonzero g_N                  PROVED / #112
canonical direct sum V=W⊕S                                            PROVED / #113
canonical shell coordinate of first-bad negative mode !=0             PROVED / #113
safe shifted predecessor inverse at lam<0                             PROVED / #113
w=-(A-lam I)^(-1)Bs                                                   PROVED / #113
basis-free scalar shifted Schur identity                              PROVED / #113
off-line zero -> one common global-first-bad Schur+cubic state        PROVED / #113

projected A symmetric / shifted coercivity                            DERIVED / OPEN FORMALIZATION
negative index exactly one / unique negative line                     DERIVED / OPEN FORMALIZATION
cubic generator has nonzero intrinsic shell coordinate                LEAD / HYPOTHESIS
cubic-normalized scale-free Schur equation                            LEAD / HYPOTHESIS
shifted resolvent positivity / monotonicity                           DERIVED / OPEN FORMALIZATION
parity nullity difference <=1                                         DERIVED / OPEN FORMALIZATION
common resonance vs one-channel resolvent                             DERIVED / OPEN FORMALIZATION
simultaneous parity-resonance classification                          OPEN
positivity / finite-to-infinite closure                              OPEN
RH                                                                     OPEN
~~~

## Current execution priority

1. **FIRST-BAD-RIGIDITY-E1 — cubic-shell incidence.** Use #113's `intrinsicShellPart_eq_zero_iff` to reduce nonzero shell content to a predecessor non-membership theorem. Attack the odd cubic generator first; then its algebraic even pullback.
2. Prove or falsify the exact projection formula suggested by the post-green calculation: `g_K=d^3-alpha_K d`, `alpha_K=(3K^2+3K-1)/5`, with outer coefficient `K(K-1)(2K-1)/5`. This is a lead until derived from the exact repository projection/indexing conventions.
3. Use `dim_C S=1` to identify the nonzero cubic shell coordinate and the nonzero first-bad eigenmode shell coordinate up to a nonzero scalar.
4. **E2 — cubic-normalized Schur.** Transfer #113's scalar identity to the canonical cubic-shell line and normalize away shell scale.
5. **E3 — shifted block rigidity.** Prove projected predecessor symmetry and quantitative coercivity for `A-lam I`; seek positive-resolvent/norm/monotonicity consequences.
6. **E4 — parity resonance.** Theoremize parity nullity difference and the common-resonance versus one-channel-resolvent dichotomy.
7. Attack or classify simultaneous even/odd resonance at the global first-bad state using KKT, displacement, cubic and shell constraints.

Negative-index-one remains useful but optional unless it becomes a cheap corollary. It must not block the higher-information shell/cubic composition.

The source-faithful `G1-B1B -> G1-final -> S-NEG -> G23` lane remains parallel.

## Why the frontier moved after #113

Before #112/#113 the N-flow shell and parity cubic channel were parallel observations. They are now available **inside one common global-first-bad finite problem**, and the N-flow side has canonical coordinates plus a theorem-backed shifted Schur reduction.

The key interface is

~~~text
intrinsicShellPart x = 0  <->  x ∈ W.
~~~

That turns the shell/cubic comparison into a smaller non-membership problem. If the cubic channel has nonzero shell coordinate, then because `dim_C S=1` it lies on the same shell line as the negative eigenmode's nonzero shell coordinate. The #113 Schur identity is homogeneous in that shell vector, so it can then be normalized onto a canonical cubic-generated shell direction.

This would be the first direct composition of the two one-dimensional bottlenecks.

## Claim firewalls after #113

- `V=W⊕S` is PROVED; shell invariance is not.
- nonzero shell coordinate is not a pure-shell statement.
- #112 proves an exact factorization `F_N(v)=ell_N(v) g_N`, but not `ell_N != 0` and therefore not exact nonzero rank one.
- D is algebraic, not unitary/isometric; do not transport Hermitian interlacing, inertia, angles or norms through it without a separate theorem.
- #113 uses only `A-lam I` with `lam<0`; no `A^-1` at zero is available.
- negative index exactly one, resolvent monotonicity, cubic-shell incidence and resonance exclusion are not promoted theorems.
- the scalar Schur identity is a reduction, not a contradiction.
- no positivity theorem, finite-to-infinite theorem or RH theorem follows from #113.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and gates.
- `RESEARCH_LEADS.md` — accumulated lead ledger.
- `RESEARCH_LEADS_POST_113_DELTA.md` — current post-green implications, new leads and falsification plan.
- `OBSTRUCTION_LEDGER.md` — explicit open obstructions/firewalls.
- `routes/R003_ccm_bridge/README.md` — active route status.
- `CLAIM_REGISTRY.json` / `R003_PROMOTED_BINDINGS.json` — machine promotion surface; do not infer claim promotion from prose alone.

**RH remains OPEN.**
