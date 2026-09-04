# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

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

PR #113 is merged. Its final validated theorem head and merged `main` have the identical theorem tree `066f5f51041b302dfa1a66d84a024660a09acbf5`.

## Current RH-directed theorem ladder

~~~text
off-line zeta zero
  -> compact C² pole-neutral negative W test                       PROVED
  -> strict aperture + legal finite approximation                 PROVED
  -> canonical finite negative obstruction                        PROVED / #94
  -> constrained algebra / Hermitianity / displacement            PROVED / #96
  -> Euclidean constrained sector / exact dimensions              PROVED / #98
  -> exact centered N-flow / fixed-L negative tail                PROVED / #100
  -> exact reversal symmetry / even commutator collapse           PROVED / #102
  -> direct parity geometry / D : V+ ≃ V-                         PROVED / #103
  -> fixed parity bad tail + least bad size                       PROVED / #105
  -> predecessor parity sector nonnegative                        PROVED / #105
  -> exact Euclidean successor parity shell finrank 1             PROVED / #105
  -> parity-constrained Euclidean compression                     PROVED / #107
  -> negative first-bad compressed eigenmode                      PROVED / #107
  -> negative first-bad eigenmode is not inherited                PROVED / #107
  -> nonzero 1D ambient successor-shell projection                PROVED / #109
  -> exact even/odd parity normal spaces + KKT                    PROVED / #109
  -> Euclidean algebraic D-equivalence                            PROVED / #110
  -> M(Du)=D(Mu) on even constrained sector                       PROVED / #110
  -> g_N = P_- d³ != 0 for N>=2                                  PROVED / #110
  -> parity compressed intertwining defect finrank <= 1           PROVED / #110
  -> GLOBAL least bad + both predecessor parities nonnegative     PROVED / #112
  -> intrinsic predecessor W and 1D shell S inside successor V    PROVED / #112
  -> exact cubic defect factorization F_N(v)=ell_N(v) g_N         PROVED / #112
  -> W and S complementary: V = W ⊕ S                             PROVED / #113
  -> canonical predecessor/shell coordinates                      PROVED / #113
  -> first-bad negative mode has nonzero canonical shell part     PROVED / #113
  -> A-lam I bijective for lam<0                                  PROVED / #113
  -> w = -(A-lam I)^(-1) B s                                     PROVED / #113
  -> basis-free scalar shifted Schur identity                     PROVED / #113
  -> off-line zero -> same finite global-first-bad Schur+cubic    PROVED / #113

NOW — FIRST-BAD-RIGIDITY-E
  E1 cubic-shell incidence:
    prove the cubic generator is not in the centered predecessor image
    hence its canonical intrinsic shell part is nonzero
    do the odd channel directly and the even channel through algebraic D^-1
  E1b one-dimensional composition:
    compare the nonzero cubic shell coordinate with the negative-mode shell coordinate
  E2 cubic-normalized scalar Schur equation
  E3 predecessor-block symmetry / shifted coercivity / positive resolvent
  E4 parity nullity / resonance-resolvent dichotomy

THEN
  classify or rule out simultaneous even/odd first-bad resonance
  combine shell, cubic defect, KKT and shifted-resolvent constraints
  attack the admissible first-bad state itself

PARALLEL
  source-faithful G1-B1B -> G1-final -> S-NEG -> G23

RH                                                                 OPEN
~~~

## What #112 and #113 changed

PR #112 promoted the first-bad problem from a selected-parity local minimum to a **global** least-bad finite state. At that same state both predecessor parity sectors are nonnegative. It internalized the centered predecessor and the one-step shell inside the exact successor parity carrier, proved the intrinsic shell has complex dimension one, and theoremized an exact cubic defect functional

~~~text
F_N(v) = ell_N(v) • g_N.
~~~

The generator is nonzero for `N>=2`; the scalar functional is **not** proved nonzero, so this is not an exact-rank-one claim.

PR #113 then proves that the intrinsic predecessor and shell are complementary and exposes canonical projections. For the genuine first-bad negative eigenmode, the canonical shell coordinate is nonzero. With

~~~text
A = P_W T|_W,
B = P_W T|_S,
lam < 0,
~~~

predecessor nonnegativity implies `A-lam I` is bijective, and Lean proves

~~~text
(A-lam I) w = -B s,
w = -(A-lam I)^(-1) B s,
<Ts,s> - lam <s,s> - <(A-lam I)^(-1)Bs, Bs> = 0.
~~~

Thus a hypothetical off-line zero is no longer merely a finite negative direction: it forces one finite global-first-bad problem carrying a canonical one-dimensional N-flow shell, an exact one-dimensional cubic parity-defect factorization, and a scalar shifted Schur equation simultaneously.

## Post-#113 research implications

**DERIVED / open formalization:**
- the projected predecessor block `A` should be symmetric because the full compressed operator is symmetric and the shell is orthogonal to the predecessor;
- for `lam<0`, the shifted block should satisfy the quantitative coercivity estimate `Re <(A-lam I)w,w> >= (-lam)||w||^2`, leading to positivity and a resolvent bound;
- codimension-one predecessor nonnegativity plus the proved negative successor mode strongly suggests negative index exactly one / a unique negative eigenline;
- after normalizing by the nonzero shell norm, the Schur identity should become a scale-free one-dimensional secular equation.

**LEAD / HYPOTHESIS — current highest-value composition:** prove the cubic channel has nonzero intrinsic shell part. Because #113 proves

~~~text
intrinsicShellPart x = 0  <->  x ∈ intrinsic predecessor W,
~~~

the hard-looking projection comparison reduces to a smaller non-membership theorem. For the odd channel, show `g_(N+1)` is not a centered predecessor extension; for the even channel, pull `g` back through the algebraic D-equivalence and prove the analogous non-membership without treating D as unitary.

A promising explicit calculation to theoremize or falsify is

~~~text
g_K = d^3 - alpha_K d,
alpha_K = <d,d^3>/<d,d> = (3 K^2 + 3 K - 1)/5,
outer coefficient at +K = K(K-1)(2K-1)/5.
~~~

For `K>=2` that outer coefficient is nonzero, which would exclude membership in the centered predecessor image if the exact repository projection normalization yields this formula. This calculation is a **LEAD / HYPOTHESIS**, not a promoted theorem.

If cubic-shell incidence is proved, the cubic shell coordinate and the first-bad eigenmode shell coordinate are two nonzero vectors in a one-dimensional space, hence scalar multiples. Because the #113 Schur identity is homogeneous of degree two in the shell vector, this should permit a canonical cubic-normalized scalar first-bad equation. That is the first direct composition of the two one-dimensional bottlenecks.

## Permanent firewalls

- `V = W ⊕ S` is now proved, but shell invariance under the compressed operator is not.
- `v ∉ W` / nonzero shell coordinate does not make the eigenmode a pure-shell vector.
- D-equivalence is algebraic, not unitary or isometric.
- exact factorization through `g_N` does not prove `ell_N != 0` or exact rank one.
- `g_N != 0` does not prove the parity defect operator is nonzero.
- algebraic same-space conjugation does not automatically preserve self-adjointness in the original inner product.
- no equal-spectrum, Hermitian interlacing or inertia transfer through D is proved.
- use `A-lam I` for `lam<0`; never assume `A^-1` at zero for the semidefinite predecessor block.
- negative index exactly one, resolvent monotonicity, cubic-shell incidence, simultaneous-resonance exclusion, positivity, finite-to-infinite closure and RH remain OPEN unless separately theorem-backed.
- generic R002 taper-grid and Bombieri zero-height truncations remain distinct from the canonical deterministic CCM finite family except where exact specialization/bridge theorems say otherwise.
- the legacy printed `finiteMatrix` differs from the canonical source matrix by a scalar identity; absolute PSD/inertia claims must use the canonical source normalization.

## Living research records

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS.md`
- `research/RHRC/RESEARCH_LEADS_POST_113_DELTA.md`
- `research/RHRC/OBSTRUCTION_LEDGER.md`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/CLAIM_REGISTRY.json`
- `research/RHRC/R003_PROMOTED_BINDINGS.json`

The theorem/CI surface through #113 is authoritative. Machine claim/binding promotion must not be inferred beyond the entries actually present in the registries; this documentation sync does not silently convert research leads into promoted claims.

**RH remains OPEN.**
