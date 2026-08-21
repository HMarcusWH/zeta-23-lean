# R003 — CCM / finite Guinand–Weil / zero-side bridge

Status: **DISCOVERY**. RH remains open.

This README is the **active route SSOT** after PR #33's Connes/CvS/Groskin normalization audit. The pre-literature transform-first roadmap has been preserved verbatim in `PRE_GROSKIN_ROADMAP_2026_08_21.md` for historical context and fallback lemmas, but it is **not** the active implementation order.

## Current theorem boundary

The finite fork-owned CCM object is theorem-authoritative in `Zeta23.CCM`.

Compiler-checked Lean facts already include:

- the formal finite CCM matrix `Zeta23.CCM.finiteMatrix L N`;
- the exact source wrapper `finiteMatrixOfLambda lam N` with `L = 2 * log lam`;
- continuity, compact support, integrability and real-valuedness of the CCM kernel for `0 < L`;
- exact finite index displacement

```text
(n-m) M_nm = g_n - g_m
[D,M] = g 1^T - 1 g^T
rank([D,M]) <= 2.
```

The displacement theorem is retained as a structural theorem. After comparison with the divided-difference literature, low displacement rank is treated as a **generic Loewner/divided-difference chassis property**, not as RH-specific evidence.

The following claims remain open:

```text
R003_CCM_RHS_IDENTITY
R003_KERNEL_EF_EXTENSION
R003_CCM_BRIDGE
R003_WEIL_DISPLACEMENT
C_RH
```

No finite numerical/source audit promotes any of these claims.

## Post-paper normalization lock

PR #33 pins an independent cutoff-free Connes–van Suijlekom / Connes–Consani–Moscovici implementation from the Groskin finite Guinand–Weil verification package under

```text
research/RHRC/external/connes_cvs/
```

and keeps it outside the Lean theorem dependency graph.

The reference audit separates three conventions:

```text
M        fork-owned formal CCM matrix
Q_inf    cutoff-free CvS/CCM Galerkin matrix in Groskin's dictionary
WeilGram inherited explicit-formula normalization used by the earlier R003 diagnostics
```

Across the frozen audit grid, the independent source formulas identify

```text
Q_inf = M + 2*cCorrection(L)*I
```

with primitive map

```text
alpha_reference = alpha_ours
beta_reference  = beta_ours
gamma_reference = gamma_ours - cCorrection(L)
pole_reference  = pole_ours.
```

Combined with PR #29's earlier finite diagnostic

```text
WeilGram = 2*M + 4*cCorrection(L)*I,
```

the current **normalization target** is

```text
WeilGram = 2*Q_inf.
```

This is a target for Lean formalization, not a promoted theorem.

### Audit artifacts

- `CCM_NORMALIZATION_LOCK_v1.json` — curated, reviewed provenance/route lock. It is not generated automatically.
- `compare_ccm_normalizations.py` — reproducible falsification/normalization audit.
- `CCM_NORMALIZATION_AUDIT_latest.json` — generated local detailed audit artifact; not theorem authority and not required to be committed.
- `NORMALIZATION_AUDIT_2026_08_21.md` — human-readable convention analysis and reproduction instructions.

The audit script deliberately refuses to overwrite the curated lock.

## Active mathematical architecture

The route is now split into four finite obligations before any finite-to-infinite campaign:

```text
formal CCM matrix / generic divided-difference source calculus
        |
        v
finite Guinand–Weil dictionary objects
        |
        v
explicit-formula admissibility adapter
        |
        v
exact zeta zero-side / CCM matrix identity
```

Only after that finite bridge is theorem-closed do we build the spectral/entire-function machinery needed to decide which finite-to-infinite route is genuinely attackable.

## Active implementation sequence

### PR #33 — reference transplant + normalization audit

**MERGED** at `adad73d06cc539a09e527f935a669e0c60fdb362`. Reference/audit only; no mathematical claim promoted.

Delivered:

- pinned external provenance and MIT license;
- cutoff-free CCM reference oracle;
- fail-closed normalization audit;
- curated normalization lock;
- CI firewall preventing external Python from entering the Lean theorem graph;
- post-Groskin route SSOT correction.

The exact-head RHRC, normalization audit, Lean CCM/ExceptionalZero builds, and placeholder gate were green before merge.

### PR #34 — generic divided-difference / source calculus

**CURRENT PR. Formal structural theorem work; no RHRC claim promotion.**

Create:

```text
Zeta23/CCM/DividedDifference.lean
Zeta23/CCM/SourceMatrix.lean
```

The generic entry deliberately separates source values from diagonal data:

```text
Q_psi,d(n,m) = d(n)                         if n = m
             = (psi(n)-psi(m))/(n-m)        if n != m.
```

This avoids importing differentiability into the algebraic chassis. A later analytic specialization may set `d(n)=psi'(n)`, but the displacement theorem does not require that identification.

Prove exactly:

```text
(n-m) Q_psi,d(n,m) = psi(n)-psi(m)
[D,Q_psi,d] = psi 1^T - 1 psi^T
rank([D,Q_psi,d]) <= 2
[D,Q_psi,d1] = [D,Q_psi,d2].
```

Then specialize the elementary source atom

```text
psi_omega(n) = sin(2*pi*n*omega)/pi
d_omega(n)   = 2*omega*cos(2*pi*n*omega)
```

and prove the exact convention bridge

```text
sourceEntry(1-y/L,n,m) = qBasis(n,m,y,L).
```

Finally identify the fork-owned CCM scalar entry with the generic class using the existing zeta-specific channel lemmas, and derive the public finite displacement/rank theorems through the generic matrix theorem.

Purpose: formally separate the universal divided-difference chassis from zeta-specific information and give PR #35 a sign-locked source API.

Detailed PR theorem boundary: `PR34_GENERIC_SOURCE_CALCULUS.md`.

### PR #35 — finite Guinand–Weil dictionary objects

Create approximately:

```text
Zeta23/CCM/FiniteDictionary.lean
```

Formalize the exact finite chain

```text
v -> symmetric coefficients u
  -> T_v
  -> K_v
  -> ghat_v
  -> g_v
```

and prove the finite source-contraction identity before invoking the zeta explicit formula.

The pinned Groskin implementation is an external oracle only; Lean owns the theorem.

### PR #36 — explicit-formula admissibility seam

Run two bounded proof spikes and keep only the smaller production route:

1. broaden the inherited explicit-formula interface to the admissibility class used by the finite dictionary; or
2. use the existing explicit `C^2` smoothing/mollifier adapter downstream of `EF_lit`.

The old transform-decay, interface-jump and mollifier analysis in `PRE_GROSKIN_ROADMAP_2026_08_21.md` remains valid fallback material for this PR, but no longer dictates the ordering.

### PR #37 — exact finite zero-side / CCM bridge

Prove the formal finite Guinand–Weil identity and reconcile it with the fork-owned CCM normalization locked by PR #33.

Define `zeroSideEntry` / `zeroSideMatrix` (not `Gram` before positivity is proved) and close the registered finite bridge claims only if their exact Lean statements are discharged.

Expected convention target:

```text
zero-side / inherited Weil matrix = 2*Q_inf
Q_inf = M + 2*cCorrection(L)*I
```

The audit cannot be cited as proof; the convention map must be established in Lean.

### PR #38 — exact finite source quotient + information-loss API

Formalize the `2N+1`-dimensional source quotient through the coordinates

```text
int omega dmu
int sin(2*pi*k*omega) dmu
int omega*cos(2*pi*k*omega) dmu, 1 <= k <= N.
```

Purpose: make explicit exactly what finite CCM compression can and cannot see, and use this as an information-loss gate for later RH routes.

### PR #39 — prime-cutoff / von Mangoldt matrix flow

Formalize the cutoff path in `u = log c` and the prime-power event law

```text
Delta Q'_N = -2*Lambda(q)/(sqrt(q)*log(q)) * 11^T.
```

Keep this initially to exact finite event, sign and rank statements. Do not promote stronger string/resolvent interpretations without their missing hypotheses.

### PR #40 — parity + extremal spectral API

Formalize reversal symmetry, even/odd block decomposition and a precise reduction of the CCM even-simple gate. Integrate the cutoff-flow consequence that prime-event rank-one shocks live in the even sector.

This does not by itself prove the global ground state is simple and even.

### PR #41 — finite characteristic / XiHat API

Formalize the pole-cancelled entire function built from a finite extremal eigenvector, including removable singularities, node interpolation and parity.

Bind it to the finite self-adjoint/real-spectrum construction only as far as the literature theorem and Lean dependencies justify.

### PR #42 — barycentric eigenvector equation

Derive, rather than assume, the exact arithmetic interpolation identity obtained by combining the CCM eigenvector equation with the divided-difference law.

The previously proposed formula is schematic until Lean derives its exact signs and scales.

After #42, **freeze implementation and run a route-selection gate** before committing to another theorem sequence.

## Post-#42 route-selection gate

Candidate campaigns include:

- fixed-`L`, `N -> infinity` Galerkin convergence;
- aperture `L -> infinity` after fixed-aperture control;
- an R002-style finite off-line obstruction using exact zero-side finite operators;
- a Suzuki-style localized self-adjoint / compact-uniform convergence route as an independent control architecture.

Every proposed route must identify:

1. the exact missing theorem;
2. why it is weaker than RH rather than RH rewritten;
3. which already-formal finite structure attacks it;
4. a cheap falsifier/negative control;
5. the smallest theorem that would materially advance the route.

## Preserved fallback analysis

The former README has been archived verbatim as

```text
PRE_GROSKIN_ROADMAP_2026_08_21.md
```

It contains the detailed pre-paper analysis of:

- derivative jumps at `-L, 0, +L`;
- two transform-decay proof spikes;
- prime and pole channel specializations;
- the archimedean scalar-shift calculation;
- explicit `C^2` mollification and channel-specific limits;
- closed-form transform diagnostics;
- the older #33–#36 transform-first implementation sequence.

Those calculations remain useful as lemmas or fallback proof routes. The archived PR numbering and ordering are **superseded** and must not be treated as active authorization.

## Naming and authority discipline

Before RH, do not call the unconditional zero-side finite matrix a `Gram` matrix merely because it resembles one: off-line zeros make the transformed ordinates complex and positivity has not been established.

Authority hierarchy:

```text
Lean / comparator theorem checks   mathematical authority
RHRC receipts                       provenance / governance
external connes-cvs Python          oracle / falsifier only
finite numerics                     diagnostic only
```

Nothing promotes itself.

## Immediate next step

Finish **PR #34: generic divided-difference/source calculus** under exact-head CI. Once it is merged, begin **PR #35: finite Guinand–Weil dictionary objects and the finite source-contraction identity**. Do not restart the superseded transform-first sequence.
