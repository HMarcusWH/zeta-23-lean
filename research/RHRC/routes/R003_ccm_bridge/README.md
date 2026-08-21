# R003 — CCM / finite Guinand–Weil / zero-side bridge

Status: **DISCOVERY**. RH remains open.

This README is the **active route SSOT** after the Connes/CvS/Groskin normalization audit and the generic divided-difference refactor. The pre-literature transform-first roadmap is preserved in `PRE_GROSKIN_ROADMAP_2026_08_21.md` for historical context and fallback lemmas, but it is **not** the active implementation order.

## Current theorem boundary

The finite fork-owned CCM object is theorem-authoritative in `Zeta23.CCM`.

Compiler-checked Lean facts already include:

- the formal finite CCM matrix `Zeta23.CCM.finiteMatrix L N`;
- the exact source wrapper `finiteMatrixOfLambda lam N` with `L = 2 * log lam`;
- continuity, compact support, integrability and real-valuedness of the CCM kernel for `0 < L`;
- the generic divided-difference matrix class with independent diagonal data;
- exact generic displacement `D Q - Q D = psi 1^T - 1 psi^T` and rank at most two;
- exact diagonal-independence of divided-difference displacement;
- the elementary single-frequency source matrix;
- the exact convention bridge `sourceEntry (1-y/L,n,m) = qBasis(n,m,y,L)`;
- the concrete CCM identification as a generic divided-difference matrix;
- exact finite index displacement

```text
(n-m) M_nm = g_n - g_m
[D,M] = g 1^T - 1 g^T
rank([D,M]) <= 2.
```

The displacement theorem is retained as a structural theorem. PR #34 makes the interpretation precise: low displacement rank is a **generic Loewner/divided-difference chassis property**, not RH-specific evidence.

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

and, combined with PR #29's earlier finite diagnostic

```text
WeilGram = 2*M + 4*cCorrection(L)*I,
```

the current formalization target is

```text
WeilGram = 2*Q_inf.
```

This remains a target for Lean formalization, not a promoted theorem.

## Active mathematical architecture

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

### PR #34 — generic divided-difference / source calculus

**MERGED** at `756d074c325a555de2afb1ef8306c4dc0bb793e2`. No RHRC claim promoted.

Delivered exact generic divided-difference displacement/rank, diagonal-independence, the elementary source atom, the exact sign/parameter bridge

```text
sourceEntry(1-y/L,n,m) = qBasis(n,m,y,L),
```

and the concrete CCM matrix factored through the generic class. Exact-head run `32529011638` was green after the final documentation polish.

Detailed theorem boundary: `PR34_GENERIC_SOURCE_CALCULUS.md`.

### PR #35 — finite Guinand–Weil dictionary objects

**CURRENT PR. READY FOR REVIEW. Formal finite-dictionary work; no RHRC claim promotion.**

Primary Lean module:

```text
Zeta23/CCM/FiniteDictionary.lean
```

Preferred architecture:

```text
paper even-sector vector v
  -> symmetric centered coefficients u
  -> source contraction K_u(omega) = <u, sourceMatrix(omega) u>
  -> compact physical-space test k_{u,L}(y)
  -> g_{u,L}(z) = Zeta23.paperFT(k_{u,L})(z)
```

Then prove equivalence with the Groskin representation

```text
u -> T_v -> Volterra K_v -> ghat_v -> g_v.
```

`paperFT` is defined in the root `Zeta23` namespace (`Zeta23.paperFT`); `EF_lit` and `literatureRHS` live under `Zeta23.EF`. The root `paperFT` definition is canonical internally. The physically preserved `finite_dictionary_reference.py` is an external oracle/falsifier only and must remain outside the Lean dependency graph.

The first implementation slice defines the full-grid source contraction, proves its zero-frequency vanishing, lifts PR #34's convention bridge to quadratic contractions, defines the compact physical-space dictionary test, and defines the canonical `Zeta23.paperFT` dictionary transform. The even-sector embedding, endpoint normalization, support/continuity, Volterra equivalence, and Groskin Fourier-convention bridge remain to be proved inside this PR.

The first Codex review found four P2 issues confined to the external Python oracle: narrow-strip complex values were projected to the real axis, import mutated global `mpmath` precision, the constructor admitted `c <= 1`, and coefficient-band mismatches were not rejected. All four are fixed, guarded in `check_finite_dictionary_reference.py`, replied to, and resolved. These changes harden the oracle only; they do not alter the finite dictionary theorem statements or promote any mathematical claim.

### PR #36 — explicit-formula admissibility seam

Run two bounded proof spikes and keep only the smaller production route:

1. broaden the inherited explicit-formula interface to the admissibility class used by the finite dictionary; or
2. use the existing explicit `C^2` smoothing/mollifier adapter downstream of `EF_lit`.

### PR #37 — exact finite zero-side / CCM bridge

Prove the formal finite Guinand–Weil identity and reconcile it with the fork-owned CCM normalization locked by PR #33. Define `zeroSideEntry` / `zeroSideMatrix` (not `Gram` before positivity is proved) and promote registered bridge claims only if their exact Lean statements are discharged.

Expected convention target:

```text
zero-side / inherited Weil matrix = 2*Q_inf
Q_inf = M + 2*cCorrection(L)*I
```

### PR #38 — exact finite source quotient + information-loss API

Formalize the `2N+1`-dimensional source quotient through

```text
int omega dmu
int sin(2*pi*k*omega) dmu
int omega*cos(2*pi*k*omega) dmu, 1 <= k <= N.
```

### PR #39 — prime-cutoff / von Mangoldt matrix flow

Formalize

```text
Delta Q'_N = -2*Lambda(q)/(sqrt(q)*log(q)) * 11^T
```

at prime-power events, initially only as exact finite event/sign/rank statements.

### PR #40 — parity + extremal spectral API

Formalize reversal symmetry, even/odd block decomposition and the precise finite reduction of the CCM even-simple gate.

### PR #41 — finite characteristic / XiHat API

Formalize the pole-cancelled entire function built from a finite extremal eigenvector, including removable singularities, node interpolation and parity.

### PR #42 — barycentric eigenvector equation

Derive the exact arithmetic interpolation identity from the CCM eigenvector equation and divided-difference law. Any previously written formula remains schematic until Lean fixes all signs and scales.

After #42, freeze implementation and run a route-selection gate before committing to another theorem sequence.

## Post-#42 route-selection gate

Candidate campaigns include fixed-`L` Galerkin convergence, aperture convergence, an R002-style finite off-line obstruction, and a Suzuki-style localized self-adjoint control route.

Every proposed route must identify:

1. the exact missing theorem;
2. why it is weaker than RH rather than RH rewritten;
3. which already-formal finite structure attacks it;
4. a cheap falsifier/negative control;
5. the smallest theorem that would materially advance the route.

## Preserved fallback analysis

`PRE_GROSKIN_ROADMAP_2026_08_21.md` preserves derivative-jump calculations, transform-decay proof spikes, prime/pole specializations, the archimedean scalar-shift calculation, explicit `C^2` mollification and channel-specific limits, closed-form transform diagnostics, and the superseded transform-first implementation sequence.

Those calculations remain useful as lemmas or fallback proof routes. Their old PR numbering and ordering are superseded.

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

Continue **PR #35** in this order: full-grid source contraction and canonical test (started), reversal-even `v -> u` embedding, endpoint normalization, compact-support/continuity proofs, Volterra/trigonometric representation, then the `ghat`/`Zeta23.paperFT` convention bridge. Do not invoke `EF_lit` until PR #36.
