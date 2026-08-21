# R003 — CCM / finite Guinand–Weil / zero-side bridge

Status: **DISCOVERY**. RH remains open.

This README is the **active route SSOT** after the Connes/CvS/Groskin normalization audit, the generic divided-difference refactor, and the first theorem-authoritative finite dictionary slice. The pre-literature transform-first roadmap is preserved in `PRE_GROSKIN_ROADMAP_2026_08_21.md` for historical context and fallback lemmas, but it is **not** the active implementation order.

## Current theorem boundary

The finite fork-owned CCM/source machinery is theorem-authoritative in `Zeta23.CCM`.

Compiler-checked Lean facts already include:

- the formal finite CCM matrix `Zeta23.CCM.finiteMatrix L N`;
- the exact source wrapper `finiteMatrixOfLambda lam N` with `L = 2 * log lam`;
- continuity, compact support, integrability and real-valuedness of the original CCM kernel for `0 < L`;
- the generic divided-difference matrix class with independent diagonal data;
- exact generic displacement `D Q - Q D = psi 1^T - 1 psi^T` and rank at most two;
- exact diagonal-independence of divided-difference displacement;
- the elementary single-frequency source matrix;
- the exact convention bridge `sourceEntry (1-y/L,n,m) = qBasis(n,m,y,L)`;
- the concrete CCM identification as a generic divided-difference matrix;
- the full-grid finite source contraction

```text
K_u(omega) = <u, sourceMatrix(omega) u>;
```

- the exact quadratic source/CCM bridge

```text
K_u(1-y/L)
  = sum_{i,j} conj(u_i) qBasis(i,j,y,L) u_j;
```

- the compact physical dictionary test

```text
k_{u,L}(y) = 1/2 K_u(1-|y|/L)  for |y| <= L,
           = 0                   otherwise;
```

- the canonical dictionary transform `g_{u,L}(z) = Zeta23.paperFT(k_{u,L})(z)`;
- exact finite index displacement

```text
(n-m) M_nm = g_n - g_m
[D,M] = g 1^T - 1 g^T
rank([D,M]) <= 2.
```

The displacement theorem is a structural theorem. Low displacement rank is a **generic Loewner/divided-difference chassis property**, not RH-specific evidence.

The following claims remain open:

```text
R003_CCM_RHS_IDENTITY
R003_KERNEL_EF_EXTENSION
R003_CCM_BRIDGE
R003_WEIL_DISPLACEMENT
C_RH
```

No numerical/source audit promotes any of these claims.

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
WeilGram inherited explicit-formula normalization used by the earlier R003 diagnostic
```

Across the frozen audit grid, the independent source formulas identify

```text
Q_inf = M + 2*cCorrection(L)*I
```

and the older PR #29 diagnostic used

```text
WeilGram = 2*M + 4*cCorrection(L)*I = 2*Q_inf.
```

**Do not import that factor two into the new dictionary theorem by name.** The current dictionary test contains an explicit factor `1/2`, so the exact relation between `literatureRHS(k_{u,L})` and the finite matrix must be proved channel by channel in Lean. The normalization lock remains a source/formula target and falsifier, not theorem authority.

## Active mathematical architecture

```text
formal CCM / generic source calculus
        |
        v
finite dictionary core                     [#35 merged]
        |
        v
finite dictionary closure                  [#36 current]
        |
        v
analytic control + EF admissibility         [#37]
        |
        v
deterministic explicit-formula RHS         [#38]
        |
        v
exact zero-side finite matrix bridge        [#39]
```

Only after the finite bridge is theorem-closed do we return to information-loss, arithmetic cutoff flow, finite spectral machinery, and then a finite-to-infinite route-selection gate.

## Active implementation sequence

### PR #33 — reference transplant + normalization audit

**MERGED** at `adad73d06cc539a09e527f935a669e0c60fdb362`. Reference/audit only; no mathematical claim promoted.

### PR #34 — generic divided-difference / source calculus

**MERGED** at `756d074c325a555de2afb1ef8306c4dc0bb793e2`. No RHRC claim promoted.

Delivered exact generic divided-difference displacement/rank, diagonal-independence, the elementary source atom, the exact sign/parameter bridge

```text
sourceEntry(1-y/L,n,m) = qBasis(n,m,y,L),
```

and the concrete CCM matrix factored through the generic class.

### PR #35 — finite Guinand–Weil dictionary core

**MERGED** at `0f35cf61b6d5787a387caa613444f72a1f8c7d30` from exact green head `43aaf26beedfa471e95c82ac39e0da9fb06fd11e`. No RHRC claim promoted.

Delivered:

```text
sourceContract / K_u
K_u(0) = 0
K_u(1-y/L) = quadratic qBasis contraction
dictionaryTest k_{u,L}
dictionaryTransform = Zeta23.paperFT(k_{u,L})
```

and a hardened external finite-dictionary oracle with fail-closed domain, precision, complex-transform and non-finite regression guards.

The Volterra/trigonometric representation is now **nonblocking explanatory equivalence**: prove it later only if it remains cheap or becomes useful for analysis. It is not a prerequisite for the finite bridge.

### PR #36 — finite dictionary closure

**CURRENT PR. Formal finite algebra/topology only; no explicit formula and no RHRC claim promotion.**

Primary goals:

```text
reusable quadraticForm convention
sourceMatrix(1) = 2I
K_u(1) = 2 * coefficientMass(u)
k_{u,L}(0) = coefficientMass(u)
k_{u,L}(+/-L) = 0
k_{u,L}(-y) = k_{u,L}(y)
support(k_{u,L}) subset [-L,L]
HasCompactSupport(k_{u,L})
Continuous(k_{u,L}) for L > 0
```

The preferred continuity proof uses the clamped coordinate

```text
omega_L(y) = max(0, 1-|y|/L)
```

and the already-proved endpoint identity `K_u(0)=0`, avoiding a brittle direct proof across the piecewise aperture boundary.

Do **not** claim global `C^1` or `C^2` here. The raw dictionary test is expected to have derivative seams and the next PR must diagnose them explicitly.

The paper even-sector embedding `v -> u` is optional/nonblocking in this PR; do not let finite-index bureaucracy delay the full-grid bridge.

### PR #37 — dictionary analytic control + explicit-formula admissibility

First formalize the seam rather than trying to prove false smoothness. For generic `u`, derive the endpoint/source derivative behavior and show why the folded compact test is generally continuous but not globally `C^1`.

Then prove the transform decay required by the zero sum, preferably from the smooth half-interval representation:

```text
|g_{u,L}(z)| <= C/(1+|Re z|^2)  on |Im z| <= 1/2.
```

Run two bounded proof spikes:

1. **preferred:** derive an adapter from the existing `EF_lit` by approximating this finite dictionary family with `C_c^2` tests and proving convergence of pole, prime, archimedean and zero-side channels;
2. **escape hatch:** formalize the exact broader literature admissibility theorem used by the finite dictionary, with explicit citation/assumptions and no claim that it follows from the current `EF_lit` definition.

Kill the mollifier route if it starts requiring a broad general analysis library rather than a finite-family adapter.

### PR #38 — deterministic explicit-formula RHS / normalization theorem

**No zeros in this PR.** Feed `k_{u,L}` into `Zeta23.EF.literatureRHS` and prove the result channel by channel.

Targets:

```text
pole RHS  = quadratic pole channel
prime RHS = - quadratic primeComponent
arch RHS  = - quadratic archComponent + diagonal correction
```

The prime normalization has a built-in acceptance check:

```text
k(log n) + k(-log n) = 2*k(log n)
k(log n) = 1/2 * <u, qBasis(log n,L) u>
```

so the two factors must cancel exactly.

Define a neutral theorem object such as

```text
dictionaryMatrix(L,N) := M(L,N) + 2*cCorrection(L)*I
```

only as a definition. The theorem

```text
literatureRHS(k_{u,L}) = <u, dictionaryMatrix(L,N) u>
```

is what identifies it with the finite Guinand–Weil/CvS operator. Do not force a factor two from the old `WeilGram` diagnostic.

If discharged, this is the natural point to promote `R003_CCM_RHS_IDENTITY` at the exact statement proved.

### PR #39 — exact zero-side finite matrix bridge + polarization

Apply the #37 admissibility result to the #38 deterministic identity:

```text
sum_rho m_rho * dictionaryTransform(u,L,gamma_rho)
  = <u, dictionaryMatrix(L,N) u>.
```

Use **real polarization** for the real symmetric finite matrices unless complex polarization becomes necessary:

```text
A_ij = (Q(e_i+e_j) - Q(e_i) - Q(e_j))/2.
```

Define `zeroSideMatrix`, not `Gram`, before positivity is proved. Then recover the full matrix identity and transfer the scalar-diagonal-invariant displacement theorem.

Only here consider promotion of:

```text
R003_KERNEL_EF_EXTENSION
R003_CCM_BRIDGE
R003_WEIL_DISPLACEMENT
```

and only if the exact registered Lean statements are discharged.

### PR #40 — exact finite source quotient + information-loss API

Formalize the `2N+1`-dimensional source quotient through

```text
int omega dmu
int sin(2*pi*k*omega) dmu
int omega*cos(2*pi*k*omega) dmu, 1 <= k <= N.
```

This theorem records exactly what fixed finite CCM data cannot see.

### PR #41 — prime-cutoff / von Mangoldt matrix flow

Formalize at prime-power cutoff events

```text
Delta Q'_N = -2*Lambda(q)/(sqrt(q)*log(q)) * 11^T.
```

Initial claims are exact finite event/sign/rank/parity statements only. This arithmetic event structure is distinct from the generic static rank-two displacement chassis.

### PR #42 — parity + extremal spectral API

Formalize reversal symmetry, even/odd block decomposition and the precise finite reduction of the CCM even-simple gate. Do not globally assert that the even ground state always wins.

### PR #43 — finite characteristic / XiHat API

Formalize the pole-cancelled entire function built from a finite extremal eigenvector, including removable singularities, node interpolation and parity.

### PR #44 — barycentric eigenvector equation

Derive the exact arithmetic interpolation identity from the CCM eigenvector equation and divided-difference law. Any pre-existing formula remains schematic until Lean fixes all signs and scales.

After #44, freeze implementation and run a route-selection gate before committing to another theorem sequence.

## Post-#44 finite-to-infinite route-selection gate

Candidate campaigns:

1. fixed-`L`, `N -> infinity` Galerkin/operator convergence;
2. aperture `L -> infinity` and normalized finite characteristic-function convergence toward `Xi`;
3. an R002-style finite off-line obstruction/signature failure;
4. a Suzuki/de Branges localized self-adjoint control route.

Every proposed route must identify:

1. the exact missing theorem;
2. why it is weaker than RH rather than RH rewritten;
3. which already-formal finite structure attacks it;
4. a cheap falsifier/negative control;
5. the smallest theorem that would materially advance the route.

## Standing dumbassery gates

- Green CI is not explicit-formula admissibility.
- Do not prove or assume false global smoothness for the folded raw dictionary test.
- Do not restrict to `sum u_i = 0` merely to erase a derivative seam; that discards a finite direction and is not the full bridge.
- Do not make the Volterra/Groskin representation load-bearing unless a later proof actually needs it.
- Do not call the unconditional zero-side object a `Gram` matrix before positivity.
- Do not turn the definition `M + 2*cCorrection*I` into a literature identification without the RHS theorem.
- Use real polarization when real symmetric quadratic forms suffice.
- External Python remains an oracle/falsifier, never theorem authority.
- After the finite bridge, do not smuggle finite-to-infinite convergence through the word “therefore.” That limit theorem is likely where the hard mathematics lives.

## Naming and authority discipline

Authority hierarchy:

```text
Lean / comparator theorem checks   mathematical authority
RHRC receipts                       provenance / governance
external connes-cvs Python          oracle / falsifier only
finite numerics                     diagnostic only
```

Nothing promotes itself.

## Immediate next step

Finish **PR #36** at the finite/topological boundary: endpoint identities, reusable quadratic-form convention, evenness, compact support and continuity. Then open #37 specifically for analytic seam/decay/admissibility work. Do not invoke `EF_lit` in #36.
