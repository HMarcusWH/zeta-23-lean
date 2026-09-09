# RHRC formal audit — theorem authority through PR #140; fixed-cell A4R frontier

> **RH remains OPEN.**

## Current authority split

```text
live main after merged PR #140 = fa96196b5bd6ed754853b0bdacee1dbd2356022f
live main tree = 2015404927540ae79a64469af82813463694b71d

theorem-state anchor = PR #140 merge fa96196b5bd6ed754853b0bdacee1dbd2356022f
validated theorem head = 77b52cfc73dfd83d2a0ed4373befba97d77e48e5
validated theorem tree = 2015404927540ae79a64469af82813463694b71d
RHRC #882 = SUCCESS
Permansson #655 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact compiler/CI evidence outrank this prose.

## Exact theorem-state progression

### PR #134 — zero-shift source transport

**PROVED:** denominator-free whole-kernel source transport, direct zero-shift cross-parity transfer, exact zero-shift `Gamma` overlap formula, and `Gamma0*mu(z)=0` under both preimage hypotheses.

### PR #136 — absolute canonical source energy

**PROVED:** scalar-sensitive `matrixRealEnergy`, identity-shift sensitivity, exact prime/arch/scalar source-energy decomposition, cubic-shell energy, regular zero-shift trial energy `= Re S0`, and negative explicit Schur root -> negative canonical trial energy.

### PR #137 — canonical one-step determinant reduction

**PROVED:** exact complex source pairing, predecessor energy, shell coupling and

```text
Delta(w)=q_c*q_A(w)-|<w,b>|^2.
```

Also PROVED: conditional domination sufficiency, kernel/range zero-shift consequences, `Re S0>=0` under domination plus predecessor nonnegativity, no safe negative explicit root under domination, exact domination-failure disjunction, and the global off-line-zero sign-failure countercertificate.

### PR #140 — aperture freedom and regularity scaffold

**PROVED:**

```text
off-line zero
  -> exists L0>0
  -> for every L>L0, a finite boundary-flat canonical negative witness exists.
```

Also PROVED:

```text
every sufficiently large L -> some AnyParityBad(L,N)
every sufficiently large L -> freshly selectable least global-first-bad Nstar
```

and the exact regularity/frozen-source interfaces:

```text
IntrinsicPredecessorRegular <-> injective intrinsicPredecessorBlock
regular predecessor -> unique preimage of every target
regular predecessor -> unique cubic zero-shift preimage
floor(exp L)=Q -> frozenCanonicalPrimeMatrix Q L K = canonicalPrimeMatrix L K
L=log q -> entering source atom matrix is exactly zero
-2*wCorrection(L) = -log(L) + canonicalApertureScalarRemainder(L), L>0.
```

No theorem proves the analytic determinant-nonidentity step, dense regular apertures, the final regular Schur sign, negative-root exclusion, or RH.

## Post-#140 research correction

The most important structural change is not a new positivity statement. It is the aperture quantifier.

Because an off-line zero now forces fresh finite negativity at every sufficiently large aperture, A4R no longer has to move one old finite witness through an unknown global regularity problem.

The preferred reduction is:

```text
choose one large frozen cutoff cell
-> invoke #140 inside the cell
-> learn a finite witness size N
-> preserve that one strict negative value locally
-> regularize only finitely many predecessor blocks up to N in both parities
-> reselect global first-bad.
```

This makes countable all-size Baire avoidance unnecessary for the primary route.

## Active A4R1 theorem

Choose `Q` large and work strictly inside

```text
log Q < L < log(Q+1).
```

The prime cutoff is constant on the cell. The next proof obligations are:

```text
1. continuity of fixed finite canonical energy in L on the cell;
2. analytic/holomorphic representation of the actual projected predecessor;
3. determinant nonidentity for each fixed parity/size;
4. dense regularity for each fixed block;
5. finite simultaneous avoidance through a prescribed M;
6. compose with #140 negativity and fresh first-bad reselection.
```

The #140 real-axis `-log(L)` scalar coefficient is already theorem-backed. The unresolved analytic part is the full production predecessor remainder, especially the archimedean channel.

The old dictionary/gamma bridge is therefore resurrected as a likely analytic input rather than rebuilding the continuation from raw interval integrals.

## Candidate determinant nonidentity argument

The proposed log-cover representation is

```text
Ahat(z) = -z I + Rhat(z)
Rhat(z+2*pi*i)=Rhat(z).
```

If `det Ahat` vanished identically, periodicity would force one fixed `d x d` matrix to have `d+1` distinct eigenvalues differing by `2*pi*i`, impossible.

This is a **LEAD / HYPOTHESIS** until the exact production continuation is theoremized. The invalid shortcut `A(exp z)=-zI+periodic` without a genuine log-cover continuation remains forbidden.

## Smallest remaining obstruction after successful A4R1

At the reselected first-bad state:

```text
A>=0                    from first-bad minimality
A injective             from A4R1
unique x0 with A x0=b   from #140 regularity scaffold
u0=c-x0.
```

The intended forced countercertificate is

```text
Ecanonical(u0)=Re S0<0.
```

The decisive arithmetic target remains

```text
Ecanonical(c-x0)>=0
```

on the exact forced regular first-bad trial, equivalently `<b,A^-1b><=q_c` once inverse shorthand is justified.

This is substantial new mathematics and cannot be obtained by assuming successor PSD under another name.

## Preserved derived/falsification state

- **DERIVED:** under predecessor PSD and one-dimensional shell, universal `q_c>=0` plus `Delta(w)>=0` is equivalent to successor positivity.
- **DERIVED:** `Delta(P_kerA b)=-||P_kerA b||^4`.
- **DERIVED / external exact-check:** `d=-(6/(2*N-1))a` for the two correction vectors.
- **DERIVED / external symbolic:** negative leading source-atom determinant coefficient rules out atomwise positive determinant/SOS as a default route.
- **EXPERIMENTAL SIGNAL:** canonical Schur endpoints can arise from extreme prime/arch/scalar cancellation.
- **EXPERIMENTAL SIGNAL:** tiny modified prime-weight perturbations can flip successor sign while predecessors stay positive.

These are not canonical RH counterexamples and are not theorem authority.

## Current execution order

```text
1. fixed-cell finite regularization: continuity + analytic predecessor + determinant nonidentity
2. finite simultaneous regular-aperture selection through a prescribed horizon
3. compose with #140 aperture freedom and fresh first-bad reselection
4. package one regular first-bad source countercertificate
5. interval/symbolic analysis of the full minimizing-trial Schur remainder
6. derive an independent exact prime/arch/scalar remainder or inequality
7. formalize regular canonical Schur-energy nonnegativity
8. compose with forced Re S0<0
9. explicit Mathlib RiemannHypothesis wrapper
```

Universal `q_c/Delta` domination remains a broad fallback if an independently positive canonical source mechanism is discovered.

## Permanent firewalls

- compiler/CI validity is authoritative; repository presence alone is not;
- theorem authority is through #140 and no further;
- aperture freedom is PROVED, dense regular-aperture selection is OPEN;
- regularity is not positivity;
- all-size Baire regularization is not required unless finite-cell selection fails for a theoremized reason;
- universal determinant positivity cannot count as a reduction if it merely restates successor PSD;
- no `A^-1` at zero before regularity; formal code should prefer the unique-preimage interface;
- D is algebraic, not unitary/isometric;
- no division by unproved transfer/source factors;
- modified-source or generic countermodels are not zeta counterexamples;
- numerical precision is not theorem authority;
- machine claim promotion remains separate;
- RH remains OPEN.

Newest research implications: `research/RHRC/RESEARCH_LEADS_POST_140_APERTURE_FREEDOM_DELTA.md`.

**RH remains OPEN.**