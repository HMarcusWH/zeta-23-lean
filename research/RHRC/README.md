# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

```text
live main after merged PR #146 = f2999d12e29d61debce130e83491ac3df410b0c2
live main tree = fe76581d445569cb838cb4df7bf50703aa34f5cc

theorem-state anchor = PR #146 merge f2999d12e29d61debce130e83491ac3df410b0c2
validated theorem head = a25d238478f7b19072c5364486b8f3f994bf6b79
validated theorem tree = fe76581d445569cb838cb4df7bf50703aa34f5cc
RHRC #922 / run 34600323163 = SUCCESS
Permansson #695 / run 34600323144 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact Lean compiler + CI are authority. Control v2 may select research actions but may not promote theorem or terminal RH status.

## Theorem-backed route

```text
finite off-line-zero obstruction / legal approximation                 PROVED
canonical finite negative obstruction                                  PROVED / #94
centered N-flow / parity / first-bad / shell / Schur package            PROVED / #100-#128
source-explicit cross-parity transfer                                   PROVED / #129
exact canonical source-moment decomposition                             PROVED / #131
denominator-free zero-shift source transport                            PROVED / #134
absolute canonical source-energy decomposition                          PROVED / #136
exact canonical source pairing + one-step determinant                   PROVED / #137
off-line zero -> q_c<0 OR exists w, Delta(w)<0                         PROVED / #137
aperture freedom at every sufficiently large L                          PROVED / #140
predecessor det!=0 <-> injective + unique preimage                      PROVED / #140
fixed-cell actual-source continuity + fixed-witness persistence          PROVED / #142
exact frozen production source/predecessor + -log(L) split              PROVED / #144
complex frozen remainder + log-cover/deck identities                    PROVED / #144
local removable scalar analyticity at zero                              PROVED / #145
removable scalar/remainder <-> production complex scalar/remainder       PROVED / #146

parameter holomorphy of fixed-unit production source integrals           OPEN / NOW
assembled frozen source/predecessor holomorphy                           OPEN / NOW
determinant nonidentity + dense regular aperture                         OPEN / NEXT
production cell-minimal regular selection                                OPEN / NEXT
regular minimizing-trial Schur-energy sign                               OPEN / DECISIVE ARITHMETIC GAP
universal canonical one-step domination                                  OPEN / BROAD FALLBACK
negative-root exclusion                                                   OPEN
explicit terminal RH bridge                                               OPEN
RH                                                                        OPEN
```

## What #144-#146 changed

The old A4R1b first break was too coarse. The exact production/log-cover object now exists.

PR #144 proves the frozen source agrees with production on a physical cutoff cell, proves the exact `-log(L) * I + remainder` decomposition through the actual parity and intrinsic-predecessor projections, constructs the complex frozen remainder, lifts it to `L=exp z`, proves exact deck-periodicity/deck-shift identities, and recovers the actual production predecessor at `z=log L`.

PR #145 repairs the scalar removable point and proves local analyticity of that scalar layer at zero.

PR #146 proves the repaired scalar factor and remainder are exactly the production complex scalar/remainder on `z!=0` and exactly match the positive-real production formulas.

What remains open is not "construct the complex predecessor". The first genuine analytic gap is now:

```text
fixed-unit parameter-dependent production integrals
  -> genuine complex differentiability / analyticity
  -> assembled complexFrozenCanonicalSourceRemainder holomorphy
  -> assembled complexFrozenIntrinsicPredecessorRemainder holomorphy.
```

## Current execution priority

1. **Prototype parameter holomorphy on the simplest fixed-unit core.** Prefer `complexBetaCore`; prove local denominator control, pointwise parameter differentiability and an integrable local majorant that licenses differentiation under the integral.
2. **Reuse the proof pattern for the remaining production cores.** Close `complexAlphaCore` and `complexGammaCore` without changing Eq. (4.4) normalization.
3. **Assemble source/predecessor holomorphy.** Push the core analytic theorems through the exact #144 complex frozen source and intrinsic predecessor definitions.
4. **Prove determinant nonidentity.** Only after genuine holomorphy is available may the logarithmic-cover finite-spectrum argument become load-bearing.
5. **Derive dense fixed-cell regularity.** Use analytic isolated-zero/identity machinery on the actual determinant.
6. **Compose with #142 persistence.** Intersect the persistent-negative open set with dense regularity and package a regular cell-minimal first-bad certificate.
7. **Expose the regular minimizing-trial deficit.** Use the #140 unique-preimage interface `A x0=b` and #136/#137 energy/Schur machinery to obtain `Ecanonical(c-x0)=Re S0<0` on the exact selected state.
8. **Attack the decisive arithmetic sign.** Prove, from exact pole/arch/scalar/prime structure, `Ecanonical(c-x0)>=0` on that state.
9. **Compose to contradiction and the terminal Mathlib RH wrapper.**

Universal A4b2b domination remains a broad fallback if a genuinely independent positive source representation or exact arithmetic remainder appears.

## Cell-minimal route compression

The post-#142 derived selection remains the preferred composition:

```text
K* = min { K | exists L in (log Q,log(Q+1)), AnyParityBad L K }.
```

Every `K<K*` is then good in both parities at every aperture in that cell. At predecessor size `N*=K*-1`, predecessor nonnegativity holds throughout the cell. #142 preserves one exact bad witness on an open `J`. Once dense regularity is proved, select a regular aperture inside `J`.

This remains **DERIVED** until production-packaged.

## Analytic negative control

The #144 deck law is exact, but it is not an analyticity theorem. The generic function

```text
F(z) = -z + Re z
```

satisfies an affine imaginary-translation law of the same structural kind while being nonholomorphic. Therefore no proof may infer parameter holomorphy from deck-periodicity/translation identities alone.

See `countermodels/POST_146_TRANSLATION_NOT_HOLOMORPHY_COUNTERMODEL_2026_09_11.md`.

The earlier post-#142 analytic regularization negative control remains active: persistence, minimality, regularity, parity and a scalar logarithm can all coexist with a negative finite state in a generic model.

## Candidate determinant mechanism after holomorphy

Once genuine holomorphy is theoremized, the exact #144 architecture becomes useful:

```text
Ahat(z) = -z I + R(exp z)
R(exp(z+2*pi*i)) = R(exp z).
```

If the determinant were identically zero, a finite-dimensional spectral/root-counting argument may force one fixed finite operator to support too many distinct scalar shifts. This remains a **LEAD / HYPOTHESIS** until the determinant theorem is actually proved.

## Decisive arithmetic target

At a selected regular cell-minimal first-bad state:

```text
A>=0                    from minimality
A injective             from regularity
A>0                     finite Hermitian consequence
unique x0 with A x0=b   from #140
u0=c-x0.
```

The intended forced countercertificate is

```text
Ecanonical(u0)=Re S0<0.
```

The decisive missing theorem is

```text
Ecanonical(c-x0)>=0
```

or, once inverse shorthand is legal,

```text
<b,A^-1b> <= q_c.
```

A proof that merely assumes or repackages successor positivity is circular.

## Permanent firewalls

- RH remains OPEN.
- theorem authority is through #146 only.
- exact complex/log-cover objects are PROVED; full parameter holomorphy is OPEN.
- local scalar analyticity is not assembled source/predecessor analyticity.
- translation/deck structure is not holomorphy.
- holomorphy is not determinant nonidentity.
- cell-minimal regular selection is DERIVED until production-packaged.
- regularity is not positivity of the successor.
- regular Schur-energy nonnegativity is OPEN.
- all-size Baire and finite-prefix regularization are fallbacks, not current dependencies.
- universal domination is not a research reduction if its proof merely restates successor PSD.
- no inverse is load-bearing before regularity; prefer the unique-preimage theorem.
- no factorwise division by `alpha`, `Gamma`, overlap or source moment without theoremized nonzeroness.
- D is algebraic, not unitary/isometric.
- machine claim promotion remains separate.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and gates.
- `RESEARCH_LEADS_POST_146_APERTURE_ANALYTIC_FRONTIER_DELTA.md` — newest research delta.
- `RESEARCH_LEADS_POST_142_FIXED_CELL_PERSISTENCE_DELTA.md` — historical pre-#144 delta.
- `countermodels/POST_146_TRANSLATION_NOT_HOLOMORPHY_COUNTERMODEL_2026_09_11.md` — holomorphy inference negative control.
- `countermodels/POST_142_REGULARIZATION_COUNTERMODEL_2026_09_10.md` — generic regularization negative control.
- `OBSTRUCTION_LEDGER.md` — reusable blockers.
- `DEAD_ROUTES.md` — quarantined routes.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — executable research routing.

**RH remains OPEN.**
