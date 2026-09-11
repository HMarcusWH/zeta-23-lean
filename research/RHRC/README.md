# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

```text
live main after merged PR #148 = fcd301ae4c1b58196ff7fca18128243f1d35a87b
live main tree = 91d537ee64b8f613bebdcf12110deba486276d35

theorem-state anchor = PR #148 merge fcd301ae4c1b58196ff7fca18128243f1d35a87b
validated theorem head = 77c2d14511004ba380b080e08b4943b267ebd863
validated theorem tree = 91d537ee64b8f613bebdcf12110deba486276d35
RHRC #930 / run 34619665717 = SUCCESS
Permansson #703 / run 34619665725 = SUCCESS

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
predecessor det!=0 <-> injectivity + unique preimage                    PROVED / #140
fixed-cell actual-source continuity + fixed-witness persistence          PROVED / #142
exact frozen production source/predecessor + -log(L) split              PROVED / #144
complex frozen remainder + log-cover/deck identities                    PROVED / #144
local removable scalar analyticity at zero                              PROVED / #145
removable scalar/remainder <-> production complex scalar/remainder       PROVED / #146
connected arch strip + alpha/beta/gamma parameter holomorphy            PROVED / #148

assembled frozen source/predecessor holomorphy                           OPEN / NOW
lifted determinant analyticity + nonidentity + dense regularity          OPEN / NEXT
production cell-minimal regular selection                                OPEN / NEXT
regular minimizing-trial Schur-energy sign                               OPEN / DECISIVE ARITHMETIC GAP
universal canonical one-step domination                                  OPEN / BROAD FALLBACK
negative-root exclusion                                                   OPEN
outside-strip/trivial-zero seam + terminal RH bridge                      OPEN
RH                                                                        OPEN
```

## What #148 changed

PR #148 closes the previous fixed-unit parameter-integral first break. It proves genuine complex analyticity of `complexAlphaCore`, `complexBetaCore`, and `complexGammaCore` throughout the connected archimedean safe strip `|Im z|<pi`, with strip-wide analyticity of `complexRegularizedArchScale` and zero-freeness of the divided sinh denominator.

The next genuine analytic gap is not another alpha/beta/gamma derivative. It is common-domain assembly of the full production source:

```text
scalar principal-log branch
+ pole denominator
+ finite prime/source channel
+ #148 arch cores
-> complexFrozenCanonicalSourceRemainder holomorphy
-> complexFrozenIntrinsicPredecessorRemainder holomorphy
-> lifted predecessor holomorphy on a connected cover domain.
```

## Current execution priority

1. **Attack the scalar common-domain branch first.** Try to prove `Re(z*coth(z/2))>0` on the punctured strip `|Im z|<pi`.
2. **Close the remaining source channels.** Prove pole-denominator zero-freeness and finite prime/source analyticity on the same domain.
3. **Assemble source/predecessor holomorphy.** Push those theorems through the exact #144 finite matrices and intrinsic projections.
4. **Lift to a connected logarithmic-cover domain.** Do not infer connectedness from deck invariance; prove it explicitly.
5. **Prove determinant nonidentity.** Use the exact deck shift plus a finite characteristic-polynomial root count, with the zero-dimensional predecessor case split off.
6. **Derive dense fixed-cell regularity.** Use one-variable analytic identity/isolated-zero machinery.
7. **Compose with #142 persistence.** Intersect the persistent-negative open set with dense regularity and package a regular cell-minimal first-bad certificate.
8. **Expose the regular minimizing-trial deficit.** Use the unique preimage `A x0=b` and existing energy/Schur machinery to obtain `Ecanonical(c-x0)=Re S0<0` on the exact selected state.
9. **Attack the decisive arithmetic sign.** Prove `Ecanonical(c-x0)>=0` from exact pole/arch/scalar/prime structure.
10. **Compose to contradiction, then close the outside-strip/trivial-zero seam and the Mathlib RH wrapper.**

Universal A4b2b domination remains a broad fallback if a genuinely independent positive source representation or exact arithmetic remainder appears.

## Cell-minimal route compression

The post-#142 derived selection remains the preferred composition:

```text
K* = min { K | exists L in (log Q,log(Q+1)), AnyParityBad L K }.
```

Every `K<K*` is then good in both parities at every aperture in that cell. At predecessor size `N*=K*-1`, predecessor nonnegativity therefore holds throughout the cell. #142 preserves one exact bad witness on an open `J`. Once dense regularity is proved, select a regular aperture inside `J`.

This remains **DERIVED** until production-packaged.

## Analytic negative control

The #144 deck law is exact, but it is not an analyticity theorem. The generic function

```text
F(z) = -z + Re z
```

satisfies an affine imaginary-translation law of the same structural kind while being nonholomorphic. No proof may infer parameter holomorphy from deck-periodicity/translation identities alone.

## Candidate determinant mechanism

Once assembled lifted holomorphy is theoremized, use

```text
Ahat(z+2*pi*i)=Ahat(z)-(2*pi*i)I.
```

If the determinant were identically zero, the same finite operator at a base point would be forced to admit too many distinct scalar shifts as eigenvalues. A characteristic-polynomial root count should establish nonidentity. This remains a **LEAD / HYPOTHESIS** until Lean proves it.

## Decisive arithmetic target

At a selected regular cell-minimal first-bad state:

```text
A>=0
A injective
A>0
unique x0 with A x0=b
u0=c-x0.
```

The intended forced countercertificate is

```text
Ecanonical(u0)=Re S0<0.
```

The decisive missing theorem is

```text
Ecanonical(c-x0)>=0.
```

A narrower possible certificate is `q_c>=0` plus `Delta(x0)>=0`, but only after the zero-shift coupling is proved real and the `q_A(x0)=0` case is handled. This is not yet theorem-backed.

## Permanent firewalls

- RH remains OPEN.
- theorem authority is through #148 only.
- fixed-unit archimedean core holomorphy is PROVED; assembled source/predecessor holomorphy is OPEN.
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
- strip-zero exclusion is not yet the full Mathlib `RiemannHypothesis` wrapper without the outside-strip/trivial-zero seam.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and gates.
- `RESEARCH_LEADS_POST_148_PARAMETER_HOLOMORPHY_GREEN_DELTA.md` — newest research delta.
- `RESEARCH_LEADS_POST_146_APERTURE_ANALYTIC_FRONTIER_DELTA.md` — historical pre-#148 delta.
- `countermodels/POST_146_TRANSLATION_NOT_HOLOMORPHY_COUNTERMODEL_2026_09_11.md` — holomorphy inference negative control.
- `countermodels/POST_142_REGULARIZATION_COUNTERMODEL_2026_09_10.md` — generic regularization negative control.
- `OBSTRUCTION_LEDGER.md` — reusable blockers.
- `DEAD_ROUTES.md` — quarantined routes.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — executable research routing.

**RH remains OPEN.**
