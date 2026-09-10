# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

```text
live main after merged PR #142 = 3e8d2995a1c00a9aef0d8cb0f5382658c91a8673
live main tree = a92d03d0d4ad800d544a835b8ae2e3d23bae2c47

theorem-state anchor = PR #142 merge 3e8d2995a1c00a9aef0d8cb0f5382658c91a8673
validated theorem head = 23d96af9aafd86ad26ae7913c3d6c14503d539de
validated theorem tree = a92d03d0d4ad800d544a835b8ae2e3d23bae2c47
RHRC #889 = SUCCESS
Permansson #662 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact Lean compiler + CI are authority. Control v2 may select research actions but may not promote theorem or terminal RH status.

## Theorem-backed route

```text
finite off-line-zero obstruction / legal approximation                 PROVED
canonical finite negative obstruction                                  PROVED / #94
constrained algebra / Euclidean sector                                  PROVED / #96-#98
exact centered N-flow + parity / first-bad / one-dimensional shell      PROVED / #100-#112
exact shifted/zero-shift Schur and secular package                      PROVED / #113-#128
source-explicit cross-parity transfer                                   PROVED / #129
exact canonical source-moment decomposition                             PROVED / #131
denominator-free zero-shift source transport                            PROVED / #134
absolute canonical source-energy decomposition                          PROVED / #136
exact canonical source pairing + one-step determinant                   PROVED / #137
off-line zero -> q_c<0 OR exists w, Delta(w)<0                         PROVED / #137
aperture freedom at every sufficiently large L                          PROVED / #140
fresh global-first-bad selection at every sufficiently large L          PROVED / #140
actual predecessor det!=0 <-> injective + unique preimage               PROVED / #140
frozen prime-cell equality + threshold atom zero + scalar -log(L) split PROVED / #140
actual canonical source entry continuity on one physical cutoff cell     PROVED / #142
fixed-vector canonical quadratic-energy continuity on one cutoff cell    PROVED / #142
same-size/same-vector strict negative witness persistence in-cell         PROVED / #142
off-line-zero -> locally persistent fixed witness beyond threshold        PROVED / #142

analytic frozen predecessor + determinant nonidentity                    OPEN / NOW
dense regular aperture in each physical cell                             OPEN / NOW
production cell-minimal regular selection                                OPEN / NEXT
regular minimizing-trial Schur-energy sign                               OPEN / DECISIVE ARITHMETIC GAP
universal canonical one-step domination                                  OPEN / BROAD FALLBACK
negative-root exclusion                                                   OPEN
explicit terminal RH bridge                                               OPEN
RH                                                                        OPEN
```

## Post-#142 research reroute

#142 closes the fixed-witness continuity/persistence obligation on the actual production `canonicalSourceMatrix`.

A stronger **DERIVED** selection now minimizes bad size over the entire physical cutoff cell before regularizing:

```text
K* = min { K | exists L in (log Q,log(Q+1)), AnyParityBad L K }.
```

Then every `K<K*` is good in both parities at **every** aperture in that cell. At predecessor size `N*=K*-1`, predecessor nonnegativity therefore holds throughout the cell.

Choose a bad parity witness at size `K*`. PR #142 keeps that exact vector negative on an open subinterval `J`. If the relevant predecessor determinant is nonzero on a dense set, one can choose a regular aperture inside `J`. At that point the predecessor is PSD by cell-minimality and injective by regularity, hence positive definite in finite Hermitian dimension.

This is smaller than the post-#140 finite-prefix plan. The primary route no longer requires either countable all-size Baire regularization or simultaneous regularization of every size through a finite witness horizon.

The production cell-minimum composition is not yet a merged theorem. A standalone abstract conditional selection theorem has been locally Lean-checked, but it assumes density and has no canonical theorem authority.

## Current execution priority

1. **Production cell-minimum wrapper.** Package the cell-wide least-bad construction on the actual `AnyParityBad` definitions without assuming pointwise least-bad persistence.
2. **Complexify the #142 regularized production primitives.** Keep exact real-axis agreement with the actual source and choose one explicit common punctured domain.
3. **Build the frozen intrinsic predecessor family.** Prove equality with the actual `intrinsicPredecessorBlock` on the physical cell and isolate the scalar term `-Log(L) I`.
4. **Prove determinant nonidentity.** Use a single-valued holomorphic remainder plus logarithmic monodromy and finite-dimensional characteristic-polynomial/eigenvalue counting.
5. **Derive dense fixed-cell regularity.** Use analytic isolated-zero/identity machinery on the actual determinant.
6. **Compose with #142 persistence.** Intersect the persistent-negative open set with dense regularity and package a regular cell-minimal first-bad certificate.
7. **Expose the regular minimizing-trial deficit.** Use the #140 unique-preimage interface `A x0=b` and #136/#137 energy/Schur machinery to obtain `Ecanonical(c-x0)=Re S0<0` on the exact selected state.
8. **Attack the decisive arithmetic sign.** Prove, from exact pole/arch/scalar/prime structure, `Ecanonical(c-x0)>=0` on that state.
9. **Compose to contradiction and the terminal Mathlib RH wrapper.**

Universal A4b2b domination remains a broad fallback if a genuinely independent positive source representation or exact arithmetic remainder appears.

## Analytic lead after #142

The #142 proof has already regularized the apparent archimedean origin singularities using divided slopes and `Real.sinc`.

After the real change of variables `x=L t`, the integration domain is fixed at `[0,1]` and the oscillatory frequency is independent of aperture. The resulting fixed-unit-interval formulas are **DERIVED**, not merged Lean declarations.

This makes a direct complex-analytic route newly attractive. Existing `DictionaryArchPhysical.lean`, `DictionaryArchBridge.lean` and `GammaFacts/Mu.lean` remain useful fallback and cross-check infrastructure rather than mandatory first dependencies.

The candidate determinant mechanism is:

```text
A(L) = -Log(L) I + B(L)
B single-valued holomorphic on a connected punctured domain
L = exp z
Ahat(z) = -z I + B(exp z)
B(exp(z+2*pi*i)) = B(exp z)
```

If `det Ahat` vanished identically, one fixed finite matrix would be forced to admit too many distinct eigenvalues differing by `2*pi*i`. This is a **LEAD / HYPOTHESIS** until the exact production continuation and domain are theoremized.

## Post-#142 falsification constraint

A generic analytic centered diagonal family can have all of:

```text
an explicit -log L scalar term;
positive predecessors for every L>0;
persistent finite negative witnesses at every aperture;
a globally minimal bad size;
common negative behavior in both parity sectors.
```

Therefore aperture freedom, persistence, minimality, regularity, parity and scalar logarithmic structure do not by themselves supply the RH contradiction. The actual canonical pole/archimedean/von-Mangoldt arithmetic must do new work.

See `countermodels/POST_142_REGULARIZATION_COUNTERMODEL_2026_09_10.md`.

Regularity also kills the predecessor kernel, so the #134 product law `Gamma0*mu(z)=0` does not become a sign theorem in the regular state.

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
- theorem authority is through #142 only.
- fixed-cell continuity and same-witness persistence are PROVED; analyticity and dense regularity are OPEN.
- cell-minimal regular selection is DERIVED until production-packaged.
- regularity is not positivity of the successor.
- regular Schur-energy nonnegativity is OPEN.
- all-size Baire and finite-prefix regularization are fallbacks, not current dependencies.
- universal domination is not a research reduction if its proof merely restates successor PSD.
- external exact checks and numerical experiments are not theorem authority.
- no inverse is load-bearing before regularity; prefer the unique-preimage theorem.
- no factorwise division by `alpha`, `Gamma`, overlap or source moment without theoremized nonzeroness.
- D is algebraic, not unitary/isometric.
- machine claim promotion remains separate.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and gates.
- `RESEARCH_LEADS_POST_142_FIXED_CELL_PERSISTENCE_DELTA.md` — newest research delta.
- `RESEARCH_LEADS_POST_140_APERTURE_FREEDOM_DELTA.md` — historical pre-#142 delta.
- `RESEARCH_LEADS_POST_138_ASTRA_DELTA.md` — historical pre-#140 reroute.
- `countermodels/POST_142_REGULARIZATION_COUNTERMODEL_2026_09_10.md` — generic post-#142 regularization negative control.
- `OBSTRUCTION_LEDGER.md` — reusable blockers.
- `DEAD_ROUTES.md` — quarantined routes.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — executable research routing.

**RH remains OPEN.**