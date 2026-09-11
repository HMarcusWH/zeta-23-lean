# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

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

Live GitHub head + exact Lean/compiler/CI remain authoritative.

## Current theorem ladder

```text
off-line zeta zero
  -> legal finite canonical negative obstruction                     PROVED
  -> global first bad + predecessor parity nonnegativity             PROVED
  -> shell/KKT/Schur/secular machinery                              PROVED
  -> source-explicit transfer                                       PROVED / #129
  -> exact canonical source-moment decomposition                    PROVED / #131
  -> denominator-free zero-shift kernel/source transport            PROVED / #134
  -> scalar-sensitive absolute canonical source energy              PROVED / #136
  -> exact source pairing + one-step determinant                    PROVED / #137
  -> off-line zero => q_c<0 OR exists w, Delta(w)<0                 PROVED / #137
  -> every sufficiently large aperture has a finite negative
     canonical witness and a freshly selectable global first bad    PROVED / #140
  -> predecessor determinant !=0 <-> injective, with unique
     zero-shift preimage on a regular predecessor                   PROVED / #140
  -> actual canonical source is continuous on each fixed physical
     cutoff cell; same finite witness persists on an open set       PROVED / #142
  -> exact frozen production source/predecessor, -log(L) split,
     complex frozen remainder and log-cover/deck identities         PROVED / #144
  -> removable scalar factor/remainder locally analytic at zero     PROVED / #145
  -> removable scalar factor/remainder equal the production complex
     scalar/remainder away from zero and on the positive real axis  PROVED / #146
  -> connected arch strip, strip-wide regularized arch scale,
     alpha/beta/gamma fixed-unit parameter holomorphy               PROVED / #148
```

No theorem proves assembled frozen source/predecessor holomorphy, lifted determinant nonidentity, dense fixed-cell regularity, production cell-minimal regular first-bad selection, the regular first-bad arithmetic sign, negative-root exclusion, or RH.

## What #148 changed

PR #148 closes the previous fixed-unit parameter-integral obstruction. It proves the common archimedean safe strip

```text
complexArchSafeStrip = { z : C | |Im z| < pi }
```

is open/convex/connected, proves the divided sinh denominator is zero-free there, proves `complexRegularizedArchScale` analytic throughout the strip, and proves `complexAlphaCore`, `complexBetaCore`, and `complexGammaCore` analytic throughout the strip.

The proof is genuine differentiation under a fixed `[0,1]` integral with local compact domination. It does not infer holomorphy from the #144 deck law.

## Active path

```text
PROVED through #148
  eventual aperture freedom
  + fixed-cell same-witness persistence
  + exact frozen/log-cover predecessor scaffold
  + scalar removable layer + production bridge
  + fixed-unit alpha/beta/gamma parameter holomorphy

NOW
  common-domain production source holomorphy
  -> assembled complex frozen source/predecessor holomorphy
  -> lifted predecessor holomorphy on a connected cover domain

THEN
  determinant nonidentity via deck-shift / finite characteristic-polynomial argument
  -> dense fixed-cell regularity
  -> intersect with #142 persistent-negative open set
  -> production cell-minimal regular first-bad countercertificate

DECISIVE OPEN THEOREM
  Ecanonical(c-x0) >= 0 on the exact forced regular trial

TARGET
  contradiction -> no off-line strip zero -> explicit outside-strip/trivial-zero seam -> Mathlib RH wrapper
```

Universal one-step domination remains a broad fallback if a genuinely independent positive canonical arithmetic mechanism is found.

## Why assembly is the next real gate

The #148 theorem package closes only the archimedean fixed-unit cores. The exact frozen production source also contains a scalar principal-log branch, pole denominators, and finite prime/source terms. Those channels must be placed on one common punctured complex domain and assembled through the exact finite matrix/projection interfaces before the lifted determinant can be treated as an analytic function.

A high-value lead is the identity

```text
Re(z*coth(z/2))
  = (x*sinh(x) + y*sin(y)) / (cosh(x) - cos(y)),  z=x+iy.
```

On `|y|<pi`, this suggests the production scalar factor has positive real part away from zero, which would give a clean principal-log branch on the same strip. This is a **LEAD / HYPOTHESIS**, not yet a theorem.

## Determinant nonidentity is separate from holomorphy

The exact #144 deck law remains

```text
Ahat(z+2*pi*i) = Ahat(z) - (2*pi*i) I.
```

Once the lifted family is analytic on a connected domain, determinant nonidentity should be attacked algebraically: if the determinant vanished identically, one fixed finite operator would support too many distinct scalar shifts as eigenvalues. A finite characteristic-polynomial root count is the intended mechanism.

The zero-dimensional predecessor case must be split off directly.

## Post-#142 cell-minimal compression

For a physical cutoff cell `I_Q=(log Q,log(Q+1))`, define the least size that is bad somewhere in the entire cell. Then every smaller size is good in both parities throughout the cell. This quantifier order is essential: minimizing at a single aperture and then moving the aperture would lose the predecessor nonnegativity conclusion.

If dense predecessor regularity is proved, it only has to hit the #142 open persistent-negative neighborhood at the single predecessor size `N*=K*-1`.

This remains **DERIVED**, not yet production-packaged in Lean.

## After regularity — decisive arithmetic obstruction

At a regular cell-minimal first-bad state:

```text
A>=0                    from cell-wide minimality
A injective             from regularity
A>0                     finite Hermitian consequence
unique x0 with A x0=b   from #140
u0=c-x0.
```

Existing machinery is intended to package

```text
Ecanonical(u0)=Re S0<0.
```

The decisive missing arithmetic theorem is

```text
Ecanonical(c-x0)>=0.
```

A potentially narrower certificate than universal domination is `q_c>=0` plus `Delta(x0)>=0`, but only after theoremizing that the zero-shift coupling is real and handling the `q_A(x0)=0` edge case.

## Permanent firewalls

- RH remains OPEN.
- theorem authority is through #148, not beyond it.
- fixed-unit archimedean parameter holomorphy is PROVED; assembled source/predecessor holomorphy is OPEN.
- translation/deck identities are not a substitute for holomorphy.
- holomorphy does not imply determinant nonidentity.
- determinant nonidentity/dense regularity does not imply the final arithmetic sign.
- cell-minimal regularization is DERIVED until production-packaged.
- regularity is not successor positivity.
- no factorwise division by unproved transfer/source quantities.
- D remains algebraic, not unitary/isometric.
- generic or modified-source countermodels do not refute the actual canonical source.
- external exact checks and numerical experiments are not theorem authority.
- machine claim promotion remains separate from compiler theorem validity.
- the terminal Mathlib RH wrapper still requires explicit outside-strip/trivial-zero bookkeeping.

## Living research records

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS_POST_148_PARAMETER_HOLOMORPHY_GREEN_DELTA.md` — newest research-priority delta
- `research/RHRC/RESEARCH_LEADS_POST_146_APERTURE_ANALYTIC_FRONTIER_DELTA.md` — historical pre-#148 delta
- `research/RHRC/countermodels/POST_146_TRANSLATION_NOT_HOLOMORPHY_COUNTERMODEL_2026_09_11.md`
- `research/RHRC/countermodels/POST_142_REGULARIZATION_COUNTERMODEL_2026_09_10.md`
- `research/RHRC/OBSTRUCTION_LEDGER.md`
- `research/RHRC/DEAD_ROUTES.md`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/control_v2/README.md`

**RH remains OPEN.**
