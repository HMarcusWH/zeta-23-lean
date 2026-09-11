# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

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
```

No theorem proves genuine aperture-parameter holomorphy of the assembled frozen source/predecessor remainder, determinant nonidentity, dense regularity, the regular first-bad arithmetic sign, negative-root exclusion, or RH.

## What changed in #144-#146

The old post-#142 plan treated "construct the complex frozen predecessor / isolate the logarithm" as one open block. That block has now split cleanly.

**PROVED / #144:** the actual frozen production source and intrinsic predecessor exist with exact fixed-cell agreement; the `-log L` scalar survives the exact production projections; the complex frozen remainder and logarithmic-cover lift are theorem-locked; and exact deck-periodicity/deck-shift identities hold.

**PROVED / #145:** the corrected scalar factor/remainder has a removable analytic extension at zero.

**PROVED / #146:** that removable scalar layer is exactly the existing production complex scalar/remainder away from zero and exactly matches the positive-real production formula.

**OPEN:** the non-scalar fixed-unit parameter integrals have not yet been proved holomorphic in the aperture parameter. Therefore the full assembled frozen source/predecessor holomorphy theorem is still open.

## Active path

```text
PROVED through #146
  eventual aperture freedom
  + fixed-cell same-witness persistence
  + exact frozen/log-cover predecessor scaffold
  + local scalar removable analyticity
  + scalar <-> production bridge

NOW
  genuine parameter holomorphy of the exact fixed-unit production source integrals
  -> assembled complex frozen source/predecessor holomorphy

THEN
  determinant nonidentity
  -> dense fixed-cell regularity
  -> intersect with #142 persistent-negative open set
  -> production cell-minimal regular first-bad countercertificate

DECISIVE OPEN THEOREM
  Ecanonical(c-x0) >= 0 on the exact forced regular trial

TARGET
  contradiction -> no off-line zero -> explicit Mathlib RH wrapper
```

Universal one-step domination remains a broad fallback if a genuinely independent positive canonical arithmetic mechanism is found.

## Why holomorphy is the next real gate

The #144 log-cover law is structural:

```text
Ahat(z) = -z I + R(exp z)
R(exp(z+2*pi*i)) = R(exp z).
```

But translation/deck identities do not imply complex differentiability. The reusable negative control

```text
F(z) = -z + Re z
```

has the same kind of affine deck-shift behavior under imaginary translation while remaining nonholomorphic.

So the next theorem must come from genuine complex analysis of the parameter-dependent integrals — most likely local denominator control plus differentiation under a fixed-domain integral — not from the deck law itself.

## Post-#142 cell-minimal compression

The preferred regularization problem remains smaller than the older finite-prefix plan.

For a physical cutoff cell `I_Q=(log Q,log(Q+1))`, define the least size that is bad somewhere in the entire cell. Then every smaller size is good in both parities throughout the cell. If dense predecessor regularity is later proved, it only has to hit the #142 open persistent-negative neighborhood at the single predecessor size `N*=K*-1`.

This is **DERIVED**, not yet production-packaged in Lean.

## After regularity — decisive arithmetic obstruction

At a regular cell-minimal first-bad state:

```text
A>=0                    from minimality
A injective             from regularity
A>0                     finite Hermitian consequence
unique x0 with A x0=b   from #140
u0=c-x0.
```

Existing machinery is intended to package the forced negative certificate

```text
Ecanonical(u0)=Re S0<0.
```

The decisive missing arithmetic theorem is still

```text
Ecanonical(c-x0)>=0
```

or equivalently after regularity `<b,A^-1b> <= q_c`.

A proof that merely repackages successor positivity or universal one-step domination is circular.

## Permanent firewalls

- RH remains OPEN.
- theorem authority is through #146, not beyond it.
- complex/log-cover structure is PROVED; assembled parameter holomorphy is OPEN.
- local scalar analyticity is not full source/predecessor analyticity.
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

## Living research records

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS_POST_146_APERTURE_ANALYTIC_FRONTIER_DELTA.md` — newest research-priority delta
- `research/RHRC/RESEARCH_LEADS_POST_142_FIXED_CELL_PERSISTENCE_DELTA.md` — historical pre-#144 delta
- `research/RHRC/countermodels/POST_146_TRANSLATION_NOT_HOLOMORPHY_COUNTERMODEL_2026_09_11.md`
- `research/RHRC/countermodels/POST_142_REGULARIZATION_COUNTERMODEL_2026_09_10.md`
- `research/RHRC/OBSTRUCTION_LEDGER.md`
- `research/RHRC/DEAD_ROUTES.md`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/control_v2/README.md`

**RH remains OPEN.**
