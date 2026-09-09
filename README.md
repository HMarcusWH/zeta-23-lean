# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

```text
live main after merged PR #138 = ebf289bdfdde69020bee0d1571047f155e5de4db
live main tree = d26cd83709437260d0a16630d90c73a93f64c975

theorem-state anchor = PR #137 merge fa2f209a6eb8b4059968e8d61239d80588ca256c
validated theorem head = 64988e142590c82bd0ad43604279ede9a8e85eff
validated theorem tree = e3de4dc0377f0124832822b6f97ab5bbd7718640
RHRC #878 = SUCCESS
Permansson #651 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact Lean/compiler/CI remain authoritative. PR #138 is documentation/control synchronization; theorem authority remains #137.

## Current theorem ladder

```text
off-line zeta zero
  -> legal finite canonical negative obstruction                     PROVED
  -> global first bad + both predecessor parities nonnegative        PROVED
  -> exact shell/KKT/Schur/secular machinery                         PROVED
  -> source-explicit transfer                                        PROVED / #129
  -> exact canonical source-moment decomposition                     PROVED / #131
  -> denominator-free zero-shift kernel/source transport             PROVED / #134
  -> scalar-sensitive absolute canonical source energy               PROVED / #136
  -> exact source pairing + one-step determinant                     PROVED / #137
  -> domination => regularity + Re S0>=0 + no safe negative root     PROVED / #137 CONDITIONAL
  -> off-line zero => q_c<0 OR exists w, Delta(w)<0                  PROVED / #137
```

No theorem proves `canonicalOneStepDomination`, unconditional negative-root exclusion, or RH.

## Post-#138 research correction

An independent Astra audit reconstructed the project from approximately PR #132 through merged #138 and challenged the old A4b2b-first ordering.

The key derived observation is:

```text
A >= 0 and dim(shell)=1:

q_c >= 0 AND forall w, Delta(w) >= 0
  <-> successor one-step quadratic form is nonnegative.
```

So universal determinant positivity remains a valid sufficient closing theorem, but it is not presently a smaller RH subproblem. The active research route is now to remove resonance **without proving positivity**.

## NOW — regular-aperture selection

Target:

```text
every strict finite canonical negative witness
  -> arbitrarily nearby positive aperture preserving negativity
  -> all finitely relevant predecessor blocks injective/positive definite
  -> reselect global first bad at the new aperture.
```

Candidate mechanism:

```text
freeze finite prime cutoff Q
M_Q(L) = -log(L) I + B_Q(L)
L = exp(z)
Bhat_Q(z) periodic under z -> z + 2*pi*i
characteristic-polynomial root count -> determinant nonidentity
-> dense regular apertures.
```

This is a LEAD until the exact production-source analyticity, cutoff-threshold continuity, basis/Gram and predecessor-compression obligations are proved.

## After regularity — the actual arithmetic obstruction

With both predecessor blocks positive definite,

```text
x0 = A^-1 b
u0 = c - A^-1 b
S0 = q_c - <b,A^-1 b>.
```

The forced bad state has

```text
Ecanonical(u0) = Re S0 < 0.
```

The decisive remaining arithmetic theorem would prove

```text
Ecanonical(c - A^-1 b) >= 0
```

on the exact forced regular first-bad trial, equivalently

```text
<b,A^-1 b> <= q_c.
```

A proof that merely assumes successor positivity under another name is circular.

## Preserved post-#138 discoveries

The newest research delta records, at the appropriate evidence levels:

- **DERIVED:** `Delta(P_kerA b) = -||P_kerA b||^4`;
- **DERIVED:** a root-selected determinant identity at the safe negative root;
- **DERIVED / external exact-check:** `d = -(6/(2*N-1)) a` for the two correction vectors;
- **DERIVED / external symbolic result:** the elementary source-atom two-vector determinant has a negative leading coefficient, so atomwise positive determinant/SOS is not the default route;
- **EXPERIMENTAL SIGNAL:** sampled canonical regular Schur energies can arise from extremely large channel cancellation;
- **EXPERIMENTAL SIGNAL:** tiny modified prime-weight perturbations can flip successor sign while predecessors stay positive, showing that the exact arithmetic coefficients matter sharply.

These are research constraints, not RH evidence.

## Active path

```text
PROVED through #137
  off-line zero -> finite first-bad sign-failure countercertificate

NOW
  regular-aperture/log-lift selection

THEN
  regular first-bad countercertificate with unique A^-1 b

DISCOVERY
  full minimizing-trial Schur remainder and prime/arch/scalar cancellation

DECISIVE OPEN THEOREM
  Ecanonical(c - A^-1 b) >= 0 on the forced regular trial

TARGET
  contradiction -> no off-line zero -> explicit Mathlib RH wrapper
```

Universal one-step domination is retained as a broad fallback and should be promoted again if an independently positive canonical arithmetic mechanism is found.

## Permanent firewalls

- RH remains OPEN.
- theorem authority remains #137 until a new theorem-bearing head passes the complete gates;
- external reviews, exact finite scripts and high-precision numerics are not Lean theorem authority;
- a regular first-bad negative state is not a contradiction;
- source decomposition is not source positivity;
- no `A^-1` at zero before regularity is proved;
- no factorwise division by `alpha`, `Gamma`, overlap or source moment without theoremized nonzeroness;
- D remains algebraic, not unitary/isometric;
- generic or modified-source countermodels do not refute the actual canonical source;
- machine claim promotion remains separate from supporting theorem validity.

## Living research records

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS_POST_138_ASTRA_DELTA.md` — newest research-priority delta
- `research/RHRC/external_reviews/ASTRA_POST_138_RH_PATH_ASSESSMENT_2026_09_09.md`
- `research/RHRC/countermodels/POST_138_ASTRA_DIAGNOSTICS_2026_09_09.md`
- `research/RHRC/OBSTRUCTION_LEDGER.md`
- `research/RHRC/DEAD_ROUTES.md`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/control_v2/README.md`

**RH remains OPEN.**