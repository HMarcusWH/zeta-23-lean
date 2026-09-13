# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

```text
live main after merged PR #161 = ef29b45de683962122c1e898ed31bf9417757125
live main tree = b080572e87068889a72b4e612f99ddf0bd67f482
latest theorem-bearing PR = #161
validated theorem head = 188407fb02a37de2e380ede3b60e140953b01441
validated theorem tree = b080572e87068889a72b4e612f99ddf0bd67f482
RHRC #1026 = SUCCESS
Permansson #799 = SUCCESS
control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact Lean/compiler/CI are authoritative. The validated #161 head and merged `main` are distinct commits with the same theorem tree.

## Current theorem ladder

```text
off-line zero -> legal finite canonical negative obstruction            PROVED
first-bad / parity / Schur / secular machinery                          PROVED
source-explicit cross-parity transfer                                   PROVED / #129
exact canonical source-moment decomposition                             PROVED / #131
zero-shift source transport / absolute source energy / determinant      PROVED / #134-#137
regular selected first-bad endpoint                                     PROVED / #140-#150
retained first-bad + exact pole-prime discrepancy                       PROVED / #153
legal generic Riesz smoothing + parity/even source jets                 PROVED / #155
complex production D transport + exact complete Riesz 6/even 8          PROVED / #157
retained transformed negativity + off-line-zero R6 wrapper              PROVED / #157
general moment-prefix odd-jet law                                       PROVED / #159
exact seventh / even ninth leading-moment self-energy jets              PROVED / #159
generic signed complete-channel Riesz boundary recurrence               PROVED / #159
retained R6->R7 / even R8->R9 moment-square boundaries                  PROVED / #159
same-state shifted Riesz x cross-parity source composition              PROVED / #161
odd-good -> nonzero exact production source moment                      PROVED / #161
headline odd-bad OR explicit-source-nonzero fork                        PROVED / #161

mixed quadratic-normal source-pairing jet -> M4                         DERIVED / OPEN
source-moment / M4 canonical-state rigidity                             OPEN
simultaneous even/odd bad exclusion                                     OPEN
odd-selected first-bad branch closure                                   OPEN
independent contradiction-producing arithmetic restriction              OPEN
negative-root exclusion                                                  OPEN
outside-strip/trivial-zero seam + Mathlib RH wrapper                     OPEN
RH                                                                       OPEN
```

## What #161 added

PR #161 closed the same-state composition gap. Lean now proves that the retained even negative root can be reconstructed as the canonical shifted secular root built from whole-cell predecessor nonnegativity, and that the **same shifted trial** carries:

```text
complete Riesz-8 energy < 0
exact Riesz-9 / M4 boundary inequality
odd secular scalar = Gamma * explicitCanonicalSourceMoment.
```

It also proves

```text
not odd ParityBad
  -> odd secular scalar != 0
  -> explicitCanonicalSourceMoment != 0,
```

and therefore the retained even-selected fork

```text
odd successor ParityBad
OR
explicitCanonicalSourceMoment(even shifted negative trial) != 0.
```

No division by Gamma/overlap is used, no sign of the Riesz endpoint scalar is assumed, and no implication from nonzero explicit source moment to nonzero `M4` is asserted.

## Current active path

The live theorem frontier is now **FB-04C**: theoremize the exact mixed quadratic-normal source observable and test whether its local `M4` jet genuinely couples to the global arithmetic source obstruction already forced by #161.

Conceptually:

```text
h_v(omega)
  = <centeredQuadraticNormal, sourceMatrix(omega) v>
      / <centeredQuadraticNormal, centeredQuadraticNormal>
```

with expected even-boundary-flat target

```text
h_v^(7)(0) = -2*(2*pi)^6*M4(v).
```

If this survives exact Lean normalization, it can be combined with the theorem-backed Riesz boundary

```text
B8(v) = 2*(2*pi)^8*S8(L)*|M4(v)|^2
```

on the same shifted state. The decisive open problem is still an **independent canonical arithmetic rigidity/sign restriction** that contradicts the forced state.

In parallel, simultaneous even+odd badness should be attacked in exact generic/rank-one controls before theorem investment, and the odd-selected first-bad branch remains an explicit coverage gap.

## Falsified shortcut

Exact K=2 boundary-flat fixtures still refute

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand.
```

The integrated boundary recurrence and #161 same-state composition do not revive that dead pointwise claim.

## Documentation authority

Current living state is maintained in:

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/RESEARCH_LEADS.md`;
- `research/RHRC/RESEARCH_LEADS_POST_161_SAME_STATE_RIESZ_SOURCE_RIGIDITY_DELTA.md`;
- `research/RHRC/DOCUMENTATION_AUTHORITY.md`;
- `research/RHRC/VALIDATION_PROTOCOL.md`;
- `research/RHRC/routes/R003_ccm_bridge/README.md`;
- `research/RHRC/control_v2/README.md`.

Older dated deltas, external reviews and countermodel records remain historical evidence and are not rewritten to look current.

## Permanent firewalls

- RH remains OPEN.
- theorem authority through #161 is separate from machine claim promotion.
- retained/shifted transformed negativity is not a contradiction.
- exact Riesz identities are not arithmetic sign theorems.
- R8/R9 statements remain conditional on even parity where stated.
- the #159 self-energy ninth-jet theorem is not the unproved mixed source-pairing seventh-jet theorem.
- `explicitCanonicalSourceMoment != 0` does not imply `M4 != 0`, nor conversely, without a theorem.
- simultaneous even/odd badness is not excluded.
- selected parity cannot be assumed even WLOG.
- no division by alpha/Gamma/overlap/source moment without separate nonzeroness.
- pointwise fixed-sign smoothed-integrand positivity remains dead.
- `D` remains algebraic, not unitary/isometric.
- interval-certified finite numerics are not Lean theorem authority.
- negative-root exclusion is not the terminal Mathlib `RiemannHypothesis` statement without the final seam.

**RH remains OPEN.**
