# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

```text
live main after merged PR #163 = bd3fa1aafa7df2aa35873df532bdb6f17ddd2bbd
live main tree = c397b3a015ea54e38ecfe626d6e29556fe963839
latest theorem-bearing PR = #163
validated theorem head = b418ff034428f92594bab0e5b8276181a086ee4b
validated theorem tree = c397b3a015ea54e38ecfe626d6e29556fe963839
RHRC #1039 = SUCCESS
Permansson #812 = SUCCESS
control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact Lean/compiler/CI are authoritative. The validated #163 head and merged `main` are distinct commits with the same theorem tree.

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
mixed quadratic-normal seventh source jet -> M4                         PROVED / #163
finite-prime sampling of the same mixed source observable               PROVED / #163
mixed-jet squared Riesz-8/Riesz-9 boundary coupling                     PROVED / #163
retained mixed-jet/Riesz specialization                                 PROVED / #163

source-moment / M4 canonical-state rigidity                             OPEN
endpoint-scalar sign/nonvanishing                                       OPEN
simultaneous even/odd bad exclusion                                     OPEN
odd-selected first-bad branch closure                                   OPEN
independent contradiction-producing arithmetic restriction              OPEN / ACTIVE
negative-root exclusion                                                  OPEN
outside-strip/trivial-zero seam + Mathlib RH wrapper                     OPEN
RH                                                                       OPEN
```

## What #163 added

PR #163 closes FB-04C. Lean now proves that the exact production mixed quadratic-normal observable

```text
h_v(omega) = quadraticNormalSourceAtom K v omega
```

satisfies, for even boundary-flat carriers,

```text
h_v^(7)(0) = -2*(2*pi)^6*M4(v),
|h_v^(7)(0)|^2 = 4*(2*pi)^12*|M4(v)|^2,
2*(2*pi)^4*(R8(v)-R9(v)) = S8(L)*|h_v^(7)(0)|^2.
```

The exact finite-prime contribution to `explicitCanonicalSourceMoment` samples this same `quadraticNormalSourceAtom` at the production prime-source coordinates. Pole and archimedean terms remain.

On the retained even shifted first-bad state, #163 specializes the same identities and proves

```text
2*(2*pi)^4*R9 < -S8(L)*|h^(7)(0)|^2
```

without assuming any sign for `S8(L)`. Under opposite-parity goodness it also theoremizes `crossParityGamma != 0`.

No global sourceMoment<->M4 implication and no endpoint-scalar sign theorem is asserted.

## Current active path

The live theorem frontier is now **FB-05**: find an independent canonical arithmetic restriction that makes the exact retained #161/#163 state impossible.

Highest-information candidate subroutes are:

```text
endpoint-scalar sign/nonvanishing
production prime-sample -> local-jet rigidity
simultaneous parity badness exclusion with actual arithmetic
odd-selected first-bad coverage
another cancellation-preserving invariant on the same state
```

The next theorem PR should be chosen only after adversarial falsification of these candidates. In particular, we do not pre-assume that `S8(L)` is positive.

## Falsified shortcut

Exact K=2 boundary-flat fixtures still refute

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand.
```

The integrated boundary recurrence, #161 same-state composition and #163 mixed-jet rewrite do not revive that dead pointwise claim.

## Documentation authority

Current living state is maintained in:

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/RESEARCH_LEADS.md`;
- `research/RHRC/RESEARCH_LEADS_POST_163_MIXED_SOURCE_RIESZ_ARITHMETIC_FRONTIER_DELTA.md`;
- `research/RHRC/DOCUMENTATION_AUTHORITY.md`;
- `research/RHRC/VALIDATION_PROTOCOL.md`;
- `research/RHRC/routes/R003_ccm_bridge/README.md`;
- `research/RHRC/control_v2/README.md`.

Older dated deltas, external reviews and countermodel records remain historical evidence and are not rewritten to look current.

## Permanent firewalls

- RH remains OPEN.
- theorem authority through #163 is separate from machine claim promotion.
- retained/shifted transformed negativity is not a contradiction.
- exact Riesz identities are not arithmetic sign theorems.
- R8/R9 statements remain conditional on even parity where stated.
- #159 self-energy jets are distinct from #163's independently proved mixed source-pairing theorem.
- `explicitCanonicalSourceMoment != 0` does not imply `M4 != 0`, nor conversely, without a theorem.
- exact finite-prime sampling does not by itself determine the local seventh jet.
- no sign or nonvanishing theorem for `S8(L)` is currently available.
- simultaneous even/odd badness is not excluded.
- selected parity cannot be assumed even WLOG.
- no division by alpha/Gamma/overlap/source moment without separate nonzeroness.
- pointwise fixed-sign smoothed-integrand positivity remains dead.
- `D` remains algebraic, not unitary/isometric.
- interval-certified finite numerics are not Lean theorem authority.
- negative-root exclusion is not the terminal Mathlib `RiemannHypothesis` statement without the final seam.

**RH remains OPEN.**
