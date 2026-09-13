# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

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

Live GitHub head + exact Lean compiler + CI are authority. Control v2 may select research actions but may not promote theorem or terminal RH status.

## Theorem-backed route

```text
finite negative obstruction / first-bad / Schur machinery            PROVED
source-explicit cross-parity transfer                                 PROVED / #129
exact canonical source-moment decomposition                           PROVED / #131
zero-shift transport / absolute energy / determinant                  PROVED / #134-#137
regular selected first bad                                            PROVED / #140-#150
retained certificate + exact pole-prime discrepancy                   PROVED / #153
legal generic Riesz smoothing + source parity/even jets               PROVED / #155
complex production transport + exact complete Riesz 6/even 8          PROVED / #157
retained transformed negativity + ExceptionalZero R6 wrapper          PROVED / #157
general moment-prefix odd-jet law                                     PROVED / #159
exact seventh / even ninth leading-moment self-energy jets             PROVED / #159
generic signed complete-channel Riesz boundary recurrence             PROVED / #159
retained R6->R7 / even R8->R9 boundary decompositions                 PROVED / #159
same-state shifted Riesz x cross-parity source composition            PROVED / #161
odd-good -> explicit source moment nonzero                             PROVED / #161
odd-bad OR explicit-source-nonzero fork                               PROVED / #161

mixed quadratic-normal source-pairing jet -> M4                       DERIVED / OPEN
source-moment / M4 rigidity                                           OPEN
simultaneous even/odd bad exclusion                                   OPEN
odd-selected branch closure                                           OPEN
independent contradiction-producing arithmetic restriction            OPEN
negative-root exclusion                                                OPEN
terminal zeta/Mathlib seam                                             OPEN
RH                                                                     OPEN
```

## Post-#161 state

The same-state alignment problem is closed. On the retained even shifted negative trial, Lean now simultaneously proves strict complete Riesz-8 negativity, the exact Riesz-9 / `M4` boundary inequality, and the cross-parity identity

```text
odd secular scalar = Gamma * explicitCanonicalSourceMoment.
```

If the odd successor is good, the odd scalar is nonzero and the exact production source moment is nonzero. Hence the fail-closed retained fork

```text
odd successor ParityBad
OR
explicitCanonicalSourceMoment(even shifted negative trial) != 0.
```

This is a structural narrowing, not a contradiction and not RH.

## Immediate frontier — FB-04C

The next theorem-bearing step is the mixed quadratic-normal source observable expected to satisfy

```text
h_v^(7)(0) = -2*(2*pi)^6*M4(v)
```

on even boundary-flat carriers.

The objective is not merely to prove that derivative identity, but to determine whether the resulting linear source jet gives genuinely new information when combined with:

```text
explicitCanonicalSourceMoment(evenShiftedTrial)
```

and the theorem-backed quadratic Riesz `|M4|^2` boundary on the same state.

`explicitCanonicalSourceMoment != 0` does not imply `M4 != 0`, nor conversely, without new mathematics.

## Current execution priority

1. **FB-04C — mixed source/M4 bridge.** Theoremize the exact mixed source observable and its seventh `M4` jet if exact production normalization checks survive.
2. **Post-green falsification.** Attack source-moment/M4 separation and simultaneous even+odd badness in exact canonical/generic controls.
3. **Odd-branch audit.** Preserve the odd-selected first-bad case as explicit coverage debt; no WLOG-even shortcut is available.
4. **FB-05 — arithmetic closure.** Prove an independent contradiction-producing canonical restriction if the composed mechanism survives.
5. **FB-06/07.** Same-state contradiction, negative-root exclusion, terminal seam.

Universal one-step domination remains a broad fallback only when supplied by genuinely independent canonical arithmetic.

## Exact falsification memory

The K=2 boundary-flat vectors still refute universal pointwise fixed-sign smoothed-integrand positivity. #159's signed integrated recurrence and #161's same-state composition do not revive that route.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and theorem gates.
- `RESEARCH_LEADS_POST_161_SAME_STATE_RIESZ_SOURCE_RIGIDITY_DELTA.md` — newest audited synthesis.
- `RESEARCH_LEADS_POST_159_RIESZ_CROSS_PARITY_FRONTIER_DELTA.md` — historical pre-#161 synthesis.
- `countermodels/POST_155_RIESZ_POINTWISE_SIGN_COUNTERMODELS_2026_09_13.md` — dead pointwise-sign shortcut memory.
- `OBSTRUCTION_LEDGER.md` / `DEAD_ROUTES.md` — reusable blockers.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — executable routing semantics.

## Permanent firewalls

- RH remains OPEN.
- theorem authority is through #161; machine claim promotion remains separate.
- transformed negativity is not a contradiction.
- exact discrepancy/Riesz identities are not arithmetic sign theorems.
- R8/R9 statements remain conditional on even parity where stated.
- #159 self-energy jets do not establish the mixed source-pairing jet.
- nonzero explicit source moment does not establish nonzero M4.
- simultaneous even/odd badness remains open.
- selected parity cannot be assumed even WLOG.
- no division by alpha/Gamma/overlap/source moment without theorem-backed nonzeroness.
- pointwise fixed-sign smoothed-integrand positivity remains dead.
- external derivations/numerics are not Lean authority.
- `D` remains algebraic, not unitary/isometric.
- negative-root exclusion still needs the terminal seam before `RiemannHypothesis`.

**RH remains OPEN.**
