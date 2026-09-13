# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

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
mixed quadratic-normal seventh source jet -> M4                       PROVED / #163
finite-prime sampling of the same mixed source observable             PROVED / #163
mixed-jet squared Riesz-8/Riesz-9 boundary coupling                   PROVED / #163
retained mixed-jet/Riesz specialization                               PROVED / #163

source-moment / M4 global rigidity                                    OPEN
endpoint-scalar sign/nonvanishing                                     OPEN
simultaneous even/odd bad exclusion                                   OPEN
odd-selected branch closure                                           OPEN
independent contradiction-producing arithmetic restriction            OPEN / ACTIVE
negative-root exclusion                                                OPEN
terminal zeta/Mathlib seam                                             OPEN
RH                                                                     OPEN
```

## Post-#163 state

The retained even shifted negative state now has four exact, theorem-backed views:

```text
R8(u_lambda) < 0
F_odd(lambda) = Gamma(lambda)*explicitCanonicalSourceMoment(u_lambda)
h^(7)(0) = -2*(2*pi)^6*M4(u_lambda)
2*(2*pi)^4*(R8(u_lambda)-R9(u_lambda)) = S8(L)*|h^(7)(0)|^2.
```

If the odd successor is good, #161 gives nonzero production source moment and #163 gives nonzero `Gamma`. In the even-selected branch #163 also gives the strict R9 upper bound

```text
2*(2*pi)^4*R9(u_lambda) < -S8(L)*|h^(7)(0)|^2
```

without assuming any sign for `S8(L)`.

This is a structural narrowing, not a contradiction and not RH.

## Immediate frontier — FB-05

FB-04C is closed. The local mixed-source/Riesz coupling is no longer the missing theorem.

The next mathematical task is an **independent canonical arithmetic restriction** on the exact retained state. Highest-information candidates are:

1. exact sign/nonvanishing analysis of `canonicalPolePrimeRieszEndpointScalar L 8`;
2. canonical prime-sample -> local-jet rigidity for `quadraticNormalSourceAtom`;
3. arithmetic exclusion of simultaneous even+odd badness;
4. odd-selected first-bad coverage;
5. another cancellation-preserving invariant that composes with the #161/#163 state.

`explicitCanonicalSourceMoment != 0` does not imply `M4 != 0`, nor conversely, without new mathematics. Exact finite-prime sampling of the same analytic function does not by itself determine its seventh derivative at zero.

## Current execution priority

1. **FB-05 falsification pass.** Attack endpoint-scalar, sample-to-jet, simultaneous-parity and odd-branch candidates before theorem investment.
2. **Choose the weakest surviving theorem.** If endpoint-scalar sign/nonvanishing survives, formalize it; if not, pivot immediately.
3. **Compose with the retained state.** Any successful arithmetic theorem must constrain the exact #161/#163 shifted state, not a nearby or zero-shift surrogate.
4. **FB-06/07.** Same-state contradiction, negative-root exclusion, terminal seam.

Universal one-step domination remains a broad fallback only when supplied by genuinely independent canonical arithmetic.

## Exact falsification memory

The K=2 boundary-flat vectors still refute universal pointwise fixed-sign smoothed-integrand positivity. #159's signed integrated recurrence, #161's same-state composition and #163's mixed-jet rewrite do not revive that route.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and theorem gates.
- `RESEARCH_LEADS_POST_163_MIXED_SOURCE_RIESZ_ARITHMETIC_FRONTIER_DELTA.md` — newest audited synthesis.
- `RESEARCH_LEADS_POST_161_SAME_STATE_RIESZ_SOURCE_RIGIDITY_DELTA.md` — historical pre-#163 synthesis.
- `countermodels/POST_155_RIESZ_POINTWISE_SIGN_COUNTERMODELS_2026_09_13.md` — dead pointwise-sign shortcut memory.
- `OBSTRUCTION_LEDGER.md` / `DEAD_ROUTES.md` — reusable blockers.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — executable routing semantics.

## Permanent firewalls

- RH remains OPEN.
- theorem authority is through #163; machine claim promotion remains separate.
- transformed negativity is not a contradiction.
- exact discrepancy/Riesz identities are not arithmetic sign theorems.
- R8/R9 statements remain conditional on even parity where stated.
- #159 self-energy jets do not establish #163's mixed source-pairing theorem by type; #163 proves it independently.
- nonzero explicit source moment does not establish nonzero M4.
- finite prime samples do not by themselves determine the local seventh jet.
- endpoint-scalar sign/nonvanishing remains open.
- simultaneous even/odd badness remains open.
- selected parity cannot be assumed even WLOG.
- no division by alpha/Gamma/overlap/source moment without theorem-backed nonzeroness.
- pointwise fixed-sign smoothed-integrand positivity remains dead.
- external derivations/numerics are not Lean authority.
- `D` remains algebraic, not unitary/isometric.
- negative-root exclusion still needs the terminal seam before `RiemannHypothesis`.

**RH remains OPEN.**
