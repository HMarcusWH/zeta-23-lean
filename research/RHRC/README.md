# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

```text
live main after merged PR #159 = 63862cd80501754c6c6599ffea09b874a327dae4
live main tree = cb7a81d3b10e7f909b794103f2a919a3a3ccf233
latest theorem-bearing PR = #159
validated theorem head = b2a064ad5d1f0acbd93309a9257c5661cfa3ec28
validated theorem tree = cb7a81d3b10e7f909b794103f2a919a3a3ccf233
RHRC #1021 / run 34736245287 = SUCCESS
Permansson #794 / run 34736245311 = SUCCESS
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

same-state shifted Riesz x cross-parity source composition            OPEN / NOW
mixed quadratic-normal source-pairing jet -> M4                       DERIVED / OPEN
independent contradiction-producing arithmetic restriction            OPEN
negative-root exclusion                                                OPEN
terminal zeta/Mathlib seam                                             OPEN
RH                                                                     OPEN
```

## Post-#159 state

The first Riesz boundary-term theorem is now consumed infrastructure, not the research frontier. The exact complete transformed negative state survives, and the first unforced endpoint dependence is explicitly a centered-moment square.

The deeper post-green pass identified a stronger composition with the existing cross-parity source stack. At an even negative secular root the repository already proves

```text
odd secular scalar
  = overlap * evenQuadraticSourceMoment(even shifted trial),
```

and the source moment is exactly `explicitCanonicalSourceMoment`, with pole/prime/archimedean cancellation preserved.

Global first-bad minimality already supplies predecessor nonnegativity for either parity below the first globally bad size.

## Immediate frontier — FB-04B

The next theorem-bearing step is to align those existing facts with #159 on the same negative secular trial.

Desired fail-closed endpoint:

```text
odd successor ParityBad
OR
explicitCanonicalSourceMoment(even negative secular trial) != 0.
```

This is a structural narrowing, not RH and not a sign theorem.

The next analytic lead, only if that composition survives, is the mixed quadratic-normal source-pairing jet expected to satisfy

```text
h_v^(7)(0) = -2*(2*pi)^6*M4(v)
```

on even boundary-flat carriers. This remains DERIVED / OPEN IN LEAN.

## Current execution priority

1. **FB-04B — same-state composition.** Theoremize shifted negative-root Riesz × cross-parity source obstruction.
2. **Post-green falsification.** Attack simultaneous both-parity badness, source-moment zeros, overlap degeneracy and fixed-cell threshold behavior.
3. **FB-04C — mixed source jet.** If useful, theoremize the linear `M4` bridge.
4. **FB-05 — arithmetic closure.** Prove an independent contradiction-producing canonical restriction if the composed mechanism survives.
5. **FB-06/07.** Same-state contradiction, negative-root exclusion, terminal seam.

Universal one-step domination remains a broad fallback only when supplied by genuinely independent canonical arithmetic.

## Exact falsification memory

The K=2 boundary-flat vectors still refute universal pointwise fixed-sign smoothed-integrand positivity. #159's signed integrated recurrence does not revive that route.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and theorem gates.
- `RESEARCH_LEADS_POST_159_RIESZ_CROSS_PARITY_FRONTIER_DELTA.md` — newest audited synthesis.
- `RESEARCH_LEADS_POST_157_PRODUCTION_RIESZ_ARITHMETIC_FRONTIER_DELTA.md` — historical pre-#159 synthesis.
- `countermodels/POST_155_RIESZ_POINTWISE_SIGN_COUNTERMODELS_2026_09_13.md` — dead pointwise-sign shortcut memory.
- `OBSTRUCTION_LEDGER.md` / `DEAD_ROUTES.md` — reusable blockers.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — executable routing semantics.

## Permanent firewalls

- RH remains OPEN.
- theorem authority is through #159; machine claim promotion remains separate.
- transformed negativity is not a contradiction.
- exact discrepancy/Riesz identities are not arithmetic sign theorems.
- R8/R9 statements remain conditional on even parity where stated.
- #159 self-energy jets do not establish the mixed source-pairing jet.
- no division by alpha/Gamma/overlap/source moment without theorem-backed nonzeroness.
- pointwise fixed-sign smoothed-integrand positivity remains dead.
- external derivations/numerics are not Lean authority.
- `D` remains algebraic, not unitary/isometric.
- negative-root exclusion still needs the terminal seam before `RiemannHypothesis`.

**RH remains OPEN.**
