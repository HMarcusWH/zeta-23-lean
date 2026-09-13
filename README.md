# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

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

Live GitHub head + exact Lean/compiler/CI are authoritative. The validated #159 head and merged `main` are distinct commits with the same theorem tree.

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
exact seventh / even ninth leading-moment self-energy jets               PROVED / #159
generic signed complete-channel Riesz boundary recurrence               PROVED / #159
retained R6->R7 / even R8->R9 moment-square boundaries                  PROVED / #159

same-state shifted Riesz x cross-parity source composition              OPEN / NEXT
mixed quadratic-normal source-pairing jet -> M4                         DERIVED / OPEN
independent contradiction-producing arithmetic restriction              OPEN
negative-root exclusion                                                  OPEN
outside-strip/trivial-zero seam + Mathlib RH wrapper                     OPEN
RH                                                                       OPEN
```

## What #159 added

PR #159 closed the former first-boundary-term sublead. Lean now proves the exact first source-energy jet and a general moment-prefix theorem

```text
M0=...=M(r-1)=0
  -> g^(2r+1)(0) = 2 * (-(2*pi)^2)^r * normSq(Mr).
```

Consequently the exact boundary-flat seventh derivative and even boundary-flat ninth derivative are theorem authority.

#159 also proves a generic signed recurrence

```text
canonicalRieszSourceChannelEnergy r
  = canonicalRieszSourceChannelEnergy (r+1)
    + canonicalPolePrimeRieszBoundaryTerm r.
```

No sign of the endpoint scalar is asserted. On retained first-bad states this yields exact R6/R7 and, under even parity, R8/R9 moment-square decompositions.

## Current active path

The post-green repo-wide pass found that #159 now composes naturally with theorem inventory that predates it.

At an even negative secular root the existing cross-parity theorem gives

```text
odd secular scalar
  = overlap * evenQuadraticSourceMoment(even shifted trial),
```

and the source moment is exactly the production quantity `explicitCanonicalSourceMoment`, retaining pole/prime/archimedean cancellation.

Global first-bad minimality already supplies predecessor nonnegativity for either parity below the first globally bad size.

The next theorem-bearing target is therefore to place the **negative secular root, #159 transformed Riesz state, and cross-parity source moment on the same shifted trial**, and derive the fail-closed fork

```text
odd successor is ParityBad
OR
explicitCanonicalSourceMoment(even negative secular trial) != 0.
```

Only after this composition survives should the project invest in the mixed quadratic-normal source-pairing jet expected to connect the linear source defect to #159's quadratic `|M4|^2` Riesz boundary.

## Falsified shortcut

Exact K=2 boundary-flat fixtures still refute

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand.
```

#159's integrated boundary recurrence is not a revival of that dead pointwise claim.

## Documentation authority

Current living state is maintained in:

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/RESEARCH_LEADS.md`;
- `research/RHRC/RESEARCH_LEADS_POST_159_RIESZ_CROSS_PARITY_FRONTIER_DELTA.md`;
- `research/RHRC/DOCUMENTATION_AUTHORITY.md`;
- `research/RHRC/VALIDATION_PROTOCOL.md`;
- `research/RHRC/routes/R003_ccm_bridge/README.md`;
- `research/RHRC/control_v2/README.md`.

Older dated deltas, external reviews and countermodel records remain historical evidence and are not rewritten to look current.

## Permanent firewalls

- RH remains OPEN.
- theorem authority through #159 is separate from machine claim promotion.
- retained transformed negativity is not a contradiction.
- exact Riesz identities are not arithmetic sign theorems.
- R8/R9 statements remain conditional on even parity where stated.
- the #159 self-energy ninth-jet theorem is not the unproved mixed source-pairing seventh-jet theorem.
- no division by alpha/Gamma/overlap/source moment without separate nonzeroness.
- pointwise fixed-sign smoothed-integrand positivity remains dead.
- `D` remains algebraic, not unitary/isometric.
- interval-certified finite numerics are not Lean theorem authority.
- negative-root exclusion is not the terminal Mathlib `RiemannHypothesis` statement without the final seam.

**RH remains OPEN.**
