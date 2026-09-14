# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

Live GitHub head + exact Lean compiler + CI are authoritative dynamically.

```text
THEOREM AUTHORITY
latest theorem-bearing PR = #163
validated theorem head = b418ff034428f92594bab0e5b8276181a086ee4b
validated theorem tree = c397b3a015ea54e38ecfe626d6e29556fe963839
RHRC #1039 = SUCCESS
Permansson #812 = SUCCESS

LATEST RESEARCH-EVIDENCE ANCHOR
merged research PR = #172
validated research head = 4c857cd031497d895232a18a4bfb9a094d9facae
merged research commit = a31bb0bb7f025d7727dd3f224c705af797f64a19
research tree = c64b098c3159d739fa15eeaa96e35693615873d7
RHRC #1063 = SUCCESS
Permansson #836 = SUCCESS

CONTROL SEMANTIC AUTHORITY
PR #117 merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
selected formal first break = E4A4-SCHUR-FB-05
RH = OPEN
```

Research PRs after #163 refine the attack surface; they do not create Lean theorem authority.

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
same-state shifted Riesz x cross-parity source composition            PROVED / #161
odd-good -> explicit source moment nonzero                             PROVED / #161
mixed quadratic-normal seventh source jet -> M4                       PROVED / #163
finite-prime sampling of the same mixed source observable             PROVED / #163
mixed-jet squared Riesz-8/Riesz-9 boundary coupling                   PROVED / #163
retained mixed-jet/Riesz specialization                               PROVED / #163

source-moment / M4 global rigidity                                    OPEN
endpoint-scalar global sign/nonvanishing                              OPEN
q13 even 2x2 scalar barrier                                           OPEN / ACTIVE RESEARCH
simultaneous even/odd bad exclusion                                   OPEN
odd-selected branch closure                                           OPEN
negative-root exclusion                                               OPEN
terminal zeta/Mathlib seam                                            OPEN
RH                                                                    OPEN
```

## Post-#163 research progression

### #165 — endpoint scalar

The exact executable `S8(L)` normalization is audited with prime powers. Broad finite evidence is positive, but positivity alone is not a contradiction.

### #166 — theorem-aligned shifted state

The finite discriminator uses the true generalized shifted secular ray `u_lambda = c - W(H-lambda G)^(-1)r`. A broad scan found no finite negative successor and isolated the near-critical `Q16/N3/K4/odd` family.

### #167 — Q16 scalar barrier

The strongest finite candidate stayed positive in floating discovery. Direct whole-cell Arb subdivision remained 256/256 `UNRESOLVED`, so brute subdivision of the current dependency-heavy matrix representation is not the current certification method.

### #168 — threshold moment jet

Boundary-flat parity annihilation yields exact executable first surviving source-energy orders 7 through `M3^2` in odd parity and 9 through `M4^2` in even parity. The exact log17 threshold and 18 two-sided Arb microscope points certify positive. The full Q17 state continues downward but remains positive.

### #170 — theorem-aligned Schur visibility

The selected scalar is rebuilt in `[W|c]` one-step coordinates and unit-shell normalized. The q17 threshold direction is finite-certified Schur-visible; its exact entering-q pivot effect is positive at checked offsets while the q-removed background has negative finite differences.

### #172 — threshold-to-threshold production barrier

The research layer tests genuine nonzero von-Mangoldt intervals across q/N/parity. No sampled bad successor is found, but finite current-q entry lift is sign-indefinite:

```text
q9 / even   negative
q13 / even  negative
q16 / odd   positive
```

The most dangerous sampled target is `q13 -> 16, N2, K3, even`. At the quantized near-minimum, Arb certifies

```text
full unit-shell pivot      ~= +5.8401616e-12
q-removed background       ~= +1.2217611e-11
q13 entry lift             ~= -6.3774491e-12
```

with H1 predecessor positivity certified.

No whole-cell or first-bad exclusion theorem follows.

## Immediate frontier — FB-05 q13 even 2x2 scalar barrier

For the q13 target the theorem-aligned executable geometry is exactly 1D predecessor -> 2D successor. Write

```text
H(L) = [[a(L), b(L)],
        [b(L), d(L)]]
```

so

```text
H1 <-> a(L) > 0
P(L) = d(L) - b(L)^2/a(L)
Delta_2(L) = a(L)d(L) - b(L)^2
```

and, on H1 scope,

```text
sign P(L) = sign Delta_2(L).
```

The next research pass should certify or falsify

```text
a(L) > 0 and Delta_2(L) > 0
```

through the full arithmetic interval `log13 <= L <= log16`.

Because the backend tracks physical `Q=floor(exp L)`, rigorous certification should be piecewise over

```text
[log13,log14], [log14,log15], [log15,log16]
```

unless exact inertness of zero-von-Mangoldt Q=14/15 additions is separately established.

This is a dependency-reduced scalar escape from the #167 representation failure, not a revival of brute full-matrix subdivision.

A positive q13 whole-cell result would still be a finite method/structure result, not FB-05 closure.

## Current execution priority

1. **Resolve/falsify the q13/N2/K3/even 2x2 determinant barrier.**
2. **If positive, identify the generalizable arithmetic reason rather than stopping at one finite cell.**
3. **If negative while H1 holds, replay the exact state through #166 immediately.**
4. **Choose the weakest surviving theorem** only if it supplies independent information rather than restating successor positivity.
5. **Compose with the exact retained #161/#163 state.**
6. **Close coverage debt:** simultaneous parity and odd-selected branches remain explicit.
7. **FB-06/07:** same-state contradiction, negative-root exclusion, terminal seam.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and theorem gates.
- `RESEARCH_LEADS_POST_172_Q13_EVEN_SCALAR_BARRIER_DELTA.md` — newest audited research synthesis.
- `RESEARCH_LEADS_POST_170_SCHUR_VISIBILITY_THRESHOLD_BARRIER_DELTA.md` — previous post-green synthesis.
- `OBSTRUCTION_LEDGER.md` / `DEAD_ROUTES.md` — reusable blockers.
- `routes/R003_ccm_bridge/README.md` — active route theorem/research surface.
- `control_v2/README.md` — executable routing semantics.

## Permanent firewalls

- RH remains OPEN.
- theorem authority remains through #163 until a later Lean theorem PR is compiler-green.
- research PR green is not theorem authority.
- exact executable algebra is not a Lean theorem.
- finite Arb certification is not a global or whole-cell theorem.
- finite differences/quadrature are not derivative theorems.
- transformed negativity is not a contradiction.
- exact discrepancy/Riesz identities are not arithmetic sign theorems.
- endpoint-scalar positivity alone is not first-bad exclusion.
- arithmetic entry lift is not known to have a universal favorable sign.
- physical H1 does not imply q-removed-background H1.
- independent channel Schur pivots may not be added.
- large channel cancellation makes coarse component-sign reasoning unsafe.
- simultaneous even/odd badness remains open.
- selected parity cannot be assumed even WLOG.
- no division by alpha/Gamma/overlap/source moment without theorem-backed nonzeroness.
- pointwise fixed-sign smoothed-integrand positivity remains dead.
- `UNRESOLVED` interval output is not sign evidence.
- `D` remains algebraic, not unitary/isometric.
- q13 whole-cell positivity alone would not imply global first-bad exclusion.
- negative-root exclusion still needs the terminal seam before `RiemannHypothesis`.

**RH remains OPEN.**
