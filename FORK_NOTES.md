# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

```text
THEOREM AUTHORITY
latest theorem-bearing PR = #184
validated theorem head = a756494ebe7e2530715e996b9a9a341fbe07c683
merged theorem commit = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e
validated theorem tree = 6c77cd470809959a403b3bcc5f08d39f4076fa4c
RHRC #1089 = SUCCESS
Permansson #862 = SUCCESS

LATEST RESEARCH-EVIDENCE ANCHOR
merged research PR = #186
validated research head = 7d277a99437d98fdb7c831f25a130eac07f1b3af
merged research commit = 0494658a87d29eeb2124aa16232c264c21d23c18
RHRC #1091 = SUCCESS
Permansson #864 = SUCCESS
research disposition = DOMINATION_SIGNAL_MIXED

CONTROL SEMANTIC AUTHORITY
PR #117 merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
selected first break = E4A4-SCHUR-FB-05
RH = OPEN
```

## Recent theorem packages

```text
#129 source-explicit cubic defect + cross-parity secular transfer
#131 exact canonical source-moment decomposition
#134 denominator-free whole-kernel source transport
#136 absolute canonical source energy + exact channel decomposition
#137 exact source pairing + one-step determinant
#140-#150 regular-aperture / retained selected first bad
#153 retained first-bad negative-energy certificate + exact discrepancy
#155 legal generic Riesz smoothing + source oddness/even jets
#157 complex production D transport + exact complete Riesz 6/even 8 + retained negativity
#159 general moment-prefix odd jets + exact signed Riesz boundary recurrence
#161 same-state shifted Riesz x cross-parity source obstruction
#163 mixed quadratic-normal source jet x retained Riesz boundary coupling
#182 generic real 2x2 Schur-envelope derivative + H1 contact orientation transfer
#184 complex-Hermitian Schur + full frozen parity log-drift + N2 shell geometry
```

## What #184 adds

`Zeta23/CCM/HermitianSchurEnvelopeDerivative.lean` and `Zeta23/CCM/FrozenN2SchurLogDrift.lean` are inside the aggregate CCM build.

The production-facing Schur correction is the genuine Hermitian form

```text
P = d - |b|^2/a.
```

The exact frozen production family is theoremized on logarithmic coordinate `t` as

```text
M~(t) = -t I + R~(t),
```

with fixed-cell equality to `parityCompressedCanonical`. For N2/K3, Lean proves the canonical cubic shell is nonzero, predecessor and shell reconstruct the successor, and predecessor is orthogonal to shell.

Under the required scalar derivative data, Lean proves

```text
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
```

and

```text
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0.
```

This closes the production/Hermitian/log-cover algebraic interface. It does not prove that actual source-specific arithmetic always satisfies the domination premise.

## Research packages through #186

```text
#165 exact executable Riesz-8 endpoint-scalar audit
#166 theorem-aligned shifted-state discriminator
#167 Q16 near-critical cell / interval-method audit
#168 log17 boundary-flat threshold-jet / Q17 microscope
#170 theorem-aligned Schur visibility / background-drift audit
#172 threshold-to-threshold Schur barrier falsification
#174 q13/N2/K3/even exact 2x2 scalar-barrier / interval-method audit
#176 fixed-unit q13/Q14 enclosure agreement + method-selection benchmark
#178 complete fixed-unit physical-L derivative implementation + Q14 derivative discrimination
#180 exact-center Q14 derivative basin + Schur H1-scope audit
#186 coordinate-correct production remainder-drift falsifier
```

#180 supplies the frozen minimum-oriented derivative panel. #186 reuses it and tests

```text
dP/dL = -E/L + dR/dL.
```

The result is:

```text
DOMINATION_SIGNAL_MIXED

positive margin:
  det_left_o2^-10_r2^-13
  det_left_o2^-13_r2^-16

negative margin:
  det_right_o2^-10_r2^-13
  det_right_o2^-13_r2^-16
  det_left_o2^-16_r2^-19
  det_right_o2^-16_r2^-19

unresolved primary exact centers: none
finite-width scope: FINITE_WIDTH_OUT_OF_H1_SCOPE
```

The simple universal production-remainder domination formulation is therefore falsified in the tested frozen scope. This does not invalidate #184's conditional theorem and does not produce a general opposite-sign theorem.

## Current route

### Research lane

Freeze the #186 panel and search for a canonical/theorem-connectable discriminator explaining the 2-positive / 4-negative split. Do not fit arbitrary labels or move the centers.

Candidate diagnostics should come from existing production geometry: `E`, `R_L'`, `rho_L`, `P_L'`, `a`, `|b|`, `d`, normalized coupling/norm balances, fixed-Q position, the #180 basin coordinate, and opposite-parity/ancestry controls.

Reject any candidate that merely restates margin sign or successor positivity, depends on arbitrary normalization, fails controls, or requires interval H1 where H1 is not certified.

### Formal lane

Use the already-proved frozen complex source remainder holomorphy to obtain the actual N2 scalar derivative witnesses through parity projection and canonical predecessor/shell pairings. Instantiate #184 as an actual production `HasDerivAt` Schur theorem, but keep this interface sign-neutral.

Only if the mixed-split audit identifies a real selector should the project formulate a narrower contact-local remainder domination theorem.

A contradiction still additionally requires an independently theorem-backed incompatible first-bad property on the **same** retained state/aperture/parity/normalization/production object.

## Normalization / coordinate warning

The q13 research integer shell generator spans the same one-dimensional shell as Lean's canonical cubic shell but is not theorem-identified with the same magnitude. Formal production should stay on the canonical intrinsic shell.

Also `d/dt = L*d/dL` for `t=log L`; do not compare derivative magnitudes across those coordinates without the factor.

## Claim firewall

- theorem authority remains #184 for the exact statements Lean proved;
- latest research evidence advances to #186 only as rigorous finite research evidence;
- Control-v2 semantic authority remains #117;
- `DOMINATION_SIGNAL_MIXED` is a successful falsification disposition, not theorem promotion;
- finite-width scope remains outside certified H1;
- #184's algebraic drift split remains valid but its universal arithmetic premise is not established;
- global Schur monotonicity remains quarantined;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**
