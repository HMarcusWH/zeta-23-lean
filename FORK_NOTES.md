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
merged research PR = #180
validated research head = a87469da9e611b53ae400cb4b18ce4afeb94e6d2
merged research commit = 93ea3df51f2671e316197c1530ea504dee76e821
research tree = 8199cdc543f1b761c70466dfd602c143a277e6a2
RHRC #1077 = SUCCESS
Lean #837 = SUCCESS
Permansson #850 = SUCCESS

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

The production-facing Schur correction is now the genuine Hermitian form

```text
P = d - |b|^2/a.
```

The exact frozen production family is theoremized on logarithmic coordinate `t` as

```text
M~(t) = -t I + R~(t),
```

with fixed-cell equality to `parityCompressedCanonical`. For the N2/K3 intrinsic geometry, Lean proves the canonical cubic shell is nonzero, predecessor and shell reconstruct the successor, and predecessor is orthogonal to shell.

Under the required scalar derivative data, Lean proves

```text
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
```

and

```text
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0.
```

This closes the production/Hermitian/log-cover algebraic interface.

It does **not** yet assemble the actual source-specific real remainder scalar derivative witnesses from existing complex holomorphy, prove the domination inequality, establish contact existence/uniqueness or the opposing first-bad contact orientation, first-bad exclusion, negative-root exclusion or RH.

## Research packages through #180

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
```

The current finite result remains:

```text
POINT_DERIVATIVE_BASIN_BRACKETED
MINIMUM_ORIENTED
left centers: 3/3 Delta_2' < 0
right centers: 3/3 Delta_2' > 0
SCHUR_OUT_OF_H1_SCOPE on nonzero-width primary Schur boxes
applicable_primary_count = 0
```

## Current route

### Research falsification lane

#184 uses `t=log L`, while #178/#180 differentiate in physical `L`. The correct conversion is

```text
dP/dL = -envelopeNormSq/L + remainder_drift_L.
```

Reuse the exact frozen #180 states and report

```text
universal drift = -E/L
remainder drift
margin = E/L - remainder drift
ratio = L*remainder drift/E
```

before investing in the source-specific domination proof.

### Formal Pair-A lane

Use the already-proved frozen complex source remainder holomorphy to obtain the actual N2 scalar derivative witnesses through parity projection and canonical predecessor/shell pairings. Then instantiate #184 as an actual production `HasDerivAt` Schur theorem and only then attack the contact-local remainder domination bound.

A contradiction additionally needs an independently theorem-backed incompatible first-bad contact orientation on the **same** retained state.

## Normalization / coordinate warning

The q13 research integer shell generator spans the same one-dimensional shell as Lean's canonical cubic shell but is not theorem-identified with the same magnitude. Formal production should stay on the canonical intrinsic shell.

Also `d/dt = L*d/dL` for `t=log L`; do not compare derivative magnitudes across those coordinates without the factor.

## Claim firewall

- theorem authority advances to #184 only for the exact statements Lean proved;
- research authority remains #180 for the latest finite evidence;
- Control-v2 semantic authority remains #117;
- `SCHUR_OUT_OF_H1_SCOPE` is not a sign theorem;
- #184's algebraic drift split is not a source-specific arithmetic domination theorem;
- analyticity is not a derivative magnitude bound;
- global Schur monotonicity remains quarantined;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**
