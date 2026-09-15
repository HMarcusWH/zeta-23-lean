# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

```text
THEOREM AUTHORITY
latest theorem-bearing PR = #182
validated theorem head = 0c3f63cdc4774ba1a68b21d1558ea0ee860a938d
merged theorem commit = a69160d37a84049711aaff6c3d5db804583a7306
validated theorem tree = e0b260b3b3a1ed470d54c14d8c0c46b32379f3fb
RHRC #1082 = SUCCESS
Permansson #855 = SUCCESS

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
```

## What #182 adds

`Zeta23/CCM/SchurEnvelopeDerivative.lean` is inside the aggregate CCM build. It theoremizes

```text
Delta_2 = aP
P' = d' - 2*(b/a)b' + (b/a)^2 a'
Delta_2' = a'P + aP'
```

and proves that at contact `P=0`,

```text
Delta_2' = aP'.
```

Under H1 `a>0`, determinant and pivot derivative orientations agree.

This is generic calculus. It does not establish contact existence, production arithmetic sign, finite-width H1, global Schur monotonicity, first-bad exclusion, negative-root exclusion or RH.

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
#178 complete fixed-unit derivative implementation + Q14 derivative discrimination
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

### Finite lane

Recover H1 by centered propagation from `a(L0)>0` and rigorous `a'(I)`. Only then retry the Schur derivative representation. Add `Delta_2''` and interval Newton/Krawczyk only if the cheaper gates succeed and still leave sign unresolved.

### Formal Pair-A lane

Use the already-proved fixed-cell source decomposition

```text
M_Q(L) = -log(L) I + R_Q(L)
```

together with #182 to theoremize a normalization-safe production/Hermitian Schur-envelope derivative. The target universal term is

```text
-||u_L||^2/L,
```

with all difficult arithmetic isolated in an exact production remainder derivative. Then seek/falsify a source-specific contact-local bound producing an orientation incompatible with first-bad crossing.

## Normalization warning

The q13 research integer shell generator spans the same one-dimensional shell as Lean's canonical cubic shell but is not theorem-identified with the same magnitude. Formal production is complex Hermitian while #182 is real 2x2. Do not silently identify those coordinate systems.

## Claim firewall

- theorem authority advances to #182 only for the exact generic statements Lean proved;
- research authority remains #180 for the latest finite evidence;
- Control-v2 semantic authority remains #117;
- `SCHUR_OUT_OF_H1_SCOPE` is not a sign theorem;
- generic contact orientation is not a production arithmetic sign;
- global Schur monotonicity remains quarantined;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**
