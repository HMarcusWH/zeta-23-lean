# RHRC validation protocol

> **Claim firewall: RH remains OPEN.**

This document defines what "green", "proved", "validated" and "promoted" mean in this repository.

## Exact object first

For theorem-bearing PRs, compiler validity attaches only to the exact checked head/tree and its successful import closure. For research-only PRs, record exact head/merge/tree and CI evidence separately. A green research PR validates faithful execution; it does not convert executable algebra, numerical output or Arb certification into Lean theorem authority.

## Authority classes

### Theorem authority

```text
latest theorem-bearing PR = #184
validated theorem head = a756494ebe7e2530715e996b9a9a341fbe07c683
merged theorem commit = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e
validated theorem tree = 6c77cd470809959a403b3bcc5f08d39f4076fa4c
```

### Latest research-evidence anchor

```text
merged research PR = #197
validated research head = 2d936f9764abdfeaa82127d5c834c6c3e429da25
merged research commit = 162df6ce8bc13a816937d747f2965bff6764fad0
validated research tree = 97f6372a4c7c131006b4abc090c86767b9e99990
research disposition = GLOBAL_MONOTONE_ORIENTATION
```

### Control authority

```text
control-plane anchor = PR #117
merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
```

Theorem, research and control anchors are deliberately separate.

## Authoritative repository gates

Current gates include:

```text
python research/RHRC/tools/run_suite.py
Control-v2 real-history smoke run
R003 normalization/dictionary/source-normalization guards
post-#163 onward frozen research regressions through #197
R004 scalar-shift invariant audit
external-reference dependency firewall
lake build Zeta23.CCM
lake build Zeta23.ExceptionalZero
forbidden sorry / project axiom scan
Permansson independent formal verification
post-190 canonical realizability regression
post-192 parity-trajectory regression
post-194 sharp trajectory / second-derivative regression
post-#196 / #197 Q14 residual-cell replay regression
```

A skipped downstream step is not a passed gate.

## Exact #184 theorem evidence

PR #184 remains the latest Lean-bearing authority. Validated mathematical content includes:

```text
Hermitian 2x2 pivot/determinant identities with |b|^2/a
real-component HasDerivAt calculus
contact-local determinant/pivot derivative sign transfer under H1
full frozen parity production family on logarithmic cover
fixed-cell equality with parityCompressedCanonical
N2 predecessor/canonical-shell reconstruction and orthogonality
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
remainder drift < envelopeNormSq -> negative pivot orientation
```

Not proved by #184: actual source-specific remainder derivative witnesses, source-specific domination, contact existence/uniqueness, opposing first-bad orientation, negative-root exclusion or RH.

## Research evidence through #197

### #186 / #190 / #192 historical constraints

PR #186 returns `DOMINATION_SIGNAL_MIXED`. PR #190 establishes `JOINT_EXACT_VECTOR_SEPARABLE` and `JOINT_THRESHOLD_SIGNATURE_SEPARABLE` for the complete frozen selector vector in ambient normalized algebra. PR #192 executes the canonical production realizability ladder, excludes the specific negative-scalar witness under an exact identity, and leaves the general reflected class `UNRESOLVED`.

### #193 trajectory evidence

The first-order finite-width classification is:

```text
TRAJECTORY_RIGIDITY_UNRESOLVED
63/96 H1_UNRESOLVED
33/96 J_UNRESOLVED
0 J_NEGATIVE
0 J_POSITIVE
```

This is historical method evidence, not a fold theorem.

### #195 second-order trajectory evidence — historical bounded partial state

```text
PARTIAL_TRAJECTORY_ORIENTATION
48 J_POSITIVE
48 J_UNRESOLVED
0 J_NEGATIVE
0 H1_UNRESOLVED
second_order_h1_recovery_count = 63
representation_conflict_count = 0
unresolved_span_count = 1
certified_t_fraction = 63/64
uniform_orientation = null
global_positive_hull = false
bounded_distinct_aperture_twin_exclusion = false
```

Interpretation law:

```text
63/64 positive parameter coverage
  -> RIGOROUS BOUNDED PARTIAL ORIENTATION RESEARCH
  -/-> complete signed hull
```

### #197 residual-cell replay — complete bounded state

PR #197 reruns #195 unchanged, identifies exactly one inherited `MAX_CELL_BUDGET` sentinel of width `1/64` of the hull, and evaluates that exact cell once.

```text
A = J_UNRESOLVED
B = J_POSITIVE
C = J_POSITIVE
replayed_cell_orientation = J_POSITIVE
completed_classification = GLOBAL_MONOTONE_ORIENTATION
uniform orientation = J_POSITIVE
unresolved span count = 0
certified_t_fraction = 1
full_hull_signed_monotonicity = true
global_positive_hull = true
bounded_distinct_aperture_twin_exclusion = true
```

This is a **complete signed Arb interval cover**, so the evidence class is:

```text
RIGOROUS BOUNDED RESEARCH
```

It is not a Lean theorem and does not promote theorem authority beyond #184.

## Evidence interpretation law

```text
Lean compiler + authoritative import closure
  -> PROVED for the exact theorem statement

exact rational identity/countermodel in research tooling
  -> EXACT EXECUTABLE RESEARCH

Arb signed point certificate
  -> RIGOROUS POINT RESEARCH for the encoded state

complete signed Arb interval cover
  -> RIGOROUS BOUNDED RESEARCH for the encoded domain

partial signed cover with explicit unresolved spans
  -> RIGOROUS BOUNDED PARTIAL RESEARCH only

floating/numerical discovery
  -> EXPERIMENTAL SIGNAL

search fails / interval graph remains unresolved
  -> UNRESOLVED, not proof
```

In particular:

- ambient normalized algebra is not identical to the image of canonical arithmetic production;
- finite Arb certification is not a global theorem;
- exact-center signs do not determine neighborhood signs;
- a bounded complete cover does not determine arbitrary Q or arbitrary retained states;
- a green falsification/nonresolution run may still be a successful validation run.

## Post-#197 validation rule

The bounded Q14 sign-recovery problem is complete. Future trajectory research should **not** present another refinement of the same already-complete cover as progress unless it changes mathematical mechanism.

The preferred next experiment may inspect

```text
J' = o''e - e''o
```

through canonical pole/arch/prime source channels. Because this object is bilinear, all cross-channel terms must be retained. Any source decomposition must rigorously reconstruct the independently evaluated direct canonical total before a dominance claim is accepted.

Permitted mechanism outcomes include stable single-channel dominance, stable cross-channel interaction, cancellation-dominated behavior, or mechanism unresolved. A mathematically negative result can still be a green validation result if the executable conclusion matches the evidence.

Any later claim of a general parity-ordering theorem requires a theorem-backed source premise on the intended class; the frozen #197 cover is not such a theorem.

## Claim firewall

- theorem authority remains #184;
- research authority advances through #197 only in the evidence classes stated above;
- Control-v2 remains non-authoritative;
- no research certificate may write terminal RH status;
- historical #195 `PARTIAL_TRAJECTORY_ORIENTATION` / `63/64` remains preserved;
- #197 `GLOBAL_MONOTONE_ORIENTATION` is rigorous bounded research on one frozen Q14 domain;
- `global_positive_hull = true` does not establish global canonical injectivity or FB-05;
- bounded distinct-aperture twin exclusion does not exclude all canonical reflected twins;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**