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
merged research PR = #199
validated research head = fabe301c95277345f0efe764252ce1c1213a4112
merged research commit = 27dda545b7ccdb2870088ebaf317d85e3d999555
validated research tree = 85eb8ea25d240c4a9c339262bdc611fae881f7f0
research disposition = SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED
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
post-#163 onward frozen research regressions through #199
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
post-#198 / #199 Q14 source-mechanism regression
```

A skipped downstream step is not a passed gate.

## Exact #184 theorem evidence

PR #184 remains the latest Lean-bearing authority. Validated mathematical content includes Hermitian 2x2 pivot/determinant identities, contact-local derivative sign transfer under H1, the full frozen parity production family, the fixed-cell bridge, N2 predecessor/canonical-shell reconstruction and

```text
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
remainder drift < envelopeNormSq -> negative pivot orientation.
```

Not proved by #184: actual source-specific remainder derivative witnesses, source-specific domination, contact existence/uniqueness, opposing first-bad orientation, negative-root exclusion or RH.

## Research evidence through #199

### #186 / #190 / #192 historical constraints

PR #186 returns `DOMINATION_SIGNAL_MIXED`. PR #190 establishes joint selector separability for the complete frozen selector vector in ambient normalized algebra. PR #192 executes the canonical production realizability ladder, excludes the specific negative-scalar witness under an exact identity, and leaves the general reflected class `UNRESOLVED`.

### #193 trajectory evidence

The first-order finite-width classification is `TRAJECTORY_RIGIDITY_UNRESOLVED` with 63/96 H1-unresolved and 33/96 J-unresolved cells. This is historical method evidence, not a fold theorem.

### PR #195 second-order trajectory evidence — historical bounded partial state

The mechanism-facing differential identity preserved from this stage is

```text
J' = o''e - e''o
```

and the historical exact result is:

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

### PR #197 residual-cell replay — complete bounded state

```text
A = J_UNRESOLVED
B = J_POSITIVE
C = J_POSITIVE
completed_classification = GLOBAL_MONOTONE_ORIENTATION
uniform orientation = J_POSITIVE
unresolved span count = 0
certified_t_fraction = 1
full_hull_signed_monotonicity = true
global_positive_hull = true
bounded_distinct_aperture_twin_exclusion = true
```

This is a **complete signed Arb interval cover**, so the evidence class is `RIGOROUS BOUNDED RESEARCH`. It is not a Lean theorem and does not promote theorem authority beyond #184.

### PR #199 source-mechanism audit — representation nonresolution

PR #199 must replay the exact #197 complete positive cover before any mechanism interpretation. It validates the four-way second-aperture source split and collapsed direct-production representation, then requires source-interaction reconstructions to overlap independent direct Method C on every primary and control cell.

Final output:

```text
mechanism_classification = SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED
four_way_classification = SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED
collapsed_three_way_classification = SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED
selected_collapsed_uniform_lock_group = null
control_transfer_status = NO_UNIQUE_COLLAPSED_UNIFORM_LOCK
```

Evidence interpretation:

```text
direct Method-C J is rigorously positive
+
source-separated interval reconstruction loses sign resolution

=> current source attribution graph is dependency-unresolved
-/-> direct J lost positivity
-/-> no source mechanism exists
-/-> Q14 ordering falsified
```

This distinction is permanent validation law: an unresolved decomposition cannot downgrade an independently certified correlated quantity when exact reconstruction overlap has been checked.

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

source-decomposition loses sign while direct correlated evaluator remains signed
  -> SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED
  -> representation limitation, not sign reversal
```

In particular:

- ambient normalized algebra is not identical to the image of canonical arithmetic production;
- finite Arb certification is not a global theorem;
- exact-center signs do not determine neighborhood signs;
- a bounded complete cover does not determine arbitrary Q or arbitrary retained states;
- a green falsification/nonresolution run may still be a successful validation run;
- regrouping already-enclosed intervals does not recover cancellation lost before enclosure.

## Post-#199 validation rule

The bounded Q14 sign-recovery problem and the first independent source-mechanism audit are both consumed.

The next experiment may use the theorem-motivated cancellation-preserving representation

```text
D = pole + prime_signed
A = direct_arch_signed
M = D + A
```

but the pairing must be performed at source/matrix jet level before parity restriction and interval transport. Merely adding already-enclosed pole and prime interaction intervals is not a new dependency graph.

The new representation must use the exact inherited #197 leaf partition and direct Method-C comparator unless a separately documented reason changes scope. No new Q/N/K/parity search, precision increase, adaptive budget increase, target-label import, or control-informed mechanism selection should be allowed merely to rescue the hypothesis.

Any later claim of a general parity-ordering theorem requires a theorem-backed source premise on the intended class; neither the frozen #197 cover nor the #199 representation diagnosis is such a theorem.

## Claim firewall

- theorem authority remains #184;
- research authority advances through #199 only in the evidence classes stated above;
- Control-v2 remains non-authoritative;
- no research certificate may write terminal RH status;
- historical PR #195 `PARTIAL_TRAJECTORY_ORIENTATION` / `63/64` remains preserved;
- #197 `GLOBAL_MONOTONE_ORIENTATION` remains rigorous bounded research on one frozen Q14 domain;
- #199 `SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED` does not weaken #197 direct `J_POSITIVE`;
- bounded distinct-aperture twin exclusion does not exclude all canonical reflected twins;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**