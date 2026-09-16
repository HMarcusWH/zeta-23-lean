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
merged research PR = #193
validated research head = 085634ca7dafe4d9f598b2b5e081be80e050ba8c
merged research commit = fdd6606f85e92bf632b4cdaf1d4af85f6fa5b195
validated research tree = db569150046459f4b87a931d3e8d01054bbbedff
RHRC #1109 = SUCCESS
Permansson #882 = SUCCESS
post-190 canonical realizability audit #5 = SUCCESS
post-192 parity trajectory rigidity #3 = SUCCESS
research disposition = TRAJECTORY_RIGIDITY_UNRESOLVED
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
post-#163 onward frozen research regressions through #193
R004 scalar-shift invariant audit
external-reference dependency firewall
lake build Zeta23.CCM
lake build Zeta23.ExceptionalZero
forbidden sorry / project axiom scan
Permansson independent formal verification
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

## Research evidence through #193

### #190 ambient selector evidence

The exact rational research tooling certifies `JOINT_EXACT_VECTOR_SEPARABLE` and `JOINT_THRESHOLD_SIGNATURE_SEPARABLE`. This is exact executable research in the ambient normalized model, not a canonical-state theorem.

### #192 canonical-realizability evidence

Use these classifications exactly:

```text
EXACT_TWIN_EXCLUDED_BY_IDENTITY
  only when a declared exact production identity excludes the object

EXACT_TWIN_SURVIVES
  only for an exact constructed model

UNRESOLVED
  for bounded production replay without an exact conclusion
```

#192 excludes the specific negative-scalar #190 witness after the exact scalar-aperture identity is imposed. Its positive-scalar adversarial control survives that identity. Later bounded production layers remain `UNRESOLVED` for the general reflected class. The six-state 0/15 seven-vector overlap count is finite structural evidence only.

### #193 trajectory evidence

The inherited exact-center P1/P2/J cross-checks use signed Arb point balls. The six exact centers with `e>0`, `o>0`, `J>0`, `P2>0` are therefore rigorous **point research** for those encoded states.

Evidence classes:

```text
exact signed center Arb balls
  -> RIGOROUS POINT RESEARCH

complete signed finite-width Arb cover
  -> RIGOROUS BOUNDED MONOTONICITY RESEARCH

six signed centers with unresolved interval cover
  -> EXPERIMENTAL/FINITE STRUCTURAL SIGNAL only;
     not monotonicity

budget exhaustion / unresolved dependency graph
  -> UNRESOLVED
```

Mandatory firewall:

```text
6/6 J>0 at centers  !=  J>0 on hull
```

#193's actual finite-width classification is `TRAJECTORY_RIGIDITY_UNRESOLVED`, with 63/96 `H1_UNRESOLVED`, 33/96 `J_UNRESOLVED`, zero `J_NEGATIVE` cells and zero `J_POSITIVE` cells. This does not establish a fold or falsify monotonicity.

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

floating/numerical discovery
  -> EXPERIMENTAL SIGNAL

search fails / interval graph remains unresolved
  -> UNRESOLVED, not proof
```

In particular:

- ambient normalized algebra is not identical to the image of canonical arithmetic production;
- exact selector separability is not canonical-state separability;
- finite Arb certification is not a global theorem;
- exact-center signs do not determine the signs of neighborhoods;
- `UNRESOLVED` is neither positive nor negative mathematical evidence;
- a green falsification/nonresolution run may still be a successful validation run.

## Post-#193 validation rule

The next trajectory experiment must preserve the identical frozen Q14 hull, inherited centers, Q/N/K/parity and target-label firewall while changing the **representation**, not silently the research population.

Compare predeclared representations such as:

```text
#193 first-order Wronskian enclosure
direct P2 log-slope enclosure
centered second-order/Taylor enclosure
```

A claim of bounded `J>0` requires a complete signed finite-width cover. Point samples, overlap absence, or budget-limited unresolved cells cannot be upgraded to monotonicity.

## Claim firewall

- theorem authority remains #184;
- research authority advances through #193 only in the evidence classes stated above;
- Control-v2 remains non-authoritative;
- no research certificate may write terminal RH status;
- canonical general reflected-twin exclusion remains OPEN;
- `J>0` on the Q14 hull remains OPEN;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**
