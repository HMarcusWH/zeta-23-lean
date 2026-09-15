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
merged research PR = #190
validated research head = 8701920b0da18ae6595ad0eee55c1f6cb291a94f
merged research commit = f87da9fde71dd1e74419c6ae5848eee3787c27e4
validated research tree = af8774b65c898de221a5bf32977ccff3407a7b2d
RHRC #1096 = SUCCESS
Permansson #869 = SUCCESS
research disposition = JOINT_EXACT_VECTOR_SEPARABLE / JOINT_THRESHOLD_SIGNATURE_SEPARABLE
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
post-#163 onward frozen research regressions through #190
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

## Exact research progression #186 -> #190

### #186 — rigorous finite falsification

The exact frozen Q14 panel certifies `DOMINATION_SIGNAL_MIXED`. This kills the broad universal domination proposal in the tested finite scope while leaving #184's conditional theorem intact.

### #188 — rigorous finite selector audit

The frozen schedule and normalization firewalls are retained. Seven strong-eligible selectors and three diagnostic mechanism components are audited without target leakage or threshold fitting.

### #189 — exact executable individual independence

For each frozen selector separately, the exact rational audit constructs ambient states with identical candidate value and threshold relation but opposite target sign. This is exact executable algebra, not a Lean theorem and not a canonical-realizability result.

### #190 — exact executable joint independence

The complete seven-dimensional strong selector vector is identical across an exact rational pair, with the same nonboundary threshold signature and opposite normalized target signs. The certified dispositions are:

```text
JOINT_EXACT_VECTOR_SEPARABLE
JOINT_THRESHOLD_SIGNATURE_SEPARABLE
```

The same witness closes all `2^7 - 1 = 127` nonempty coordinate subsets. Positive target-alias controls still distinguish the pair.

PR #190 explicitly keeps:

```text
theorem_promotion = false
canonical_realizability_claimed = false
fb05_closed = false
negative_root_exclusion = false
rh_claim = false
```

## Evidence interpretation law

```text
Lean compiler + authoritative import closure
  -> PROVED for the exact theorem statement

exact rational identity/countermodel in research tooling
  -> EXACT EXECUTABLE RESEARCH

Arb point/interval certificate
  -> RIGOROUS FINITE RESEARCH for the encoded object

floating/numerical discovery
  -> EXPERIMENTAL SIGNAL

search fails to find a counterexample
  -> UNRESOLVED, not proof
```

In particular:

- ambient normalized algebra is not identical to the image of canonical arithmetic production;
- exact selector separability is not canonical-state separability;
- finite Arb certification is not a global theorem;
- `UNRESOLVED` is neither positive nor negative evidence;
- a green falsification may return `MIXED` or `SEPARABLE` and still be a successful validation run.

## Post-#190 validation rule

The next canonical-realizability audit must separate three outcomes:

```text
EXACT_TWIN_SURVIVES
EXACT_TWIN_EXCLUDED_BY_IDENTITY
UNRESOLVED
```

If an identity excludes the twin, record the exact assumptions used. If only bounded computation/search fails to find a twin, remain `UNRESOLVED`. Do not silently promote absence of a witness to nonexistence.

The production arch/scalar relation

```text
scalar_shift = 2*cCorrection'(L) I
arch_signed  = -arch_direct - scalar_shift
```

is currently executable-definition infrastructure. It becomes theorem authority only if separately formalized in the validated Lean closure.

## Claim firewall

- theorem authority remains #184;
- research authority advances to #190 only in the evidence class stated above;
- Control-v2 remains non-authoritative;
- no research certificate may write terminal RH status;
- canonical realizability remains OPEN;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**