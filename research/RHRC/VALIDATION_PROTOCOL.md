# RHRC validation protocol

> **Claim firewall: RH remains OPEN.**

This document defines what "green", "proved", "validated" and "promoted" mean in this repository.

## Exact object first

For every theorem-bearing PR record the base, exact PR head checked by GitHub Actions, theorem tree, merged theorem-bearing commit/tree and relevant compiler/toolchain evidence. Compiler validity attaches only to the exact checked object.

For research-only PRs, record the exact research head/merge and CI evidence separately. A green research PR validates that its executable checks ran as specified; it does not convert symbolic/numerical/Arb research output into Lean theorem authority. A falsification disposition can be mathematically negative while the PR is correctly green.

## Authority classes

### Theorem authority

```text
latest theorem-bearing PR = #184
validated theorem head = a756494ebe7e2530715e996b9a9a341fbe07c683
merged theorem commit = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e
validated theorem tree = 6c77cd470809959a403b3bcc5f08d39f4076fa4c
RHRC #1089 = SUCCESS
Permansson #862 = SUCCESS
```

### Latest research-evidence anchor

```text
merged research PR = #186
validated research head = 7d277a99437d98fdb7c831f25a130eac07f1b3af
merged research commit = 0494658a87d29eeb2124aa16232c264c21d23c18
RHRC #1091 = SUCCESS
Permansson #864 = SUCCESS
research disposition = DOMINATION_SIGNAL_MIXED
```

### Control authority

```text
control-plane anchor = PR #117
merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
```

Theorem, research and control anchors are deliberately separate.

## Authoritative repository gates

Current theorem/claim gates include:

```text
python research/RHRC/tools/run_suite.py
R003 normalization audit / dictionary guards / source-normalization firewall
post-#163 onward frozen research regressions, including #186 remainder-drift falsification
R004 scalar-shift invariant audit
external-reference dependency firewall
lake build Zeta23.CCM
lake build Zeta23.ExceptionalZero
forbidden sorry / project axiom scan
Permansson independent formal verification
```

A skipped downstream step is not a passed gate. Control-v2 regression tests guard routing semantics only; they do not grant theorem authority.

## Exact #184 theorem evidence

PR #184 validated the exact head

```text
a756494ebe7e2530715e996b9a9a341fbe07c683
```

with theorem tree

```text
6c77cd470809959a403b3bcc5f08d39f4076fa4c
```

and was merged as

```text
6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e.
```

The modules `Zeta23/CCM/HermitianSchurEnvelopeDerivative.lean` and `Zeta23/CCM/FrozenN2SchurLogDrift.lean` are imported by `Zeta23/CCM.lean`, so the successful aggregate CCM build compiler-validates their declarations. The same workflow built `Zeta23.ExceptionalZero` and ran the forbidden-placeholder scan over the promoted CCM/ExceptionalZero subtrees. Permansson #862 independently completed successfully.

Validated mathematical content includes:

```text
Hermitian 2x2 Schur pivot/determinant identities with |b|^2/a
real-component HasDerivAt theorems for the complex off-diagonal coordinate
contact-local determinant/pivot derivative sign transfer under H1
full frozen parity production family on logarithmic cover
M~(t) = -t I + R~(t)
fixed-cell equality with parityCompressedCanonical
log-cover deck-translation law
N2 predecessor/shell reconstruction
nonzero canonical cubic shell
predecessor-shell orthogonality
algebraic P_t' = -envelopeNormSq + remainderEnvelopeDerivative
conditional negative orientation when remainder drift < envelopeNormSq
```

Operational interpretation:

```text
PROVED / #184
  complex-Hermitian contact calculus
  normalization-safe production log-cover family
  exact fixed-cell production attachment
  N2/K3 intrinsic predecessor-shell geometry
  algebraic universal-negative-drift/remainder split
  conditional negative-orientation criterion

NOT PROVED / #184
  actual source-specific real remainder-coordinate derivative witnesses
  fully instantiated production HasDerivAt N2 Schur identity
  source-specific remainder domination
  contact existence or uniqueness
  required first-bad crossing orientation on the same retained state
  finite-width H1 on the Q14 boxes
  global Schur monotonicity
  first-bad exclusion
  negative-root exclusion
  RH
```

## Exact #186 research evidence

PR #186 validated the exact research head

```text
7d277a99437d98fdb7c831f25a130eac07f1b3af
```

and was merged as

```text
0494658a87d29eeb2124aa16232c264c21d23c18.
```

RHRC #1091 and Permansson #864 completed successfully.

The research certificate reuses the exact frozen #180 q13/Q14 N2/K3/even schedule and checks the physical-aperture decomposition

```text
P_L' = -E/L + R_L'
margin_L = E/L - R_L'
rho_L = L*R_L'/E.
```

The primary exact-center disposition is:

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

Interpretation:

```text
RIGOROUS FINITE RESEARCH CERTIFICATION / #186
  exact encoded frozen states
  exact-center H1 checks required by the certificate
  internal algebraic/enclosure consistency checks
  mixed domination-margin disposition

NOT THEOREM PROMOTION / #186
  no Lean source-specific domination theorem
  no general opposite-sign theorem
  no contact existence/orientation theorem
  no negative-root exclusion
  no RH
```

The fact that #186 is green means the falsifier executed faithfully. It does **not** mean the tested hypothesis survived. The tested broad formulation did not survive: four of six primary exact centers certify negative domination margin.

## Research evidence interpretation law

```text
research gate green
  -> executable research check is validated on the exact head
  -/-> Lean theorem
  -/-> global sign theorem
  -/-> whole-cell theorem
  -/-> universal arithmetic-entry sign
  -/-> RH.
```

In particular:

- exact SymPy/algebraic identities are **EXACT EXECUTABLE**, not Lean theorem authority;
- floating discovery is **EXPERIMENTAL SIGNAL**;
- deterministic numerical checks are implementation evidence only;
- Arb pointwise replay is **RIGOROUS FINITE CERTIFICATION** only;
- Arb interval output is a rigorous enclosure only for the exact encoded interval expression;
- Arb central finite differences are finite-difference enclosures, not derivative theorems;
- `UNRESOLVED` is neither positive nor negative evidence;
- a green falsification PR may return `MIXED` or `FAILS` and still be a successful validation run;
- absence of a finite negative candidate is not a positivity theorem.

## Inherited #180 research evidence

The #186 schedule descends from #180. At all six frozen primary Q14 exact centers, #180 rigorously certified

```text
POINT_DERIVATIVE_BASIN_BRACKETED
MINIMUM_ORIENTED
left centers:  3/3 Delta_2' < 0
right centers: 3/3 Delta_2' > 0
```

For the nonzero-width primary boxes:

```text
SCHUR_OUT_OF_H1_SCOPE
applicable_primary_count = 0
```

#186 does not change that finite-width H1 classification; its own finite-width result is `FINITE_WIDTH_OUT_OF_H1_SCOPE`.

## Current FB-05 validation target after #186

The next research target is **not** to prove the now-falsified broad domination hypothesis. It is to explain the mixed exact-center split on the unchanged frozen panel and look for a canonical, theorem-connectable selector condition.

Any candidate selector must be predeclared before outcome inspection and tested against:

```text
same frozen centers
normalization invariance / canonical normalization
opposite-parity and ancestry controls
no target leakage from margin/rho/successor positivity
same-state composition requirement
finite-width H1 scope where intervals are used
```

The next formal target may still be a sign-neutral transport of existing complex frozen-source remainder holomorphy through parity projection and N2 predecessor/shell scalar pairings to actual real derivative witnesses and an instantiated production `HasDerivAt` Schur identity.

Only after a narrower arithmetic condition survives research falsification should a source-specific sign inequality become theorem work.

## Production normalization and coordinate firewall after #184/#186

The finite q13 research code uses exact integer `W,c` coordinates. Its shell generator spans the same one-dimensional shell as Lean's canonical cubic shell but is not theorem-identified at the same magnitude. Formal production uses the canonical intrinsic cubic shell and complex Hermitian geometry.

Coordinate law:

```text
#184 theorem coordinate: t = log L
  dP/dt = -E + dR/dt

#178/#180/#186 research coordinate: physical L
  dP/dL = -E/L + dR/dL
```

Therefore:

```text
research W/c coordinates
  -/-> formal canonical shell coordinates by definitional equality

log-coordinate derivative d/dt
  -/-> physical-aperture derivative d/dL without the factor L

analyticity of the remainder
  -/-> domination of its derivative magnitude

mixed finite domination signal
  -/-> a general opposite-sign theorem
```

## Axiom inspection

The accepted production foundation remains the compiler-reported Mathlib foundations; no production theorem may depend on `sorryAx` or a promoted project axiom. The authoritative workflow rejects `sorry` and top-level `axiom` declarations in the promoted CCM/ExceptionalZero subtrees.

Research Python/SymPy/Arb tooling has no authority to alter this axiom surface.

## What remains outside theorem authority

```text
explicitCanonicalSourceMoment != 0 -> M4 != 0
M4 != 0 -> explicitCanonicalSourceMoment != 0
finite production samples determine the seventh jet at zero
canonicalPolePrimeRieszEndpointScalar L 8 >= 0
canonicalPolePrimeRieszEndpointScalar L 8 != 0
actual N2 production remainder scalar derivative witnesses
actual production HasDerivAt Schur log-drift identity
any valid narrowed source-specific contact-orientation bound
first-bad contact existence/orientation composition on the same retained state
centered finite-width H1 on frozen Q14 boxes
q13/N2/K3/even whole-cell strict positivity / nonvanishing / contact classification
simultaneous even/odd bad exclusion
odd-selected first-bad branch reduction/closure
independent contradiction-producing complete arithmetic restriction
negative-root exclusion
outside-strip/trivial-zero terminal seam
RiemannHypothesis
```

## Import/build closure law

A `.lean` file existing in the repository, appearing in a PR, passing syntactic no-placeholder checks or being merged does not establish that its declarations elaborate. A declaration becomes compiler-validated theorem authority only when its module lies in an exact successful authoritative build closure or is explicitly built by such a gate.

## Proof versus promotion

For R003 `PROVED_UNCONDITIONAL`, theorem names must agree across

```text
CLAIM_REGISTRY.json
R003_PROMOTED_BINDINGS.json
Zeta23/CCM/ClaimBindings.lean
```

PR #186 is research-only and does not alter those machine claim-promotion surfaces.

## Vocabulary

- **source present** — file exists;
- **module compiles** — Lean elaborated that module;
- **umbrella build green** — named target and transitive imports compiled;
- **PR green** — all required gates for the exact PR object succeeded;
- **PROVED** — exact statement compiler-validated with acceptable axiom surface;
- **PROVED_UNCONDITIONAL** — proved theorem additionally registered on the production claim surface;
- **DERIVED** — mathematical consequence not separately theorem-locked;
- **LOCAL LEAN CHECK** — standalone/local compilation outside merged theorem authority;
- **EXACT EXECUTABLE** — symbolic/executable identity locked by research tooling, not Lean theorem authority;
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only;
- **RIGOROUS FINITE CERTIFICATION** — Arb/interval statement in the exact finite scope only;
- **LEAD / HYPOTHESIS** — motivated research route;
- **OPEN** — not established.

## Claim firewall

Green #184 Hermitian/log-drift structure is not a source-specific arithmetic domination theorem. Green #186 research evidence is not theorem promotion, and its `DOMINATION_SIGNAL_MIXED` disposition specifically blocks pretending that the broad source-remainder domination clue survived. A contradiction still requires a genuinely independent canonical restriction on the exact retained state, a same-state incompatible first-bad property, negative-root exclusion and the terminal zeta/Mathlib seam.

**RH remains OPEN.**
