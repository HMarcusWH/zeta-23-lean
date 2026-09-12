# RHRC validation protocol

> **Claim firewall: RH remains OPEN.**

This document defines what "green", "proved", "validated" and "promoted" mean in this repository.

## Exact object first

For every theorem-bearing PR record the base, exact PR head checked by GitHub Actions, theorem tree, eventual merged-main commit/tree and relevant compiler/toolchain.

Compiler validity attaches only to the exact object actually checked. A control/docs-only green must not create theorem authority.

## Authoritative repository gates

Current theorem/claim gates include:

```text
python research/RHRC/tools/run_suite.py
R003 normalization audit / dictionary guards / source-normalization firewall
post-#150 selected-residual certification plumbing / scout / certificate replay
R004 scalar-shift invariant audit
external-reference dependency firewall
lake build Zeta23.CCM
lake build Zeta23.ExceptionalZero
forbidden sorry / project axiom scan
Permansson independent formal verification
```

A skipped downstream step is not a passed gate.

`run_suite.py` also executes FFBBP and Control-v2 regression tests. Those guard research-control semantics; they do not grant theorem authority to the controller.

## Current theorem/control validation anchors

```text
latest theorem-bearing PR = #155
merged theorem-bearing main = 7bd3f1028d42272fcadc347c43371b992d9c0bd7
validated theorem head = ecfd075c07923e6fc80ab1a5b4f2d49c724f5577
validated theorem tree = 9a4f21ed55aa0cbdf54527164c2f5f96912c65de
RHRC #1005 / run 34720946254 = SUCCESS
Permansson #778 / run 34720946242 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
```

The #155 validated PR head and merged main are different commit objects but share theorem tree `9a4f21ed...`. PR #117 remains the Control-v2 semantic authority because #155 changes mathematical state, not controller capability/authority semantics.

## Exact #155 gate evidence

At validated theorem head `ecfd075c07923e6fc80ab1a5b4f2d49c724f5577`, RHRC workflow run #1005 (`34720946254`) completed successfully. Permansson workflow run #778 (`34720946242`) also completed successfully.

Successful theorem-bearing closure includes:

```text
python-rhrc
r003-normalization-audit
lean
lake build Zeta23.CCM
lake build Zeta23.ExceptionalZero
forbidden placeholder/project-axiom scan
Permansson independent formal verification
```

## What #155 validates

The new #155 modules are imported through `Zeta23.CCM` and therefore lie in the authoritative aggregate build closure.

### Discrepancy integrability

Validated declarations include:

```text
intervalIntegrable_canonicalPrimeCumulativeWeight
intervalIntegrable_canonicalPoleCumulativeWeight
intervalIntegrable_canonicalPolePrimeDiscrepancy
```

The finite prime cumulative object remains a staircase; no continuity at prime-log thresholds is claimed.

### Anchored Riesz primitive API

Validated declarations include:

```text
canonicalPolePrimeRieszPrimitive
canonicalPolePrimeRieszPrimitive_zero
canonicalPolePrimeRieszPrimitive_succ_zero
intervalIntegrable_canonicalPolePrimeRieszPrimitive
absolutelyContinuousOnInterval_canonicalPolePrimeRieszPrimitive_succ
ae_deriv_canonicalPolePrimeRieszPrimitive_succ
```

Positive-order primitives are absolutely continuous and recover the previous primitive as derivative almost everywhere on the physical interval.

### Pulled-back source-energy jets / legal repeated IBP

Validated declarations include the source composed-jet regularity/chain-rule layer and the generic Riesz energy theorem

```text
canonicalPolePrimeDiscrepancyEnergy_eq_rieszEnergy
```

under explicit endpoint-jet hypotheses through the requested order.

This is a legal arbitrary-order smoothing engine. It does not itself prove those production odd jets.

### Source-coordinate parity/even jets

Validated declarations include:

```text
sourceAtomRealEnergy_neg_sourceCoordinate
iteratedDeriv_even_sourceAtomRealEnergy_zero
centeredMoment_three_eq_zero_of_even
```

Hence production source energy is odd in the source coordinate, all even endpoint derivatives at zero vanish, and even reversal parity forces `M3=0`.

## What remains outside theorem authority after #155

```text
complex production D-transport g_u''=-(2*pi)^2 g_(D u)
moment-prefix D-transport recursion
odd endpoint derivative formula
unconditional production Riesz order 6
unconditional even-parity production Riesz order 8
retained transformed-negative first-bad wrapper
sign of the complete transformed discrepancy/archimedean/scalar residual
regular selected-residual nonnegativity
canonical one-step domination
negative-root exclusion
outside-strip/trivial-zero terminal seam
RiemannHypothesis
```

These may be DERIVED or motivated, but none should be labeled PROVED before the exact Lean declarations pass the authoritative build and axiom gates.

## Complex-production transport firewall

Existing real-vector contraction derivative results do not automatically establish the production complex source-energy identity.

For FB-03E, acceptable proof authority must explicitly bridge:

```text
entrywise sourceEntry second derivative
-> complex source-matrix identity
-> contraction against conj(u_i)*u_j
-> zero-sum annihilation of the rank-two correction
-> production source energy of indexMatrix *ᵥ u.
```

A real-only theorem may be a helper but not the final production statement.

## Import/build closure law

A `.lean` file existing in the repository, appearing in a PR, passing the no-placeholder scan, or being merged does **not** establish that its declarations elaborate.

A declaration is compiler-validated project theorem authority only if its module lies in the transitive import closure of an exact successful authoritative build, or the module itself was explicitly built by an authoritative successful gate.

PR #103 remains the canonical historical example: a merged source file outside the validated import closure was not theorem authority until a later build consumed it.

Current example: the #155 source-energy jet, discrepancy-integrability and Riesz modules are imported by `Zeta23.CCM` and were validated by the exact green aggregate build.

## Axiom inspection

For production-promoted R003 bindings, `ClaimBindings.lean` must contain exact

```lean
#check <theorem>
#print axioms <theorem>
```

The accepted production foundation is `[propext, Classical.choice, Quot.sound]`. No production theorem may depend on `sorryAx` or a promoted project axiom.

Supporting theorem modules may carry module-local `#print axioms` checks without thereby becoming machine-promoted claims. PR #155 advances compiler theorem authority beyond the current machine-promoted claim-ID surface.

## Proof versus promotion

For R003 `PROVED_UNCONDITIONAL`, exact theorem names must agree across:

```text
CLAIM_REGISTRY.json
R003_PROMOTED_BINDINGS.json
Zeta23/CCM/ClaimBindings.lean
```

`promoted_binding_lint.py` enforces set equality, theorem-name equality and exact `#check`/`#print axioms` presence.

This docs/control sync deliberately leaves those promotion surfaces unchanged.

## Control-v2 validation law

`research/RHRC/control_v2/` is diagnostic research infrastructure only. Its CI gates enforce, among other things:

- no theorem/claim/terminal-answer authority;
- separate theorem and control-plane anchors;
- deterministic route certificates and score diagnostics;
- fail-closed missing retro-search / first-break requirements;
- exact archaeology scope and replay semantics;
- dead-route revival records when required;
- hard-coded current theorem/frontier/action smoke assertions.

The post-#155 sync must update the exact theorem anchor to #155, mark generic smoothing/even jets as completed theorem prerequisites, and retarget the chronological first break to complex D-transport / production odd jets / exact Riesz 6/8.

Control v2 may still rank a later arithmetic falsifier cheaply, but that routing decision is distinct from chronological theorem dependency.

## Vocabulary

- **source present** — file exists.
- **module compiles** — Lean elaborated that module.
- **umbrella build green** — named target and transitive imports compiled.
- **PR green** — all required gates for the exact PR object succeeded.
- **PROVED** — exact statement compiler-validated with acceptable axiom surface.
- **PROVED_UNCONDITIONAL** — proved theorem additionally registered on the production claim surface.
- **DERIVED** — mathematical consequence not separately theorem-locked.
- **LOCAL LEAN CHECK** — standalone/local compilation evidence outside merged theorem authority.
- **EXTERNAL DERIVED** — externally supplied exact/symbolic reasoning not yet repository-theoremized.
- **LEAD / HYPOTHESIS** — motivated research route.
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only.
- **OPEN** — not established.

## Claim firewall

Green generic smoothing and even-jet infrastructure are not RH. A contradiction still requires exact production odd jets, a retained transformed negative residual, and an independent nonnegative arithmetic sign on that same forced state, followed by negative-root exclusion and the terminal statement seam.

**RH remains OPEN unless the exact terminal RH theorem passes the complete proof and claim-validation gates.**
