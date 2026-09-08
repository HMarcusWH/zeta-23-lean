# Post-129 structural countermodels and historical transfer discovery evidence — 2026-09-08

> **Status:** EXPERIMENTAL SIGNAL / SYNTHETIC FALSIFICATION FIXTURES.  
> **Not Lean theorem authority. Not a realizable zeta counterexample. RH remains OPEN.**

This file preserves the post-#128/#129 falsification evidence that changed the active theorem frontier. Its purpose is to stop the project from rebuilding a generic contradiction that has already been defeated by explicit finite models.

## What these fixtures are for

They test statements of the form:

> "The already-proved first-bad / shell / Schur / resonance / parity / KKT / displacement structure by itself should force a contradiction."

A fixture that satisfies the generic structural hypotheses while retaining a negative finite state refutes that generic route. It does **not** refute the actual `canonicalSourceMatrix`, because the fixture's diagonal/source values are not proved to come from the CCM source formula.

## Generic regular 2x2 fixture

Take

```text
T = [[1,1],
     [1,0]]
A = [1]
b = [1]
```

Then the predecessor block is nonnegative and the zero-shift solve is `x0=1`. The canonical shell-normalized zero-shift trial is represented by

```text
u0 = (-1,1)
```

and

```text
T u0 = (0,-1),
S0 = -1.
```

Thus a nonnegative predecessor can coexist with a strictly negative zero-shift Schur endpoint and a pure-shell zero-shift response. This kills any argument that treats `Re S0<0` or the shell-response sign as a generic contradiction.

## Generic resonant 2x2 fixture

Take

```text
T = [[0,1],
     [1,0]]
A = [0]
b = [1].
```

The predecessor has a genuine zero mode with nonzero shell coupling, while the full operator has negative eigenvalue `-1`. The resonant identity/pole mechanism is exact rather than contradictory.

This kills the generic inference

```text
zero resonance + negative successor spectrum -> impossible.
```

## Centered radius-3 diagonal fixtures

The discovery pass then moved from abstract 2x2 blocks to the repository's actual centered radius-3 grid

```text
d = -3,-2,-1,0,1,2,3
```

with the actual boundary-flat even/odd parity spaces, centered-index D-map, cubic channel/KKT normal geometry and centered nesting, but with a generic real reversal-symmetric diagonal operator

```text
M = diag(q_|d|).
```

Three useful fixtures were found.

### Fixture C1 — both predecessors positive, both regular responses negative

```text
q = (1,1,1,-10).
```

Observed structural behavior:

- both predecessor parity sectors positive;
- both successor regular shell responses negative;
- cubic defect remains one-channel/rank-at-most-one compatible.

Use: refutes generic regular-branch exclusion from predecessor positivity + one-dimensional shell/cubic structure.

### Fixture C2 — one parity bad, the other positive

```text
q = (0,1,4,-10).
```

Observed structural behavior:

- odd successor negative;
- even successor positive.

Use: refutes automatic transfer of negative-root/badness from one parity to the other under generic parity geometry.

### Fixture C3 — genuine odd resonance without successor nullity

```text
q = (0,1,-4,0).
```

Observed structural behavior:

- genuine odd zero resonance at the predecessor level;
- both successor kernels zero.

Use: refutes the inference that a predecessor resonance must lift to successor nullity or that generic nullity bookkeeping alone removes resonance.

## Displacement identity is not enough

For the centered index operator `D`, a diagonal matrix commutes with `D`. Therefore adding a reversal-symmetric diagonal perturbation preserves the displacement commutator

```text
[D, M + diag(q)] = [D,M].
```

Yet the fixtures above change sign-sensitive successor behavior.

So the exact low-rank displacement identity is valuable structure, but it cannot by itself exclude the first-bad negative state. A terminal contradiction must use canonical source values not preserved by arbitrary diagonal perturbation.

## Historical exact-rational discovery record

The post-#128 discovery pass reported exact-rational checks of the proposed cross-parity transfer architecture.

Recorded external results were:

```text
37 distinct diagonal parameter cases
5 rational negative shifts per case
185 exact secular-transfer / trial-reconstruction / overlap checks passed
74 exact KKT moment-coefficient checks passed
140 checks failed when the predecessor correction in D c+ was omitted
```

One recorded exact-rational example at an even root used

```text
lam = -13/42
F_- = -55/21
Gamma = 1
phi(u_+) = -55/21.
```

### Repository reproducibility status

The original discovery script and its complete 37-case parameter table were **not checked into this repository with PR #129 and were not recovered from repository history during the PR #130 review**. Therefore the counts above are preserved only as **HISTORICAL EXPERIMENTAL SIGNAL**.

They are **not** a current CI regression gate, must **not** be described as repository-reproducible regression data, and must not be used to claim that `run_suite.py` independently verifies the `185 / 74 / 140` counts.

Fail-closed rule:

```text
missing original oracle/data
  -> do not fabricate replacement cases from the reported counts
  -> do not upgrade the counts to CI evidence
  -> rely on the Lean-PROVED #129 decomposition for theorem authority
  -> recover and independently validate the original oracle before wiring it into CI
```

The theorem-backed firewall remains stronger than the historical discovery signal: #129 proves the exact predecessor-plus-shell decomposition and retains the predecessor correction in the cross-parity proof. It does **not** prove that the predecessor correction is nonzero in every allowed case.

## What these fixtures falsify

The explicit finite fixtures above falsify or quarantine the following generic leads:

1. negative zero-shift endpoint is itself a contradiction;
2. exact zero resonance is itself a contradiction;
3. one parity negative automatically forces the other parity negative/rooted;
4. the bad eigenmode's cubic coefficient must vanish generically;
5. predecessor resonance must imply successor nullity;
6. first-bad + KKT + rank-one cubic + N-flow structure alone excludes the obstruction;
7. the displacement identity alone excludes the obstruction.

The historical exact-rational counts are supporting discovery evidence for the transfer architecture; until the original oracle is recovered they are not an executable repository falsifier.

## What remains live

The fixtures do **not** test the actual canonical source values. Therefore the live question after PR #129 is:

> Which exact identity satisfied by `canonicalSourceMatrix` invalidates these generic finite models?

The first theorem-backed place to ask that question is

```text
evenQuadraticSourceMoment L K v
  = <centeredQuadraticNormal K,
      canonicalSourceMatrix(L,K) v>
      / <centeredQuadraticNormal K, centeredQuadraticNormal K>
```

because PR #129 proves this is exactly the surviving cubic parity-defect coefficient.

## Fast falsification rule for future leads

Before building a new root-exclusion theorem around a proposed structural identity:

1. ask whether the identity is preserved by arbitrary reversal-symmetric diagonal perturbations;
2. if yes, run it against C1-C3;
3. if it still predicts impossibility, locate the hidden extra assumption;
4. only then spend Lean effort.

This is intended to maximize mathematical information gain and minimize proof-engineering on already-dead generic routes.

**RH remains OPEN.**
