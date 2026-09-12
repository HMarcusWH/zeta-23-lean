# Post-#155 research delta — legal Riesz smoothing, D-transport frontier, and pointwise-sign falsification

Date: 2026-09-13

> **Claim firewall:** compiler/CI evidence is authoritative for theorem validity. DERIVED statements, external reviews and numerical/exact finite falsifiers are not silently promoted to Lean theorems. **RH remains OPEN.**

## Exact authority

```text
merged main after #155 = 7bd3f1028d42272fcadc347c43371b992d9c0bd7
merged theorem tree = 9a4f21ed55aa0cbdf54527164c2f5f96912c65de
validated #155 head = ecfd075c07923e6fc80ab1a5b4f2d49c724f5577
validated theorem tree = 9a4f21ed55aa0cbdf54527164c2f5f96912c65de
RHRC #1005 / run 34720946254 = SUCCESS
Permansson #778 / run 34720946242 = SUCCESS
control-plane semantic anchor = PR #117
RH = OPEN
```

The validated PR head and merged main are different commits with the same theorem tree.

# What became formally true

## FB-03A — discrepancy integrability

**PROVED / #155**

The exact finite prime cumulative staircase, smooth pole cumulative weight, and pole-prime discrepancy are interval-integrable on every positive physical aperture.

## FB-03B — anchored Riesz primitives

**PROVED / #155**

`canonicalPolePrimeRieszPrimitive` gives left-anchored iterated primitives. Every positive-order primitive is absolutely continuous and has the previous primitive as derivative almost everywhere on the physical interval.

This is the legal analytic seam: the prime staircase is never differentiated.

## FB-03C — generic repeated integration by parts

**PROVED / #155**

The pulled-back source-energy iterated jets are smooth, their affine-chain derivative is exact, and the generic discrepancy energy can be rewritten as an arbitrary-order normalized Riesz energy under explicit endpoint-jet hypotheses.

The generic theorem still assumes

```text
forall j, 1 <= j -> j <= r ->
  iteratedDeriv j (sourceAtomRealEnergy K x) 0 = 0.
```

Therefore #155 proves the smoothing engine, not production order 6/8.

## FB-03D — source oddness / even jets / parity moment

**PROVED / #155**

Production `sourceAtomRealEnergy` is odd in the source coordinate. Hence all even endpoint derivatives at zero vanish. Even reversal parity also forces centered moment `M3=0`.

# What changed

Before #155 the project still had two intertwined doubts:

1. whether the prime staircase could be smoothed without illegal differentiation;
2. whether the production source energy really possessed the historical high-order endpoint flatness.

#155 closes the first and partially closes the second.

The remaining gap is narrower:

```text
odd endpoint jets only.
```

The generic Riesz theorem is already available once those jets are supplied.

# Derived theorem composition — next formalization target

## Source-coordinate D transport

**Status: DERIVED / OPEN IN LEAN.**

Let `g_u(omega)` be the production elementary source energy and let `D` be the centered-index diagonal map.

Direct differentiation gives the entrywise identity

```text
A''(omega) + (2*pi)^2 D A(omega) D
  = -4*pi * rank-two correction.
```

The correction is built from the all-ones vector and the sine profile. For complex coefficients, its Hermitian quadratic form contains `sum u` or its conjugate. Therefore

```text
M0(u)=sum u=0
  -> g_u''(omega)=-(2*pi)^2 g_(D u)(omega).
```

This must be theoremized on the genuine complex production energy.

## Moment-prefix recursion

The repository already proves the centered-moment shift

```text
M_k(Du)=M_(k+1)(u).
```

Hence the intended induction is

```text
M0=...=M(r-1)=0
  -> g_u^(2r)(omega)=(-1)^r*(2*pi)^(2r)*g_(D^r u)(omega).
```

Using the rank-one first derivative at zero then gives

```text
g_u^(2r+1)(0)
  = 2*(-1)^r*(2*pi)^(2r)*|M_r(u)|^2.
```

Expected production consequences:

```text
M0=M1=M2=0
  -> jets 1..6 vanish
  -> g^(7)(0)=-2*(2*pi)^6*|M3|^2

even parity + #155 M3=0
  -> jets 1..8 vanish
  -> g^(9)(0)=2*(2*pi)^8*|M4|^2.
```

These remain DERIVED until Lean validates them.

# Implementation firewall

Existing contraction-level second-derivative results are real-vector results. Production `sourceAtomRealEnergy` is the real part of a complex sesquilinear quadratic form.

The safe theorem path is:

```text
sourceEntrySecondDerivative
  -> entrywise rank-two identity, diagonal included
  -> coerce to the complex source matrix
  -> sum against conj(u_i)*u_j
  -> explicitly kill the rank-two correction using sum u_i=0
  -> identify D A D with source energy of indexMatrix *ᵥ u.
```

A theorem only for the real contraction API is not the production theorem.

# Downstream implications

If FB-03E is green, the generic #155 theorem immediately yields:

```text
boundary-flat trial -> exact production order-6 Riesz identity
even boundary-flat trial -> exact production order-8 Riesz identity.
```

The next composition should retain the whole #153 certificate:

```text
off-line zero
  -> retained regular first-bad certificate
  -> exact negative source-channel energy
  -> exact order-6/order-8 transformed negative residual.
```

At that point FB-03 is closed. The remaining contradiction-producing step is genuinely arithmetic.

# Resurrected routes

The D/moment infrastructure from the earlier constrained-sector work becomes newly valuable because #155 supplies a generic smoothing theorem waiting only on odd jets.

This does **not** revive generic D-isometry/unitary transfer. `D` remains algebraic, not metric-preserving.

# Dead route / exact falsification

The tempting implication

```text
positive Riesz primitive + boundary flatness
  -> pointwise fixed-sign smoothed integrand
```

is false.

Exact `K=2` boundary-flat fixtures are

```text
even: (1,-4,6,-4,1)
odd:  (1,-2,0,2,-1).
```

They satisfy the three boundary-flat moment equations and the stated reversal parity. The relevant seventh/ninth source derivatives change sign on the physical source-coordinate interval.

Classification:

```text
DEAD / exact finite falsification of the proposed mechanism.
```

This is not a zeta counterexample and does not refute the Riesz identity.

# New RH-relevant clues

## Complete integrated residual

**Status: LEAD / HYPOTHESIS.**

Since pointwise sign fails, any successful sign theorem must likely preserve more of the exact integrated cancellation:

```text
Riesz-transformed pole-prime discrepancy
  - reduced archimedean diagonal
  - reduced archimedean off-diagonal
  - scalar correction.
```

Candidate mechanisms include stationarity `A x0=b`, whole-cell smaller-size goodness, transfer to predecessor energies, or a new cancellation identity.

## Combined parity

**Status: LEAD / HYPOTHESIS.**

The first surviving local cutoff terms have opposite signs in the two parity sectors. Candidate combined quantities include

```text
S_even + S_odd
S_even * S_odd.
```

No global compensation theorem follows from the local sign observation.

# Falsification checks

1. **Complex-coefficient audit:** verify the D-transport algebra for arbitrary complex vectors, not only real fixtures.
2. **Boundary checks:** test `K=1`, `K=2`, degenerate moment cases, and vectors with `M_r=0` accidentally.
3. **Scaling:** confirm both sides scale by `|a|^2` under `u -> a*u`.
4. **Parity:** verify that the even-parity `M3=0` theorem supplies exactly the needed extra odd jet and nothing stronger by implication alone.
5. **Pointwise sign:** preserve the exact `K=2` falsifiers as a regression fixture.
6. **Combined parity:** numerically test proposed sum/product invariants across prime-power thresholds and inside fixed cells before theorem investment.
7. **Circularity:** any final nonnegative residual theorem must not assume successor positivity, absence of the negative root, or `canonicalOneStepDomination` under a new name.

# Highest-leverage next moves

1. Formalize the complex source-coordinate D-transport theorem.
2. Prove the moment-prefix recursion and odd endpoint formula.
3. Instantiate #155 to exact production Riesz orders 6/8.
4. Compose the transformed representation with the retained #153 negative certificate.
5. Only then retarget the #152 harness to the exact Lean-defined transformed residual.
6. Use the harness to falsify specific arithmetic mechanisms, not merely to observe sign frequency.
7. If a combined-parity invariant survives falsification, consider it as a parallel FB-04 lead.

# Standing questions

**Given everything now formally true, what becomes possible that was not possible before?**

The old D/moment machinery can now close the only missing analytical hypotheses of an already-proved generic Riesz theorem.

**If this contains a clue toward RH, where does it propagate?**

It propagates directly into an exact transformed version of the retained first-bad negative certificate, stripping the frontier down to one genuinely arithmetic sign obstruction.

**What most efficiently tells us whether the clue is real?**

The complex production D-transport theorem. If it compiles with the expected moment-prefix recursion, production Riesz 6/8 follows cheaply; if it fails, the failure identifies the exact algebraic obstruction before any more sign work.

**RH remains OPEN.**
