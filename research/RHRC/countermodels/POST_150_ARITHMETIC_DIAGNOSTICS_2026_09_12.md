# Post-#150 arithmetic diagnostics and falsification memory

Date: 2026-09-12

> **Status firewall:** this file records external/derived/experimental diagnostics that constrain proof design after PR #150. Unless separately theoremized, nothing here is `PROVED`. These are not zeta counterexamples. **RH remains OPEN.**

## D1 — regularization is closed; arithmetic sign is not

**Classification:** PROVED theorem context + OPEN arithmetic consequence.

PR #150 proves that a hypothetical off-line zero forces a finite regular first-bad state with exact negative canonical source-channel energy.

This kills the old escape hatch “perhaps the predecessor is singular.” It does **not** prove that the selected energy must be nonnegative.

Research consequence: do not route back to assembled holomorphy, determinant nonidentity or regular-aperture selection unless a regression is discovered.

## D2 — full construction state is richer than the outer endpoint

**Classification:** DERIVED from theorem interfaces.

The cell-minimal construction has access to whole-cell minimality and smaller-size goodness before the outer energy/ExceptionalZero wrappers compress the witness.

Research consequence: before arithmetic work, consider exporting a richer certificate that retains:

```text
K* and N*=K*-1
whole-cell minimality
all-smaller-size goodness
selected aperture / parity
regularity
negative root
A x0=b
negative exact channel energy.
```

This is not a new theorem until separately formalized.

## D3 — pole/prime discrepancy identity

**Classification:** EXTERNAL DERIVED; repository reproduction pending.

With

```text
g_u(omega)=<sourceMatrix(omega)u,u>
D(t)=4*sinh(t/2)-sum_{q<=exp(t)} Lambda(q)/sqrt(q),
```

the external audit derives

```text
E_pole(u)-E_prime(u)
  = (1/L) * integral_0^L D(t) * g_u'(1-t/L) dt.
```

Research consequence: preserve pole/prime cancellation before inequalities. Do not independently majorize the two channels unless the loss is rigorously controlled.

## D4 — boundary-flat Taylor annihilation

**Classification:** DERIVED algebraic calculation; Lean theoremization pending.

For centered moments `M_j(u)`, the exact elementary source-atom energy expands as

```text
g_u(omega)
  = sum_{r>=0}
      [(-1)^r * 2^(2r+1) * pi^(2r)/(2r+1)!]
      * omega^(2r+1)
      * sum_{a=0}^{2r} conjugate(M_{2r-a}(u))*M_a(u).
```

Legal boundary-flat vectors satisfy

```text
M0=M1=M2=0.
```

Therefore the first generic surviving term is

```text
-(8*pi^6/315)*|M3|^2*omega^7.
```

For even parity, `M3=0`, so the first possible term is

```text
(4*pi^8/2835)*|M4|^2*omega^9.
```

Research consequence: the discrepancy kernel is highly stationary at the endpoint. This is stronger and more useful than treating the atom as a generic smooth function.

## D5 — Riesz-smoothed discrepancy candidate

**Classification:** DERIVED conditional on D3; not yet Lean-locked.

Let `D^[r]` denote the r-fold cumulative integral of `D`, starting with `D^[0]=D`.

Repeated integration by parts, using D4 to kill the endpoint derivatives, gives the candidate exact forms

```text
E_pole-E_prime
  = L^-7 * integral_0^L D^[6](t) * g^(7)(1-t/L) dt
```

for legal boundary-flat vectors and

```text
E_pole-E_prime
  = L^-9 * integral_0^L D^[8](t) * g^(9)(1-t/L) dt
```

for even parity.

Research consequence: attack a high-order Riesz-smoothed prime discrepancy rather than the raw prime staircase.

**LEAD:** in explicit-formula representations, repeated integration may strongly suppress high-zero contributions. Whether this is quantitatively sufficient for the exact archimedean budget is OPEN.

## D6 — raw aperture Loewner monotonicity

**Classification:** EXPERIMENTAL SIGNAL / QUARANTINED SHORTCUT.

Canonical numerical probes show mixed signs in derivative eigenvalues rather than a uniform Loewner direction.

Do not assume

```text
M'(L) >= 0
```

or

```text
M'(L) <= 0
```

globally.

A revival requires a narrower state/sector theorem or rigorous evidence showing the mixed-sign modes are irrelevant to the exact #150 trial.

## D7 — minimizing-trial Schur monotonicity

**Classification:** EXPERIMENTAL SIGNAL / QUARANTINED SHORTCUT.

The derivative of the regular zero-shift Schur value changes sign in tested canonical aperture ranges.

Research consequence: the envelope identity

```text
S'(L)=<M'(L)u(L),u(L)>
```

may still be useful diagnostically, but not as a global monotonicity theorem without new structure.

## D8 — universal positive elementary atom kernel

**Classification:** EXPERIMENTAL SIGNAL / QUARANTINED SHORTCUT.

The elementary atom energy on tested canonical zero-shift trials changes sign.

Research consequence: do not seek a proof that every elementary source atom contributes a nonnegative amount to the selected residual. Full-source cancellation or a transformed discrepancy may still be positive.

## D9 — extreme channel cancellation

**Classification:** EXPERIMENTAL SIGNAL; continuation of post-#138 conditioning warning.

Small canonical examples exhibit final Schur energies many orders of magnitude smaller than the individual pole/arch/scalar/prime terms.

Research consequence: a candidate proof must preserve correlated cancellation or demonstrate, with interval-certified margins, that its separate bounds are sufficiently sharp.

## D10 — coth/deck coordinate mismatch

**Classification:** DERIVED CORRECTION / DOWNGRADED LEAD.

The removable scalar factor uses the complex aperture variable `L`:

```text
L*(exp L + 1)/(exp L - 1)=L*coth(L/2).
```

The exact deck action occurs after the logarithmic lift `L=exp z` and acts on `z`:

```text
Ahat(z+2*pi*i)=Ahat(z)-(2*pi*i)I.
```

The two `2*pi*i` appearances therefore live in different coordinates. No common-lattice resolvent identity may be inferred without an explicit transform/conjugacy theorem.

## D11 — strongest useful next numerical gate

Do not spend compute merely confirming more positive predecessor eigenvalues. The next useful experiment should target the exact regular selected-residual observables and should preferably use interval arithmetic.

For each tested canonical state record:

```text
L, Q, N, parity
regularity margin / smallest predecessor eigenvalue
x0 solving A x0=b
full Ecanonical(c-x0)
pole contribution
arch-diagonal contribution
arch-off-diagonal contribution
scalar contribution
prime contribution
q_c
<b,x0>
raw discrepancy integral
Riesz-smoothed discrepancy integral when implemented
aperture derivative / envelope value
```

Tests should include both parities, increasing size, and points near prime/prime-power threshold apertures while respecting the exact fixed-cell hypotheses.

## D12 — what would count as a decisive falsifier

A rigorous interval-certified canonical state satisfying the exact scoped #150 hypotheses with

```text
Ecanonical(c-x0)<0
```

independently of an assumed off-line zero would falsify any proposed theorem asserting universal nonnegativity on that broader scope, but would **not** by itself be an RH counterexample.

A proposed final sign theorem must state a scope narrow enough to use the full forced #150 ancestry if broader canonical states violate it.

## Claim boundary

These diagnostics may reroute research. They do not establish:

```text
Riesz-smoothed discrepancy sign
regular Schur-energy nonnegativity
one-step domination
negative-root exclusion
RiemannHypothesis
```

**RH remains OPEN.**
