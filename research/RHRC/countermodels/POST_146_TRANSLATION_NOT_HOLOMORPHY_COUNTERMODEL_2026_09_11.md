# Post-#146 negative control — translation/deck law does not imply holomorphy

Date: 2026-09-11  
Evidence class: **exact elementary countermodel, not a Lean theorem**  
Scope: analytic proof-design firewall only  
Claim firewall: **not a CCM source counterexample; not a zeta counterexample; RH remains OPEN.**

## Purpose

PR #144 theorem-locks an exact logarithmic-cover structure for the frozen intrinsic predecessor:

```text
Ahat(z) = -z I + R(exp z)
R(exp(z+2*pi*i)) = R(exp z)
Ahat(z+2*pi*i) = Ahat(z) - (2*pi*i) I.
```

Those identities are useful for a later determinant-nonidentity argument, but they do not by themselves imply that `R(exp z)` or `Ahat(z)` is holomorphic.

This file records a minimal exact countermodel to the invalid inference

```text
translation/deck identity
-> holomorphy.
```

## Countermodel

Define

```text
F : C -> C
F(z) = -z + Re(z).
```

Let

```text
T = 2*pi*i.
```

Since `T` is purely imaginary,

```text
Re(z+T) = Re(z).
```

Therefore

```text
F(z+T)
  = -(z+T) + Re(z+T)
  = -z - T + Re(z)
  = F(z) - T.
```

So `F` satisfies exactly the same *shape* of affine deck-shift identity as the lifted predecessor scalar law:

```text
F(z+2*pi*i) = F(z) - 2*pi*i.
```

Equivalently, writing

```text
P(z)=Re(z),
```

we have

```text
F(z)=-z+P(z)
P(z+2*pi*i)=P(z).
```

Thus the decomposition

```text
linear nonperiodic term + deck-periodic remainder
```

is not sufficient to imply complex analyticity.

## Why `F` is not holomorphic

`Re(z)` is not complex differentiable on any open set. For example, at any point `z0`, compare directional difference quotients for the real and imaginary directions.

For real `h`:

```text
(Re(z0+h)-Re(z0))/h = 1.
```

For real `h` in the imaginary direction:

```text
(Re(z0+i h)-Re(z0))/(i h) = 0.
```

The complex derivative therefore does not exist. Hence `F(z)=-z+Re(z)` is not holomorphic.

## What this refutes

This exact elementary example refutes any proof pattern that argues:

```text
R(z+2*pi*i)=R(z)
therefore R is holomorphic
```

or

```text
Ahat(z+2*pi*i)=Ahat(z)-(2*pi*i)I
therefore Ahat is holomorphic.
```

Periodicity/translation laws are algebraic functional identities. Holomorphy is an analytic regularity property and requires separate hypotheses/proof.

## What this does not refute

This countermodel does **not** refute:

- the exact #144 deck identities;
- the existence of the exact frozen/log-cover production continuation;
- the possibility that the actual `complexFrozenIntrinsicPredecessorRemainder` is holomorphic;
- the finite-dimensional determinant nonidentity strategy once holomorphy is proved;
- any theorem about the actual canonical CCM source;
- RH.

## Required escape

A valid route must prove genuine complex differentiability / analyticity from the exact production definitions. The preferred mechanism is:

```text
fixed integration domain
+ pointwise complex differentiability in the parameter
+ local denominator nonvanishing/control
+ locally uniform integrable domination
-> differentiation under the integral
-> holomorphy of the exact production source cores
-> holomorphy of the assembled frozen source/predecessor remainder.
```

Only after that analytic gate closes should the deck identity be used in determinant nonidentity arguments.

## Regression rule

Whenever future proof plans use the phrases

```text
periodic remainder
translation law
deck transformation
log-cover identity
```

as evidence for holomorphy, test the reasoning against `F(z)=-z+Re z` first. If the same reasoning would incorrectly certify this `F` as holomorphic, the reasoning is invalid.

**RH remains OPEN.**
