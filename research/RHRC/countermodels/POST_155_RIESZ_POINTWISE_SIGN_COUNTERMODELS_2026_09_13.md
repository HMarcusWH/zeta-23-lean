# Post-#155 exact Riesz pointwise-sign countermodels

Date: 2026-09-13

> **Scope firewall:** these are exact finite countermodels to a proposed proof mechanism, not counterexamples to RH and not counterexamples to the #155 Riesz identity. **RH remains OPEN.**

## Mechanism being tested

The falsified implication is

```text
positive left-anchored Riesz primitive
+ boundary-flat endpoint cancellation
-> pointwise fixed-sign smoothed source-energy integrand.
```

A failure of this implication means smoothing cannot manufacture pointwise positivity merely from primitive positivity and endpoint flatness.

## Exact K=2 fixtures

Use centered coordinates `n=-2,-1,0,1,2`.

### Even reversal fixture

```text
u_even = (1,-4,6,-4,1)
```

This vector is reversal-even and satisfies the three boundary-flat centered-moment constraints

```text
M0=0
M1=0
M2=0.
```

Even parity also gives `M3=0`.

The first potentially surviving odd endpoint derivative is therefore the ninth-order term, proportional to `|M4|^2` at zero. The corresponding ninth derivative is not of one fixed sign throughout the physical source-coordinate interval.

### Odd reversal fixture

```text
u_odd = (1,-2,0,2,-1)
```

This vector is reversal-odd and satisfies

```text
M0=0
M1=0
M2=0.
```

The first potentially surviving odd endpoint derivative is the seventh-order term, proportional to `-|M3|^2` at zero. The corresponding seventh derivative changes sign on the physical source-coordinate interval.

## What these fixtures establish

They falsify the proposed universal step

```text
D^[r](t) >= 0
and endpoint jets vanish
-> D^[r](t) * g^(r+1)(1-t/L) has a fixed sign pointwise.
```

Even when the Riesz primitive is positive in a prime-free aperture, the source-energy derivative factor can change sign.

## What they do not establish

They do **not** show that:

- the full integrated Riesz pairing has no useful sign;
- the complete discrepancy minus archimedean/scalar residual can be negative under the exact retained first-bad ancestry;
- the D-transport recursion is false;
- the #155 Riesz identity is false;
- RH is false.

## Research consequence

Classify the universal pointwise-sign route as dead. Future FB-04 work must instead preserve the complete integrated arithmetic structure or identify a different global invariant.

Potential surviving mechanisms include:

```text
stationarity A x0=b
whole-cell first-bad minimality
transfer to smaller-size good states
exact discrepancy/archimedean cancellation
combined-parity invariants.
```

Each remains OPEN until separately theoremized.

## Regression use

Before reviving a proposed pointwise positivity argument, test it against both fixtures. A valid revival must name a new hypothesis that excludes these fixtures and prove that the exact retained first-bad production state satisfies that hypothesis.

**RH remains OPEN.**
