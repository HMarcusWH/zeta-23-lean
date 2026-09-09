# Post-#138 Astra diagnostic findings

> **Status firewall:** this file records discovery/falsification evidence reported by an external audit. Unless separately theoremized or repository-certified, entries are `DERIVED` or `EXPERIMENTAL SIGNAL`, not `PROVED`. **RH remains OPEN.**

## Purpose

Preserve the reusable negative controls and discovery signals that changed the post-#138 research ordering.

## D1 — universal determinant positivity is not a smaller target

**Classification:** DERIVED.

Under predecessor PSD and a one-dimensional shell,

```text
q_c >= 0 AND forall w, Delta(w) >= 0
```

is equivalent to nonnegativity of the successor quadratic form. Therefore a universal A4b2b proof that merely repackages successor positivity has zero information gain.

## D2 — resonance supplies an explicit determinant witness

**Classification:** DERIVED.

For `k=P_(ker A)b`,

```text
Delta(k) = -||k||^4.
```

This is a preferred falsification direction for singular predecessor states.

## D3 — root-selected determinant witness

**Classification:** DERIVED.

At a safe negative explicit root `lambda`, with `w_lambda=(A-lambda I)^-1 b`,

```text
Delta(w_lambda)
  = lambda*q_A(w_lambda)*(rho+||w_lambda||^2)
    - lambda^2*||w_lambda||^4.
```

This gives a canonical discovery vector attached to the actual forced root.

## D4 — correction-vector proportionality

**Classification:** DERIVED / external exact finite verification; not Lean-locked.

Reported identity:

```text
d = -(6/(2*N-1)) a.
```

Exact rational checks were reported for `K=2,...,30`. Until formalized, use this only as a route-design constraint.

**Route consequence:** do not invest in arguments requiring `a` and `d` to be linearly independent.

## D5 — atomwise determinant positivity fails

**Classification:** DERIVED symbolic result reported by external audit; repository reproduction pending.

The first nonzero two-vector determinant coefficient of an elementary source atom is reported negative. On the tested BF predecessor/shell fixtures the first determinant orders are:

```text
odd parity:  omega^18
even parity: omega^22.
```

**Route consequence:** the old `omega^7 / omega^9` source-coordinate cancellation does not justify a positive atom-by-atom determinant or SOS decomposition. Full canonical mixed-channel cancellation remains open.

## D6 — sharp canonical Schur cancellation

**Classification:** EXPERIMENTAL SIGNAL; high precision, not interval certified.

Reported canonical sample:

```text
L = 3
K = 6
even parity
S0 ~= 4.91225958747865e-10
(sum absolute channel magnitudes)/S0 ~= 6.4583e20.
```

**Route consequence:** independent absolute bounds on pole, archimedean, scalar and prime channels may lose far too much information. Prefer exact paired cancellation/remainder identities before inequalities.

## D7 — prime coefficient sensitivity

**Classification:** EXPERIMENTAL SIGNAL on modified sources; not a canonical zeta counterexample.

Reported sample at `L=2, K=3`:

- increasing the prime-2 coefficient by relative `1e-8` can make the even successor negative;
- both predecessor blocks remain positive;
- shell energy remains positive;
- a consistent relative perturbation of the available powers `2,4` preserves the qualitative effect.

**Route consequence:** positivity of weights, finite support, parity and source-channel architecture alone cannot prove the desired sign. The exact canonical coefficients and prime/archimedean interaction matter.

## D8 — required next numerical gate

Do not spend compute on another broad list of positive eigenvalues. The next useful experiment should target the regular minimizing trial

```text
u0 = c - A^-1 b
S0 = Ecanonical(u0)
```

and report, preferably with interval certification:

- full `S0`;
- pole, arch-diagonal, arch-off-diagonal, scalar and prime contributions;
- `q_c` and `<b,A^-1b>` separately;
- `r/q_c`;
- prime-weight sensitivities from `dS0/dt=<u0,M'(t)u0>`;
- behavior at prime/prime-power threshold apertures;
- both parities and increasing size.

## Claim boundary

These findings constrain research design. They do not establish regular-aperture selection, Schur-energy nonnegativity, negative-root exclusion, or RH.

**RH remains OPEN.**