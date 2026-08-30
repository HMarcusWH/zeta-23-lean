# D0-R — R002 taper-grid / CCM map-or-separate audit — 2026-08-30

Status: **SPECIALIZATION-ONLY / GENERIC PRODUCTION MAP NOT ESTABLISHED**.

Base after merged PR #65:

```text
ab3dace8489f3eb9a566bc85f507fc811efa90be
```

PR: **#66**

Branch:

```text
research/d0r-r002-ccm-map-separate-20260830
```

## Question

Does the actual R002 taper-grid/windowed-probe object map exactly to the
canonical finite CCM object by equality, scaling, congruence, compression, or a
named change of basis?

The comparison must distinguish the actual objects.  In particular:

- R002 `Gz P T` is a **global** all-zero taper-grid matrix.
- R002 `Az P T` is only the finite zero-window contribution and is the object
  identified with `ZeroSide.blockA`.
- CCM `zeroSideMatrix hs N L` is again global, but is built from the centered
  finite qBasis/dictionary family.
- PR #65 proves
  `zeroSideMatrix = cutoffFreeMatrix = finiteMatrix + 2*cCorrection(L)*I`.

Therefore `blockA = CCM` is not an admissible identification unless the R002
tail is separately shown to vanish.

## PROVED — theorem-level D0-R firewalls

`Zeta23/ExceptionalZero/R002CCMRepresentation.lean` proves:

```text
Gz = Az + Ez
Gz = Az  <->  Ez = 0
```

for the exact R002 definitions.

It also proves:

```text
1 < P.lam  ->  not P.Valid
```

because the current production `Params.Valid` includes `P.lam <= 1`.

Thus the historical R002 oversampling experiment at `lambda > 1` is not
inside the current formal production-validity envelope.

The file also theorem-locks the exact frequency-grid decomposition

```text
tau_k = T + k*hgrid
```

and proves the generic response-coordinate atom law

```text
vecMulVec(C v, C v)
  = C * vecMulVec(v,v) * transpose(C).
```

Any legitimate exact R002 -> CCM basis-map claim must therefore provide an
actual response-level coordinate map; a same-dimension numerical matrix fit is
not sufficient.

## DERIVED / EXPERIMENTAL SIGNAL — hard-window specialization

The deterministic falsifier

```text
compare_r002_ccm_probe_families.py
```

checks the character-correlation interpretation directly.

For hard-window Fourier characters on `[0,L]` it evaluates

```text
2 Re [ L^-1 integral_0^(L-y)
  exp(2*pi*i*n*x/L)
  conj(exp(2*pi*i*m*(x+y)/L)) dx ].
```

Its elementary closed form is exactly the current CCM `qBasis(n,m,y,L)`:

- on the diagonal:
  `2*(1-y/L)*cos(2*pi*n*y/L)`;
- off the diagonal:
  `(sin(2*pi*n*y/L)-sin(2*pi*m*y/L))/(pi*(m-n))`.

The script verifies both the closed form and direct numerical quadrature.

This is useful: the old intuition that CCM belongs to a hard truncated-character
correlation geometry is real.

But the same script replaces the hard box by a smooth plateau/ramp taper of the
R002 type and obtains a nonzero entry mismatch.  This is an
**EXPERIMENTAL SIGNAL**, not a universal no-map theorem.

## Exact production differences that remain

The actual production families differ in several theorem-visible ways:

| Feature | R002 production | CCM canonical finite object |
|---|---|---|
| finite index type | `Fin(P.d T)` | `Fin(2*N+1)` |
| index origin | `k = 0,...,d(T)-1` around carrier `T` | centered `-N,...,N` |
| physical window | smooth C3 taper profile with ramp width `w` | hard truncated-character/qBasis source convention |
| zero range of block object | `Az`: finite `ZIprime T` | `zeroSideMatrix`: all zeros |
| global R002 object | `Gz = Az + Ez` | already global |
| aperture parameters | `L=P.lam*l(T)` plus `T,w,rho` | `L,N` |
| current validity | `0 < lambda <= 1` | positive `L` |

No theorem in PR #66 erases any of these differences.

## D0-R classification

```text
SPECIALIZATION_ONLY
```

The hard-window truncated-character geometry underlying qBasis is a genuine
specialization-level connection.

What is **not** proved is a generic production theorem

```text
R002 Gz / G-tilde  =  CCM zeroSideMatrix
```

or any universal congruence/compression between those two families.

Accordingly, the generic R002 masking obligation `R002_WINDOWED_VISIBILITY`
must not be treated as a bottleneck for the canonical CCM/Galerkin route.

This is a route separation, not a refutation of R002 itself.  R002 remains a
valid independent discovery route with its own block-level negativity theorem
and its own open windowed-visibility problem.

## Claim firewall

**PROVED:**

- exact R002 global/window/tail decomposition;
- exact tail-vanishing criterion for replacing `Gz` by `Az`;
- current `Params.Valid` excludes `lambda>1`;
- response atoms transform by transpose congruence under a supplied coordinate
  map;
- the R002 frequency grid has an explicit common carrier plus lattice offset.

**DERIVED / EXPERIMENTAL SIGNAL:**

- hard-window character correlation has the qBasis closed form;
- numerical quadrature reproduces it;
- a smooth tapered example does not reproduce the same entries.

**OPEN:**

- any generic taper-dependent exact response map to CCM;
- R002 windowed visibility;
- arithmetic positivity for the R002 windowed family;
- Bombieri correspondence;
- localized Weil form restriction;
- form-core density;
- Rayleigh-Ritz convergence;
- RH.

## Next move

D0-R no longer blocks the CCM critical path.

The next representation audit is **D0-B: Bombieri correspondence**.  Extract the
exact finite Bombieri object, then classify equality, congruence, compression,
or mismatch against the theorem-authoritative canonical finite matrix before
using any negative-inertia conclusion.

RH remains **OPEN**.
