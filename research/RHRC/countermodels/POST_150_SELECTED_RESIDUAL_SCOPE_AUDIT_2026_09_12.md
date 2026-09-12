# Post-#150 selected-residual scope audit — FB-04 harness

Date: 2026-09-12

> **RH remains OPEN.**
>
> This directory entry documents a falsification/certification harness. It is
> not Lean theorem authority and does not promote any RHRC claim.

## Purpose

PR #150 closed the regular-aperture dependency and theoremized a finite
regular cell-minimal first-bad state with a unique zero-shift preimage
`A x0 = b` and strictly negative exact canonical source-channel energy under a
hypothetical off-line zeta zero.

The current frontier is therefore the independent arithmetic sign target

```text
Ecanonical(c - x0) >= 0
```

on that forced state.

The control-plane first break `E4A4-SCHUR-FB-04` asks for an
**interval-certified** attempt to falsify proposed scoped versions of that sign.
Repeated high-precision floating point is not enough.

This harness implements that first break without changing theorem authority.

## Exact scope hierarchy used by the scout

The discovery script classifies finite states by increasing hypothesis strength:

```text
H0  selected predecessor is regular
H1  H0 + selected predecessor is positive definite
H2  H1 + selected successor parity has a negative quadratic direction
H3  H2 + every smaller size is good in both parities at the same selected aperture
```

`H3` matches the strongest selected-aperture ancestry exported by
`exists_regular_cellMinimal_firstBad`.

It is still weaker than the construction history used inside PR #150, which
first minimizes bad size over the **whole physical cutoff cell** and only then
moves the aperture. The floating scout may report a
`CELL_ANCESTRY_DISCOVERY_HEURISTIC`, but finite sampling never certifies that
whole-cell quantifier.

## Exact finite geometry

`post150_selected_residual.py` reconstructs the formal finite geometry over
exact rationals/integers before any floating source matrix is inserted.

For radius `N` and parity `p` it imposes:

```text
M0(u) = 0
M1(u) = 0
M2(u) = 0
reverse(u) = +u   (even)
reverse(u) = -u   (odd)
```

The exact nullspace has dimension `N-1`, matching the Lean theorem.

The one-step predecessor is centered zero extension into radius `N+1`.
The shell generator is obtained exactly as a nonzero vector in

```text
W^perp ∩ V_(N+1).
```

The shell is one-dimensional. Therefore this rational generator differs from
the formal `intrinsicCubicShellPart` only by a nonzero scalar. The
selected-residual **sign** is unchanged by that rescaling; the raw energy
magnitude is not identified with the canonical cubic normalization.

## Fast production backend

`canonical_source_numeric.py` deliberately imports only the existing R004
primitive formulas and applies the theorem-locked normalization repair

```text
canonicalSourceMatrix
  = legacyPrintedMatrix + 2*cCorrection(L) I.
```

It does not modify `run_commutator_gauntlet_v2.py`, whose `build_ccm_matrix`
binding remains the historical printed normalization.

The fast backend is for discovery and regression only.

## Independent Arb backend

`canonical_source_arb.py` independently reconstructs the direct production
equation-(4.4) canonical source with python-flint/Arb ball arithmetic.

The origin-sensitive archimedean integrals use the removable forms already
theoremized in `CanonicalApertureContinuity.lean`:

```text
sinh(z)/z
(cos z - 1)/z
(exp z - 1)/z
```

are evaluated through entire sinc-based formulas. The physical prime sum is
frozen only after the exact dyadic aperture is certified to satisfy

```text
log Q < L < log(Q+1).
```

The direct Eq.(4.4) matrix is also compared against the independently
reconstructed legacy-channel-plus-`2*cCorrection(L)I` split.

## Basis-invariant block algebra

Let `B` be the exact integer predecessor basis embedded in the successor
carrier, `c` the exact rational shell generator, and `M+` the production
successor canonical matrix.

The arbitrary-basis block equations are

```text
H = B* M+ B
r = B* M+ c
q = c* M+ c
H x = r
u0 = c - B x
S0 = q - r* x.
```

No orthonormalization is needed in the rigorous replay. `H x = r` is exactly
the coordinate form of the projected predecessor equation because the common
Gram factor cancels.

The fast scout uses orthonormal numerical coordinates only for conditioning;
it separately checks the raw exact-basis N-flow restriction identity.

## Rigorous certification conditions

For a checked-in candidate, the Arb replay certifies:

1. exact physical cutoff-cell membership;
2. predecessor regularity by determinant exclusion of zero;
3. predecessor positive definiteness by Sylvester's criterion;
4. successor badness by an explicit rational direction with a strictly negative enclosed quadratic value;
5. every smaller size in both parities is positive definite at the same aperture, a stronger sufficient condition for `not AnyParityBad`;
6. the Schur and direct trial energies are both strictly negative;
7. the two energy evaluations overlap as rigorous balls;
8. the direct production source and legacy-plus-repair channel sum overlap.

Only a state passing all H3 conditions and strict negative energy is reported as

```text
RIGOROUS_FINITE_NUMERICAL_COUNTEREXAMPLE_TO_H3_SCOPED_SIGN_MECHANISM.
```

That would falsify that *scope of the candidate arithmetic theorem*, not RH and
not the stronger whole-cell #150 state.

## Files

```text
research/RHRC/routes/R003_ccm_bridge/canonical_source_numeric.py
research/RHRC/routes/R003_ccm_bridge/canonical_source_arb.py
research/RHRC/routes/R003_ccm_bridge/post150_selected_residual.py
research/RHRC/routes/R003_ccm_bridge/probe_post150_selected_residual_scope.py
research/RHRC/routes/R003_ccm_bridge/certify_post150_selected_residual_scope.py
research/RHRC/routes/R003_ccm_bridge/check_post150_selected_residual_scope.py
research/RHRC/routes/R003_ccm_bridge/fixtures/post150_selected_residual_v1.json
```

## Commands

Broad discovery:

```bash
python research/RHRC/routes/R003_ccm_bridge/probe_post150_selected_residual_scope.py \
  --q-min 2 --q-max 12 --n-min 1 --n-max 8 --samples 5 \
  --output /tmp/POST150_SELECTED_RESIDUAL_DISCOVERY.json
```

Rigorous replay of checked-in candidates:

```bash
python research/RHRC/routes/R003_ccm_bridge/certify_post150_selected_residual_scope.py \
  --input research/RHRC/routes/R003_ccm_bridge/fixtures/post150_selected_residual_v1.json \
  --output /tmp/POST150_SELECTED_RESIDUAL_CERTIFICATE.json
```

Cheap CI plumbing/regression check:

```bash
python research/RHRC/routes/R003_ccm_bridge/check_post150_selected_residual_scope.py
```

## Initial research signal

During development, a low-dimensional floating scout over 880 states
(`Q=2..12`, five dyadic apertures per cell, `N=1..8`, both parities) produced
negative selected-residual values only in states where the predecessor was
numerically at/near the regularity or positivity boundary at the chosen
tolerance. No H2/H3 negative state appeared in that exploratory sweep.

**Status: EXPERIMENTAL SIGNAL ONLY.**

This does not prove H2/H3 nonnegativity, and it is not a substitute for the
interval-certified search. It does suggest that first-bad ancestry may be doing
genuine mathematical work rather than merely decorating the endpoint.

The checked-in fixture starts with no promoted counterexample candidate. A
future candidate must survive the Arb replay before FB-04 can be called
falsified at the advertised scope.

## Claim firewall

- exact rational finite geometry is not a Lean proof of a source sign;
- floating discovery is not interval certification;
- Arb finite certification is not Lean theorem authority;
- selected-aperture H3 is not whole-cell #150 ancestry;
- arbitrary shell normalization preserves sign, not canonical magnitude;
- generic or modified-source countermodels do not refute canonical CCM;
- no finite calculation closes the finite-to-infinite seam;
- **RH remains OPEN.**
