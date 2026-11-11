# Step 4 target consolidation after round 7

11 November 2026. Parent head `b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`.
**Register and navigation document. RH and Step 4 remain OPEN.** The paper
derivations cited here are DERIVED and not independently reviewed; the two Lean
modules are compiled locally on the pinned toolchain and need current-head CI.

## The three open suppliers are one

The November handovers list three alternative sufficient tasks for the fixed
source `h` and its complete prime field `Z`:

* (U): a cofinal bound for the weighted response `A_Z(T)` at every positive rate;
* (F): a lower bound for the loading ratio of the reconstructed vector `v_L`;
* (E): a cofinal bound for the predecessor defect `E_L` under a hypothetical zero.

Round 7 shows that they are the same growth bound for `Z`, in three norms.

| Target | What it is | Why |
|---|---|---|
| (U) | weighted `L¹` growth of `Z` | definition |
| (F) | weighted `L²` growth of `Z` | the numerator `‖N v_L‖²` tends to the fixed positive constant `‖U‖²`, so the ratio is the reciprocal of the weighted energy |
| (E) | plain `L²` growth of `Z` at horizon `L − c₀` | at arbitrarily late apertures the least-crossing cutoff is 3, the predecessor is `{0}`, and the defect is the complete source column |

Each of them, at rate `η`, excludes zeros with displacement above `η` and is
implied by their absence. None is a weaker intermediate of another. Work on (E)
or (F) as separate suppliers should stop.

## What the selector does under a hypothetical zero

* Derived, no dominance assumption: for every `β < δ` there are arbitrarily late
  apertures where one of the two cutoff-3 unit vectors has energy below
  `−e^{βL}`. Any packet at such an aperture with depth `D ≤ 2e^{βL}` has stored
  cutoff 3 and both predecessor spaces zero. That finite implication is
  compiled: `SelectedCutoff.lean` (M61). Without a dominance assumption the note
  does not show that these apertures are the ones the compiled production
  detector selects.
* Derived, dominant zero: the cutoff is 3 or 4 at every late aperture, so the
  predecessor has dimension 0 or 2.
* Model illustration (one added off-line quadruple; not the zeta function):
  [evidence/increment6a](../evidence/increment6a/SUMMARY.json). In both parameter
  sets every sampled aperture beyond a transient has cutoff 3 or 4.

Round 6's cubic ceiling is therefore a constant ceiling on those packets. The
positive predecessor that inequality (P) relies on is empty or two-dimensional
exactly where (P) is meant to be used.

## The weakest form of the remaining target

Let `E_e(L)` be the canonical energy of the unit vector of the even cutoff-3
pole-neutral boundary-flat space. Its transform is explicit:
`R(z) = c_e (z² − 1/4) / (z ∏_{a≤3} (z² + (2πa/L)²))`.

* Derived: `sup Re ρ − 1/2` equals the least exponential rate at which `E_e` is
  bounded below. In particular RH holds if and only if `E_e(L) ≥ 0` for all large
  `L`, and under RH `0 < E_e(L) ≤ 12.94 / L⁵`.
* Checked: the prime side (Arb enclosures) and the sum over the first 400 zeros
  agree to a relative difference between `8e-17` and `9e-14` at twelve apertures
  from 2 to 12 (EXPERIMENTAL SIGNAL; the identity itself is compiled in
  `BoundaryFlatFiniteWeil.lean`).

The closing premise can be stated on one explicit sequence of smoothed prime
sums. Whole slices, the quartic cutoff, the selected ground and the near-null
core are not needed to state it, and none of them currently helps to prove it.

## The rate ladder (compiled)

`ZeroFreeFloor.lean` (M60) proves, for `a ≥ 0` and each parity:

    every nontrivial zero has |Re ρ − 1/2| ≤ a
        ⇔  for every α > a, the fixed-rate bound at rate α holds at every large aperture.

* The direction "zero strip ⇒ floor" is new and has explicit constants: on every
  boundary-flat native vector the energy is at least
  `−S e^{aL} L (1 + (2πK/L)²)² (2K + 1) ‖x‖²`, with `S = ∑ m_ρ / (1 + |γ_ρ|²)`.
* `fixedRateMomentSliceBounds_of_re_le`: any proved half-plane `Re ρ ≤ θ` gives
  both parities at every rate above `θ − 1/2`.
* `fixedRateMomentSliceBounds_of_half_lt`: the unconditional rates above `1/2`.
* Sharp interfaces. With every zero on the line, the critical-line positivity
  already in the repository gives both slice bounds with error zero. So each
  of the slice contracts (C1), (SB), (PG) and (SE) is equivalent to Mathlib
  `RiemannHypothesis`: `riemannHypothesis_iff_cofinal_moment_slice_bounds`,
  `…_cofinal_moment_slice_semibounded`, `…_fixed_parity_polynomial`,
  `…_fixed_parity_subexponential`. None is weaker or stronger than RH.

Step 4 is the statement that the rate can be taken to zero. The trivial rate is
`1/2`. An external zero-free half-plane, once imported and audited, would give a
fixed rate below it (about `0.373` for the boundary `0.8733819666133` recorded in
the handover). No inspected statement lets the rate tend to zero.

## What is ruled out, and what is not

Ruled out as closing mechanisms:

* any argument that derives the response bound from positivity on the selected
  predecessor together with approximation of the source inside it;
* a loading-ratio or angle law for (F) beyond the energy bound itself;
* ground-state convergence as an independent route: identifying the near-radical
  vector with the ground vector needs the absence of eigenvalues below it, which
  is canonical positivity.

Not ruled out: a direct arithmetic bound for the scalar `E_e(L)` or for the
energy of `Z`. That is the original problem. The model used above has no Euler
product, so it refutes only arguments that do not use the divisor identities.

## Finite certificates

[bottom_certificate.py](../bottom_certificate.py) certifies, by ball-arithmetic
inertia, that the bottom eigenvalue is positive and simple on six constrained
spaces at `L = 2` (cutoff 16) and at `L = 3` (cutoff 81). With the native
real-root lemma of the round-7 note (paper level), the ground transforms there
have only zeros `z` with `z²` real. These are statements about those finite
objects only.

## Where things are

| Item | Location |
|---|---|
| Round-7 note (repository edition; the Drive file has sha256 `14071c2c…de947`) | [ROUND7_SELECTED_PREDECESSOR_AND_SCALAR_TARGET.md](ROUND7_SELECTED_PREDECESSOR_AND_SCALAR_TARGET.md) |
| Floor adapter and graded equivalence (M60) | `Zeta23/OPICARound4/ArithmeticFrontier/ZeroFreeFloor.lean` |
| Least-crossing statement (M61) | `Zeta23/OPICARound4/ArithmeticFrontier/SelectedCutoff.lean` |
| Records | [evidence/increment6a](../evidence/increment6a/SUMMARY.json) |
| Tools | [bottom_certificate.py](../bottom_certificate.py), [spectral_lowdeg.py](../spectral_lowdeg.py), [selector_model.py](../selector_model.py) |

The note names the scratch scripts of the session that produced it. The
repository tools above are rewrites in ball arithmetic; the records were
regenerated with them and reproduce the scratch values.

One wording correction. The note's first table says the even cutoff-3 values
agree "to 14-16 digits". The data, then and now, show relative differences from
`8e-17` to `9e-14`, which is 13 to 16 digits. The repository edition keeps the
original sentence. It differs from the Drive file only in its author line and in
two file titles.

## Decision rule for the next rounds

1. A proposed supplier must lower the rate `α` in `E_e(L) ≥ −C e^{αL}`, or the
   equivalent energy rate for `Z`. A reformulation that leaves the rate at `1/2`
   is not progress on Step 4.
2. An imported zero-free half-plane enters through
   `fixedRateMomentSliceBounds_of_re_le`, with its own complete proof and axiom
   audit. It yields a fixed rate, not closure.
3. Closure needs the rate to reach zero. No mechanism for that is known here.
