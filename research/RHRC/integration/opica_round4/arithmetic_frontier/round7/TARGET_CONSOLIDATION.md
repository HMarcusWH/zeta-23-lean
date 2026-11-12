# Step 4 target consolidation after round 7

11 November 2026. Parent head `b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`.
**Register and navigation document. RH and Step 4 remain OPEN.** The paper
derivations cited here are DERIVED and not independently reviewed; the new Lean
statements are compiled locally on the pinned toolchain and need current-head CI.

## The three open suppliers are one

The November handovers list three alternative sufficient tasks for the fixed
source `h` and its complete prime field `Z`:

* (U): a cofinal bound for the weighted response `A_Z(T)` at every positive rate;
* (F): a lower bound for the loading ratio of the reconstructed vector `v_L`;
* (E): a cofinal bound for the predecessor defect `E_L` under a hypothetical zero.

Round 7 shows that they are the same growth bound for `Z`, in three norms, at
every positive rate (see the corrections at the end for fixed rates).

| Target | What it is | Why |
|---|---|---|
| (U) | weighted `L¹` growth of `Z` | definition |
| (F) | weighted `L²` growth of `Z` | the numerator `‖N v_L‖²` tends to the fixed positive constant `‖U‖²`, so the ratio is the reciprocal of the weighted energy |
| (E) | plain `L²` growth of `Z` at horizon `L − c₀` | at arbitrarily late apertures the least-crossing cutoff is 3, the predecessor is `{0}`, and the defect is the complete source column |

At every positive rate each of them excludes every off-line zero and is implied
by the absence of such zeros. The quantities of (E) and (F) are squared norms, so
at a fixed rate they grow at twice the rate of the field and a fixed-rate statement
must track the squaring. None is a weaker intermediate of another: (E) and (F) are
not easier suppliers, and an independent proof of either would itself prove the
energy bound.

## What the selector does under a hypothetical zero

* Derived, no dominance assumption: for every `β < δ` there are arbitrarily late
  apertures where one of the two cutoff-3 unit vectors has energy below
  `−e^{βL}`. Any packet at such an aperture with depth `D ≤ 2e^{βL}` has stored
  cutoff 3 and both predecessor spaces zero. That finite implication is compiled
  in the last section of `ZeroFreeFloor.lean` (M61). Without a dominance
  assumption the note does not show that these apertures are the ones the
  compiled production detector selects.
* Derived, dominant zero: the cutoff is 3 or 4 at every late aperture, so the
  predecessor has dimension 0 or 2.
* Model illustration (one added off-line quadruple; not the zeta function):
  [evidence/increment6a](../evidence/increment6a/SUMMARY.json). In both parameter
  sets every sampled aperture beyond a transient has cutoff 3 or 4.

Round 6's cubic ceiling is therefore a constant ceiling on those packets. Under
a dominant zero, the positive predecessor that inequality (P) relies on is empty or
two-dimensional at every late aperture. Without that assumption this is shown only
on a cofinal set, and that set is not shown to meet the production family.

## The weakest form of the remaining target

Let `E_e(L)` be the canonical energy of the unit vector of the even cutoff-3
pole-neutral boundary-flat space. Its transform is explicit:
`R(z) = c_e (z² − 1/4) / (z ∏_{a≤3} (z² + (2πa/L)²))`.

* Derived: `sup Re ρ − 1/2` equals the least exponential rate at which `E_e` is
  bounded below. In particular RH holds if and only if `E_e(L) ≥ 0` for all large
  `L`, and under RH `0 < E_e(L) ≤ 12.94 / L⁵` (sharpened to `O(L⁻¹³)`; see the
  corrections).
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
`1/2`, and the established literature has no better one: a rate below `1/2` is a
zero-free half-plane `Re s > θ₀` with `θ₀ < 1`, which is the quasi-Riemann
hypothesis.

The repository records external claims of such half-planes (`7/8` and
`0.8733819666133`; see `MADNESS.md` and `MADNESS_SOURCE_AUDIT.json`). They are not
imported, and this round did not verify them. If one of them is correct, it is a
major theorem in its own right and gives a fixed rate near `0.375`. Otherwise the
rate stays at `1/2`. No inspected statement lets the rate tend to zero.

## What is ruled out, and what is not

Ruled out as closing mechanisms, in the forms stated:

* an argument that derives the response bound from positivity on the selected
  predecessor together with approximation of the source inside it, wherever the
  predecessor is empty (every late aperture under a dominant zero; otherwise only
  where the production family meets the cofinal set above);
* a loading-ratio or angle law for (F) as a weaker substitute for the energy
  bound (an independent proof of the angle law would itself prove that bound);
* ground-state convergence proved by assuming the absence of eigenvalues below
  the near-radical vector, which is canonical positivity. That version is
  circular; other proofs of convergence are not ruled out.

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
| Least-crossing statement (M61) | last section of `Zeta23/OPICARound4/ArithmeticFrontier/ZeroFreeFloor.lean` |
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

A second correction. Section 9, item 4 of the note says that the external family
bootstrap "has moved alpha below 1/2". That holds only if the external half-plane
claims are correct. They amount to the quasi-Riemann hypothesis and were not
verified in this round.

## Decision rule for the next rounds

1. A proposed supplier must lower the rate `α` in `E_e(L) ≥ −C e^{αL}`, or the
   equivalent energy rate for `Z`. A reformulation that leaves the rate at `1/2`
   is not progress on Step 4.
2. A zero-free half-plane enters through `fixedRateMomentSliceBounds_of_re_le`,
   with its own complete proof and axiom audit. Any such half-plane is the
   quasi-Riemann hypothesis, so a claim of one stays unverified until that audit
   is done. It yields a fixed rate, not closure.
3. Closure needs the rate to reach zero. No mechanism for that is known here.

## Corrections (12 November, increment 6B)

The signed-aperture investigation (Drive, 01:48 UTC) and the endpoint-kernel audit
(Drive, 13:53 UTC) reviewed this document. Four corrections follow from them, and
the text above now carries them.

1. **Rates.** The quantities of (E) and (F) are squared norms. A field component
   that grows at rate `δ` gives squared energy at rate `2δ`. The every-positive-rate
   equivalence of (U), (F) and (E) is unaffected; fixed-rate correspondences must
   track the squaring. No quantitative equivalence of the full (E) and (F)
   contracts, with their horizons and packet choices, is established.
2. **What is ruled out.** Only the circular forms are ruled out: positivity on a
   predecessor where it is empty, an angle law used as a substitute for the energy
   bound, and convergence proofs that assume the missing positivity. An
   independent proof of an RH-equivalent target is not circular.
3. **Where the predecessor is empty.** Under a dominant zero this holds at every
   late aperture. Without one, it holds only on a cofinal set, which is not shown
   to meet the cofinal production family; two cofinal sets need not meet.
4. **Size under RH.** Under RH, the normalized scalar `T = w E_e` (with `w = L/c_e²`
   of degree 13) is uniformly bounded, so `E_e(L) = O(L⁻¹³)`. The bound
   `12.94 / L⁵` remains true but is weaker.

The successor register is [round8/MISSING_ARITHMETIC_SHAPE.md](../round8/MISSING_ARITHMETIC_SHAPE.md).
