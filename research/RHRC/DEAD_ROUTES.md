# Dead and quarantined routes

A route is listed here when it fails for a reusable reason. Failure is a valid research output.

Do not silently resurrect a dead route. A revival must state **which blocking premise changed** and why that change is theorem-relevant.

## DR-001 — TightMult-visible scalar improvement

Improve RH by a new scalar inequality consuming only the TightMult-visible single-compression statistics.

**Blocked by:** OBS-001.

## DR-002 — fixed local-ordinal zeta mapping

Use a fixed local-ordinal map as a bridge from finite CCM objects to zeta zeros.

**Status:** rejected in the earlier CCM campaign.

## DR-003 — curvature_gap W96 hidden field

Treat `curvature_gap` W96 as an RH field.

**Status:** rejected by matched adversarial null and transfer failure.

## DR-004 — MV square-root-cancellation shortcut for R001

Close `R001_PRIME_UPPER` by xi-modulation averaging plus Montgomery--Vaughan mean value.

**Blocked by:** exponent bookkeeping; detection still requires delta > 1/2. Reviving this route requires removing the MV additive `sum n|c_n|^2` penalty at the needed scale, which is already RH/zero-density-strength information.

## DR-005 — independent scalar arithmetic closure of R001

Treat `R001_PRIME_UPPER` as "one more prime estimate."

**Blocked by:** OBS-008. The exact scalar target is Lean-proved RH-equivalent.

## DR-006 — killed R002 observable families

Killed in `routes/R002_multi_probe/MULTI_PROBE_GRAM_OPERATOR_FEASIBILITY_2026_08_21.md`:

- odd moment `tr G-tilde^3` — requires unavailable ternary Lambda-correlation precision;
- L2 aperture coherence — collapses to OBS-008;
- full-diagonal majorization — delta-insensitive at leading order.

## DR-007 — naive finiteMatrix = ambient QW restriction

Identify the historical printed-normalization `finiteMatrix` directly with the external finite restriction `QW_lambda|E_N`.

**Status:** forbidden. PRs #71/#73 showed that the direct Section-4 source authority is the canonical cutoff-free object, while `finiteMatrix` is the frozen later printed normalization. The objects differ by a scalar identity shift.

## DR-008 — generic R002 taper-grid = canonical CCM

Treat the production R002 smooth-taper family as merely the canonical CCM finite matrix in another basis.

**Status:** refuted as a generic identity / classified SPECIALIZATION_ONLY by D0-R (#66).

## DR-009 — Bombieri finite truncation = deterministic CCM Fourier band

Directly identify Bombieri's finite zero-index matrix with the deterministic centered Fourier-mode CCM matrix.

**Status:** not supported by the source audit / quarantined.

## DR-010 — fitted small commutator -> eigenvector convergence

Infer useful eigenvector convergence from a numerically fitted symmetric tridiagonal generator because its normalized commutator with the finite CCM matrix is small.

**Status:** falsified as a route in its present form. A revival requires an analytically specified generator plus separate absolute commutator and spectral-gap theorems.

## DR-011 — legacy absolute spectrum as canonical source spectrum

Use absolute eigenvalues, inertia, PSD, trace, determinant or lower bounds computed from legacy printed `finiteMatrix` as if they were canonical source spectral data.

**Status:** forbidden semantic shortcut. The canonical and legacy matrices differ by a scalar identity shift. Only shift-invariant information transports automatically.

## DR-012 — generic shell/Schur/parity/KKT first-bad exclusion

Attempt to exclude the global first-bad negative state using only generic Hermitianity, predecessor nonnegativity, one-dimensional shell, Schur endpoint, resonance classification, rank-one parity defect, KKT geometry and first-bad ancestry without actual canonical source values.

**Status:** quarantined by post-#128 countermodels.

**Post-#150 clarification:** #150 removes selected-predecessor singularity but does not revive DR-012. The final sign theorem must spend actual canonical arithmetic.

## DR-013 — displacement identity alone excludes the first-bad state

Use the exact centered displacement identity / low displacement rank as the decisive contradiction.

**Status:** quarantined by diagonal-perturbation countermodels.

## DR-014 — universal raw source-moment positivity

Attempt to prove universal positivity/nonnegativity of `explicitCanonicalSourceMoment L K v` on the whole legal vector space.

**Status:** structurally dead after PR #131 because the observable is linear in `v` and changes sign under negation unless zero.

## DR-015 — factorwise alpha / Gamma / overlap / source-moment exclusion

Try to close the first-bad state by proving from the generic transfer package that one transfer factor has a fixed sign or cannot vanish, or by dividing the transfer equation by such a factor.

**Status:** quarantined by exact rational post-#129 countermodels and unchanged by #134/#137/#150.

No argument may divide by `alpha`, `Gamma`, overlap, source moment, `Gamma0`, or `mu(z)` without a separate theorem.

## DR-016 — shift-invariant transfer data determine absolute spectral sign

Attempt to infer absolute negative spectral location using only the shift-invariant transfer package.

**Status:** structurally unavailable in generic models.

PR #136 restores scalar-sensitive self-energy and #137 extends that absolute normalization to exact source pairing/determinant. Any argument that drops the scalar correction or otherwise becomes shift-blind falls back into DR-016.

## DR-017 — domination proved by restating successor positivity

Attempt to close A4b2b by assuming, invoking, or merely renaming positivity of the successor block, absence of the negative root, or `canonicalOneStepDomination` itself.

**Status:** dead by circularity / zero information gain after PR #137; strengthened post-#138.

Under predecessor nonnegativity and a one-dimensional shell, the Astra audit derives

```text
q_c>=0 AND forall w, Delta(w)>=0
  <-> successor one-step quadratic form >=0.
```

Universal domination remains a valid sufficient closing theorem, but it does **not** count as a reduction unless obtained from an independently justified canonical arithmetic mechanism.

## DR-018 — atom-by-atom positive determinant / SOS

Attempt to prove the #137 determinant nonnegative by proving each elementary canonical source atom has a nonnegative two-vector determinant and summing positive pieces.

**Status:** quarantined by the post-#138 Astra symbolic audit.

The reported first nonzero two-vector determinant coefficient is negative on tested boundary-flat predecessor/shell sectors, with leading determinant orders `omega^18` in odd parity and `omega^22` in even parity.

**Evidence class:** external DERIVED/symbolic; repository theoremization pending.

## DR-019 — correction-vector independence in the #134 kernel transport

Attempt to force factorwise kernel/source conclusions by treating the two odd predecessor correction vectors `a` and `d` as independent directions.

**Status:** quarantined pending formalization of the post-#138 identity

```text
d = -(6/(2*N-1)) a.
```

Until Lean-locked, treat it as external DERIVED evidence, but do not invest in an independence argument contradicted by exact checks.

## DR-020 — independent coarse channel majorants for the regular Schur sign

Attempt to prove `Ecanonical(c-A^-1b)>=0` by separately bounding the absolute magnitudes of pole, archimedean, scalar and prime channels with large slack, without exploiting their exact cancellation.

**Status:** quarantined as a default strategy by post-#138 and post-#150 numerical conditioning signals.

The final regular Schur endpoint can be a tiny residue of much larger channel terms. Any proposed separated bound must demonstrate enough correlated structure to survive that conditioning.

**Escape requirement:** exact paired-channel cancellation, a sharp source-specific remainder, or rigorously quantified interval-certified bounds resolving the observed cancellation scale.

## DR-021 — global aperture Loewner monotonicity

Attempt to prove the selected canonical sign by showing the full canonical matrix family is globally monotone in Loewner order as aperture varies.

**Status:** quarantined as a default route by post-#150 EXPERIMENTAL SIGNAL.

Canonical derivative probes exhibit mixed spectral signs rather than a uniform positive- or negative-semidefinite derivative.

**Revival requirement:** narrow the theorem to the exact selected residual/subspace and prove that the mixed-sign modes are irrelevant, with rigorous certification.

## DR-022 — global minimizing-trial Schur monotonicity

Attempt to prove the final sign from a global monotonicity theorem for the regular zero-shift Schur value `S(L)`.

**Status:** quarantined as a default route by post-#150 EXPERIMENTAL SIGNAL.

The derivative of the minimizing-trial Schur value changes sign in tested canonical aperture ranges.

The envelope identity `S'(L)=<M'(L)u(L),u(L)>`, if theoremized, remains useful diagnostically; it does not imply a fixed sign.

## DR-023 — universal positive elementary source-atom energy

Attempt to represent the selected residual energy as a sum/integral of elementary source atoms each having nonnegative quadratic energy on the relevant canonical trial.

**Status:** quarantined as a default route by post-#150 EXPERIMENTAL SIGNAL.

Tested elementary atom energies change sign. A transformed discrepancy or full-source mixed cancellation may still admit a useful sign and is not killed by this record.

## Coordinate-mismatch warning — not a dead route ID

The scalar identity

```text
L*(exp L+1)/(exp L-1)=L*coth(L/2)
```

uses the complex aperture coordinate `L`, whereas #150 deck translation acts on the log-cover coordinate `z` after `L=exp z`.

Therefore a direct “same `2*pi*i` lattice -> same resolvent” argument is **downgraded**, not established. Reviving it requires an explicit transform/conjugacy theorem connecting the two coordinates.

**RH remains OPEN.**
