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

**Post-#138 clarification:** neither the regular-aperture route nor the later Schur-energy route revives DR-012. A4R uses exact canonical aperture dependence only to select a regular witness; the eventual sign theorem must spend exact source arithmetic.

## DR-013 — displacement identity alone excludes the first-bad state

Use the exact centered displacement identity / low displacement rank as the decisive contradiction.

**Status:** quarantined by diagonal-perturbation countermodels.

## DR-014 — universal raw source-moment positivity

Attempt to prove universal positivity/nonnegativity of `explicitCanonicalSourceMoment L K v` on the whole legal vector space.

**Status:** structurally dead after PR #131 because the observable is linear in `v` and changes sign under negation unless zero.

## DR-015 — factorwise alpha / Gamma / overlap / source-moment exclusion

Try to close the first-bad state by proving from the generic transfer package that one transfer factor has a fixed sign or cannot vanish, or by dividing the transfer equation by such a factor.

**Status:** quarantined by exact rational post-#129 countermodels and unchanged by #134/#137.

No argument may divide by `alpha`, `Gamma`, overlap, source moment, `Gamma0`, or `mu(z)` without a separate theorem.

## DR-016 — shift-invariant transfer data determine absolute spectral sign

Attempt to infer absolute negative spectral location using only the shift-invariant transfer package.

**Status:** structurally unavailable in generic models.

PR #136 restores scalar-sensitive self-energy and #137 extends that absolute normalization to exact source pairing/determinant. Any argument that drops the scalar correction or otherwise becomes shift-blind falls back into DR-016.

## DR-017 — domination proved by restating successor positivity

Attempt to close A4b2b by assuming, invoking, or merely renaming positivity of the successor block, absence of the negative root, or `canonicalOneStepDomination` itself.

**Status:** dead by circularity / zero information gain after PR #137; strengthened post-#138.

Under predecessor nonnegativity and a one-dimensional shell, the Astra audit derives the exact equivalence

```text
q_c>=0 AND forall w, Delta(w)>=0
  <-> successor one-step quadratic form >=0.
```

Universal domination remains a valid sufficient closing theorem, but it does **not** count as a reduction of the RH obstruction unless it is obtained from an independently justified canonical arithmetic mechanism.

**Changed-premise requirement for revival as the primary route:** exhibit a source-specific theorem — e.g. a genuinely positive representation, exact combined-channel remainder, or independent arithmetic inequality — whose premises do not already encode successor positivity or RH-strength Weil positivity.

## DR-018 — atom-by-atom positive determinant / SOS

Attempt to prove the #137 determinant nonnegative by proving each elementary canonical source atom has a nonnegative two-vector determinant and summing positive pieces.

**Status:** quarantined by the post-#138 Astra symbolic audit.

The reported first nonzero two-vector determinant coefficient of an elementary source atom is negative on the tested boundary-flat predecessor/shell sectors, with leading determinant orders `omega^18` in odd parity and `omega^22` in even parity.

**Consequence:** the old `omega^7 / omega^9` cancellation signal does not support atomwise determinant positivity. A full-source mixed-channel cancellation identity remains possible and is not killed by this route record.

**Evidence class:** external DERIVED/symbolic result; repository reproduction pending. Do not promote to Lean theorem authority.

## DR-019 — correction-vector independence in the #134 kernel transport

Attempt to force factorwise kernel/source conclusions by treating the two odd predecessor correction vectors `a` and `d` as independent directions.

**Status:** quarantined pending formalization of the post-#138 geometric identity

```text
d = -(6/(2*N-1)) a.
```

The identity was reported with exact rational checks for `K=2,...,30` and an elementary power-sum derivation. Until Lean-locked, treat it as external DERIVED evidence, but do not invest in an independence argument contradicted by the available exact checks.

## DR-020 — independent coarse channel majorants for the regular Schur sign

Attempt to prove `Ecanonical(c-A^-1b)>=0` by separately bounding the absolute magnitudes of pole, archimedean, scalar and prime channels with large slack, without exploiting their exact cancellation.

**Status:** quarantined as a default strategy by post-#138 numerical conditioning signals.

Sampled canonical regular endpoints were reported as residues of cancellation with an absolute-channel/final-value ratio around `6.46e20` in one small case. This does not prove every coarse-majorant strategy impossible, but any proposed bound must demonstrate enough correlated structure to survive that conditioning.

**Escape requirement:** exact paired-channel cancellation, a sharp source-specific remainder, or a rigorously quantified bound shown by interval-certified tests to resolve the observed cancellation scale.

**RH remains OPEN.**