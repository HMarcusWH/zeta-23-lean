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

## DR-007 — naïve finiteMatrix = ambient QW restriction

Identify the historical printed-normalization `finiteMatrix` directly with the external finite restriction `QW_lambda|E_N`.

**Status:** forbidden.

PRs #71/#73 showed that the direct Section-4 source authority is the canonical cutoff-free object, while `finiteMatrix` is the frozen later printed normalization. The objects differ by a scalar identity shift.

## DR-008 — generic R002 taper-grid = canonical CCM

Treat the production R002 smooth-taper `G-tilde(T)` as merely the canonical CCM finite matrix in another basis.

**Status:** refuted as a generic identity / classified SPECIALIZATION_ONLY by D0-R (#66).

## DR-009 — Bombieri finite truncation = deterministic CCM Fourier band

Directly identify Bombieri's finite zero-index matrix with the deterministic centered Fourier-mode CCM matrix.

**Status:** not supported by the source audit / quarantined.

## DR-010 — fitted small commutator -> eigenvector convergence

Infer useful eigenvector convergence from a numerically fitted symmetric tridiagonal generator because its normalized commutator with the finite CCM matrix is small.

**Status:** falsified as a route in its present form.

A revival requires an analytically specified generator plus separate absolute commutator and spectral-gap theorems.

## DR-011 — legacy absolute spectrum as canonical source spectrum

Use absolute eigenvalues, inertia, PSD, trace, determinant or lower bounds computed from legacy printed `finiteMatrix` as if they were canonical source spectral data.

**Status:** forbidden semantic shortcut.

The canonical and legacy matrices differ by a scalar identity shift. Only shift-invariant information transports automatically.

## DR-012 — generic shell/Schur/parity/KKT first-bad exclusion

Attempt to exclude the global first-bad negative state using only generic Hermitianity, predecessor nonnegativity, one-dimensional shell, Schur endpoint, resonance classification, rank-one parity defect, KKT geometry and first-bad ancestry without actual canonical source values.

**Status:** quarantined by post-#128 countermodels.

**Post-#137 clarification:** the live determinant route is not a revival of DR-012. It explicitly consumes the scalar-sensitive canonical source energy/pairing from #136/#137. Generic structure remains insufficient.

## DR-013 — displacement identity alone excludes the first-bad state

Use the exact centered displacement identity / low displacement rank as the decisive contradiction.

**Status:** quarantined by diagonal-perturbation countermodels.

## DR-014 — universal raw source-moment positivity

Attempt to prove universal positivity/nonnegativity of `explicitCanonicalSourceMoment L K v` on the whole legal vector space.

**Status:** structurally dead after PR #131 because the observable is linear in `v` and changes sign under negation unless zero.

**Post-#137 clarification:** the quadratic one-step determinant is a different object and does not revive raw linear source-moment positivity.

## DR-015 — factorwise `alpha` / `Gamma` / overlap / source-moment exclusion

Try to close the first-bad state by proving from the generic transfer package that one transfer factor has a fixed sign or cannot vanish, or by dividing the transfer equation by such a factor.

**Status:** quarantined by exact rational post-#129 countermodels and unchanged by #134/#137.

**Post-#137 clarification:** the determinant route avoids these factors. It should not carry DR-015 as a dead-route revival blocker, but DR-015 remains a permanent firewall against factorwise shortcuts.

## DR-016 — shift-invariant transfer data determine absolute spectral sign

Attempt to infer absolute negative spectral location using only the shift-invariant transfer package.

**Status:** structurally unavailable in generic models.

Under `M -> M+tI`, `lambda -> lambda+t`, the old transfer data can remain unchanged while the spectrum moves relative to zero.

**Post-#137 status:** #136 restores scalar-sensitive self-energy and #137 extends that absolute normalization to the exact source pairing/determinant. The live determinant route is therefore not a revival of DR-016. Any argument that drops the scalar correction or otherwise becomes shift-blind falls back into DR-016.

## DR-017 — domination proved by restating successor positivity

Attempt to close A4b2b by assuming, invoking, or merely renaming the positivity of the successor one-step block, the absence of the negative root, or `canonicalOneStepDomination` itself.

**Status:** dead by circularity / zero information gain after PR #137.

With predecessor nonnegativity and a one-dimensional shell,

```text
q_c>=0
forall w, Δ(w)>=0
```

is essentially the missing one-step block-positivity content. PR #137 proves this certificate is sufficient; it does not provide a cheaper proof of the certificate.

**Changed-premise requirement for any apparent revival:** provide an independent canonical arithmetic mechanism — such as a positive Gram/integral representation, exact source cancellation, or sum-of-squares identity — whose premises do not already encode the desired successor positivity or RH-strength conclusion.

**RH remains OPEN.**
