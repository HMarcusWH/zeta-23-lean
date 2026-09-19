# Post-#222 bi-regular first-bad and zero-shift scalar normal-form delta

**Status:** GREEN theorem delta, pending merge.

**Validated theorem head:** `e42dbce1bbbc68b5cf9612e7c8a8dab2a2eca543`  
**Validated theorem tree:** `48d8752950c28e0d3bbd385646e71075abef9e76`  
**Validation run:** RHRC research and Lean checks #1215 / run `35447050111`.

Compiler/CI evidence on this exact head: `lake build Zeta23.CCM` PASS; `lake build Zeta23.ExceptionalZero` PASS; forbidden `sorry` / project-`axiom` scan PASS; RHRC Python/control suite PASS; R003 normalization/research audit PASS.

PR #221 is now the merged theorem authority. PR #222 is a separate validated theorem delta; no merge commit is claimed for #222.

# What became formally true

**PROVED.** `exists_open_fixedCell_intrinsicPredecessorRegular_persistence` makes predecessor regularity locally persistent inside one fixed cutoff cell.

**PROVED.** `exists_both_intrinsicPredecessorRegular_in_open_fixedCell` gives one aperture where even and odd predecessor blocks are simultaneously regular at the same predecessor size.

**PROVED.** `exists_biRegular_cellMinimal_firstBadCertificate` preserves the same strict negative first-bad witness, whole-cell minimality, and selected parity while moving to that bi-regular aperture.

**PROVED.** `exists_biRegular_cellMinimal_negativeCanonicalEnergyCertificate` carries the complete retained negative-energy state onto that exact aperture.

**PROVED.** Regularity annihilates every predecessor-kernel coordinate. On the bi-regular retained state the three distinct odd coordinates vanish independently: actual shell `K(b)`, #219 generator `K(a)`, and #220 transported-index `K(d)`.

**PROVED.** `cubicZeroShiftSchurEndpoint_re_eq_shellResponse_re_mul_norm_sq` gives `Re S₀ = Re σ₀ * ||c||²`.

**PROVED.** `successorParityBad_iff_zeroShiftShellResponse_re_neg` gives `ParityBad p ... ↔ Re σ_p < 0`; the complementary good sector is `0 ≤ Re σ_p`.

**PROVED.** `exists_evenOddZeroShiftScalarNormalForm_of_even` gives both zero-shift preimages, `Re σ_+ < 0`, the exact transfer `σ_- = α₀ σ_+ + Γ₀ μ₀`, and odd badness iff `Re σ_- < 0`.

# What changed

PR #221's retained resonant-or-regular-negative fork collapses to the regular sign branch on the strengthened retained state. Generic resonance theory remains valid outside this construction.

The #220 balance keeps its odd-good hypothesis. When that hypothesis applies here, both kernel terms are already zero, so it specializes to `0 = 0`; no unconditional strengthening of #220 is claimed.

# Upstream implications

The natural retained object is now bi-regular rather than selected-parity regular. Both parity zero-shift preimages are unique at the same aperture.

# Downstream implications

The even-selected/odd-successor problem is scalarized to the open sign of `Re(α₀ σ_+ + Γ₀ μ₀)`, with `Re σ_+ < 0` already proved. The odd-selected route remains OPEN because the direct transfer is currently even-to-odd.

# Resurrected routes

The exact source/moment machinery from #207-#213 becomes more relevant as possible same-state information about `μ₀`, `α₀`, or `Γ₀`. Generic resonant spectral-tube results remain valid but are downgraded for this retained state.

# New RH-relevant clues

**LEAD / HYPOTHESIS.** The remaining obstruction may be a canonical arithmetic sign or magnitude law for `α₀ σ_+ + Γ₀ μ₀`, rather than a matrix-kernel obstruction.

**LEAD / HYPOTHESIS.** At the bi-regular retained state the odd preimage is unique, so `α₀` and `Γ₀` are no longer choice-dependent there.

**OPEN.** #222 does not determine the transferred sign, exclude odd badness, exclude the selected negative root, close the finite-to-zeta seam, or prove RH.

# Falsification checks

- Final aperture stays in the same fixed cutoff cell.
- The same strict negative witness is retained; no witness is fitted after regularization.
- Both parities use the same predecessor size.
- `K(b)`, `K(a)`, and `K(d)` are not identified; they vanish because the target kernel is trivial.
- PR #205 is not contradicted: its simultaneous-bad countermodel has `canonical_realizability=false`; #222 uses canonical aperture analyticity.
- PR #215 remains intact; no universal source/M4 sign or proportionality is revived.
- No same-state contact theorem or RH-equivalent assumption is introduced.

# Highest-leverage next moves

1. Expand the real part of the exact transfer without breaking the correlations among `α₀`, `Γ₀`, and `μ₀`.
2. Characterize or bound the unique-preimage coefficients `α₀` and `Γ₀` from canonical arithmetic.
3. Reconnect `μ₀` to the complete source-functional/source-kernel results from #211-#213 at this same state.
4. Try to construct a canonical-realizable countermodel with negative transferred real part before attempting positivity.
5. Build the odd-selected mirror only after testing whether the scalar law is directional or parity-symmetric.

Next descriptive target: `RETAINED_BIREGULAR_ZERO_SHIFT_SCALAR_DISCRIMINATION`.

# Standing questions

Given everything now formally true, what becomes possible that was not possible before?

If the scalarized transfer contains an RH-relevant clue, where does it propagate upstream into source arithmetic or downstream into negative-root exclusion?

What lemma, countermodel, or bounded canonical experiment most efficiently decides whether `Re(α₀ σ_+ + Γ₀ μ₀)` is structurally constrained?

**OBS-059I remains OPEN. Negative-root exclusion remains OPEN. RH remains OPEN.**
