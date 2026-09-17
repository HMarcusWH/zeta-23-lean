# Post-#207 Pair-D source/M4 theorem delta

> **Claim firewall: RH remains OPEN.**

PR #207 is a theorem-bearing PR. Its exact checked head is `7e186ede13beece95e8a08b2449cd3accbe5b2f5`; merge commit `76cf4e3b5ef4b7ab904a861b6d4cb01fdcd8d0e0`; merge tree `d6509407cc7b667b0ff3e7faab2acd525ae32db9`. The research-only evidence anchor remains PR #205.

# What became formally true

**PROVED.** For an even constrained negative compressed eigenmode `v` with eigenvalue `lam < 0`, the centered-index image in the odd sector satisfies the exact operator identity

```text
T_odd(Dv) = lam * Dv + explicitCanonicalSourceMoment(v) * g3
```

and the exact self-energy identity

```text
re <T_odd(Dv), Dv>
  = lam * ||Dv||^2
    + re (star(explicitCanonicalSourceMoment(v)) * M4(v)).
```

The generic headline theorem is

```text
re_star_explicitCanonicalSourceMoment_mul_momentFour_pos_of_even_negative_eigenmode_of_not_oddBad
```

which proves, under the odd-good hypothesis,

```text
0 < re (star(explicitCanonicalSourceMoment(v)) * M4(v)).
```

On the exact retained even-selected first-bad state, PR #207 proves:

```text
RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceMomentMomentFour_re_pos_of_even_of_not_oddBad
RegularCellMinimalNegativeEnergyCertificate.evenShiftedMomentFour_ne_zero_of_even_of_not_oddBad
RegularCellMinimalNegativeEnergyCertificate.evenShiftedMixedSourceSeventhJet_ne_zero_of_even_of_not_oddBad
RegularCellMinimalNegativeEnergyCertificate.oddBad_or_sourceMomentMomentFour_re_pos_of_even
RegularCellMinimalNegativeEnergyCertificate.oddBad_or_sourceMoment_momentFour_mixedJet_ne_zero_of_even
```

Thus, on the odd-good branch of the retained even-selected state, the exact canonical source moment, `M4`, and the #163 seventh mixed source jet are all nonzero, and the sourceMoment/M4 Hermitian pairing is strictly positive.

No unconditional theorem `explicitCanonicalSourceMoment != 0 -> M4 != 0` was proved.

# What changed

The theorem authority advances from PR #184 to PR #207. PR #184 remains historical theorem ancestry; PR #207 composes later parity/source infrastructure into a new exact canonical Pair-D rigidity theorem.

The planned post-#205 generic defect-versus-`M4` falsifier is now **SUPERSEDED / UNNECESSARY AS THE NEXT STEP**. It was not executed and was not falsified. PR #207 found a better conditional theorem: negative even eigenmode + opposite parity good forces a strictly positive sourceMoment/M4 pairing directly.

The research anchor does not move: PR #205 remains the latest research-only evidence, with `PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED` and `canonical_realizability=false`.

# Upstream implications

The centered-index map is now linked to the canonical fourth centered moment by the exact identity

```text
<oddCubicCompressionVector, Dv> = M4(v).
```

This makes the rank-one parity defect, canonical source moment, and fourth centered moment one theorem-backed energy package rather than three loosely related observables.

The generic C1 lesson from PR #205 is preserved: generic predecessor/parity/shell/displacement structure alone cannot exclude simultaneous badness. PR #207 succeeds only after spending the actual canonical source coefficient.

# Downstream implications

`OBS-059` now splits sharply:

```text
generic structural simultaneous-bad exclusion
  = FALSIFIED / CONSUMED BY #205

even-selected + odd-good retained branch
  = PROVED THROUGH #207
  = re(star(sourceMoment) * M4) > 0
  = sourceMoment != 0
  = M4 != 0
  = mixed seventh jet != 0

canonical simultaneous odd-bad branch
  = OPEN

odd-selected first-bad branch
  = OPEN

terminal FB-05 incompatibility / negative-root exclusion
  = OPEN
```

The strongest immediate downstream target is quantitative. The proof of the strict pairing already uses

```text
0 <= odd_energy
odd_energy = lam * ||Dv||^2 + pairing
lam < 0
```

so it suggests the coercive bound

```text
-lam * ||Dv||^2 <= re(star(sourceMoment) * M4).
```

This bound is **DERIVED / not yet separately formalized** in the repository.

# Resurrected routes

No dead route is resurrected. DR-012 and DR-013 remain strengthened by #205. Pair D survives only because #207 introduces genuinely canonical arithmetic absent from the C1 countermodel.

The #163 Riesz-8/Riesz-9 mixed-source boundary package becomes more relevant because PR #207 now proves the mixed seventh jet is nonzero on the retained odd-good branch rather than merely exposing a formula for it.

# New RH-relevant clues

**LEAD / HYPOTHESIS.** Formalize the quantitative coercivity inequality already latent in the #207 proof and transport it through the #163 identity

```text
iteratedDeriv 7 quadraticNormalSourceAtom 0
  = -2 * (2*pi)^6 * M4.
```

If an independent canonical/Riesz estimate can upper-bound the same coupling more sharply than the lower bound forced by negative energy, that could create the same-state contradiction FB-05 needs.

**LEAD / HYPOTHESIS.** The strict real-part orientation may matter more than factorwise nonvanishing. Any later arithmetic argument should preserve the phase/correlation information in `re(star(S) * M4)` rather than immediately discarding it to `S != 0` and `M4 != 0`.

# Falsification checks

- The simultaneous odd-bad branch is still allowed; PR #207 does not exclude it.
- `Dv` is not an odd eigenvector. The cubic defect is retained explicitly.
- The centered-index map is used algebraically/injectively, not as an isometry or unitary map.
- The theorem does not prove an unconditional sourceMoment-to-`M4` implication.
- The theorem is even-selected; there is no WLOG-even reduction, so odd-selected closure remains open.
- No endpoint scalar sign, global aperture monotonicity, finite-to-infinite closure, negative-root exclusion, or RH theorem follows automatically.

# Highest-leverage next moves

1. Synchronize living docs/control through the exact #207 theorem state.
2. Formalize the quantitative coercive lower bound already latent in the proof:
   `-lam * ||Dv||^2 <= re(star(sourceMoment) * M4)`.
3. Specialize that bound to `c.evenShiftedTrial`.
4. Compose it with the #163 mixed seventh-jet/Riesz boundary identity and look for an independent canonical upper bound or incompatibility.
5. Separately address the simultaneous odd-bad branch and the odd-selected first-bad branch.
6. Keep Pair B secondary unless the canonical Pair-D composition stalls.

# Standing questions

Given everything that is now formally true, what becomes possible that was not possible before?

The sourceMoment/`M4` relation no longer needs to be guessed from factorwise nonvanishing: on the retained even-selected odd-good branch it has a strict theorem-backed orientation.

If this contains a clue toward RH, where does that clue propagate upstream or downstream through the existing mathematics?

It propagates downstream into the #163 mixed seventh jet and Riesz boundary package, and upstream into the canonical rank-one parity defect that identifies the source coefficient.

What experiment, lemma, reformulation, or connection would most efficiently tell us whether that clue is real?

Formalize the quantitative coercivity inequality and ask whether the existing canonical arithmetic/Riesz machinery can independently upper-bound the same pairing on the same retained state.

The selected formal first break remains `E4A4-SCHUR-FB-05`. R003 remains `DISCOVERY`; confirmatory execution is not authorized. Negative-root exclusion remains OPEN. **RH remains OPEN.**
