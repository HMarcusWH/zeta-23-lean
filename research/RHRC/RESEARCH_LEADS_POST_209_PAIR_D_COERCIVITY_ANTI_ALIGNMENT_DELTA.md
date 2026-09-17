# Post-#209 Pair-D coercivity / anti-alignment delta

> **Claim firewall: RH remains OPEN.**

PR #209 is a theorem-bearing PR. Its exact checked theorem head is `a6f0e5d3db988eeaf3ed54cf283f85b8d23f5392`; merged theorem commit `e029af769e01a547ebbc6ed045509bb2cbdd6cff`; merge tree `6a75278ebf3f2bd19a77419238872cb81835ec13`. The research-only evidence anchor remains PR #205.

# What became formally true

**PROVED.** PR #209 formalizes the quantitative Pair-D coercive estimate already latent in #207. For an even compressed eigenmode `v` with odd successor sector good,

```text
-lam * ||Dv||^2
  <= re (star(explicitCanonicalSourceMoment(v)) * M4(v)).
```

The generic theorem is

```text
neg_lam_mul_evenToOdd_norm_sq_le_re_star_explicitCanonicalSourceMoment_mul_momentFour_of_even_eigenmode_of_not_oddBad
```

PR #209 then composes that estimate with the exact #163 seventh mixed-source jet identity

```text
h_v^(7)(0) = -2 * (2*pi)^6 * M4(v)
```

and proves

```text
re (star(explicitCanonicalSourceMoment(v)) * h_v^(7)(0))
  <= 2 * (2*pi)^6 * lam * ||Dv||^2.
```

For `lam < 0` and `v != 0`, injectivity of the centered-index map makes the right-hand side strictly negative, hence

```text
re (star(explicitCanonicalSourceMoment(v)) * h_v^(7)(0)) < 0.
```

The retained theorem package includes

```text
evenShiftedSourceMomentMomentFour_coercive_of_even_of_not_oddBad
evenShiftedSourceMomentMixedJet_re_le_of_even_of_not_oddBad
evenShiftedSourceMomentMixedJet_re_neg_of_even_of_not_oddBad
oddBad_or_sourceMomentMixedJet_re_neg_of_even
evenShiftedRieszEight_eq_nine_iff_endpointScalar_eq_zero_of_even_of_not_oddBad
```

Thus the exact retained even-selected first-bad state now satisfies

```text
odd successor bad
OR
re(star(sourceMoment) * mixedSeventhJet) < 0.
```

On the retained even-selected odd-good branch, the mixed seventh jet is nonzero and the Riesz-8/Riesz-9 boundary is nondegenerate:

```text
R8 = R9
  <-> canonicalPolePrimeRieszEndpointScalar L 8 = 0.
```

No sign theorem for the endpoint scalar is proved.

# What changed

PR #207 proved qualitative orientation and factor nonvanishing:

```text
0 < re(star(sourceMoment) * M4)
sourceMoment != 0
M4 != 0
mixed seventh jet != 0
```

PR #209 strengthens that branch to a **quantitative compensation law** and then to a **strict complete-source/local-jet anti-alignment law**. The prior three-step execution plan

```text
1. formalize coercivity generically;
2. specialize to evenShiftedTrial;
3. compose with #163 mixed-jet / Riesz boundary identities;
```

is now CLOSED / PROVED BY #209.

The active frontier moves to a genuinely independent canonical-arithmetic incompatibility on the same state.

# Upstream implications

The useful abstract interface is now

```text
S(v) = explicitCanonicalSourceMoment L K v
J7(v) = iteratedDeriv 7 (quadraticNormalSourceAtom K v) 0
```

with the exact relation

```text
J7(v) = -2 * (2*pi)^6 * M4(v).
```

The #209 theorem therefore constrains the complete pole/archimedean/prime source functional and a local seventh jet of the same source observable. Any upstream refactor should preserve that complete functional and its cancellations; #199/#201 remain warnings against splitting source terms and losing correlation.

A straightforward **DERIVED** consequence, not yet separately formalized, is the magnitude budget

```text
2 * (2*pi)^6 * (-lam) * ||Dv||^2
  <= |explicitCanonicalSourceMoment(v)| * |J7(v)|
```

on a genuine negative even eigenmode with odd successor good.

# Downstream implications

The current Pair-D split becomes

```text
generic structural simultaneous-bad exclusion
  = FALSIFIED / CONSUMED BY #205

even-selected + odd-good retained branch
  = PROVED THROUGH #209
  = quantitative sourceMoment/M4 coercivity
  = strict sourceMoment/seventh-jet anti-alignment
  = nondegenerate Riesz-8/Riesz-9 boundary

canonical simultaneous odd-bad branch
  = OPEN

odd-selected first-bad branch
  = OPEN

independent same-state canonical incompatibility
  = OPEN / ACTIVE

terminal FB-05 incompatibility
  = OPEN
```

The next theorem/research target must not be another rearrangement of the same #207/#209 odd-sector energy identity. It must supply genuinely new information about the complete canonical source functional, the retained state, or the Riesz hierarchy.

# Resurrected routes

The post-#163/#165 Riesz endpoint route becomes **REACTIVATED / NONDEGENERATE ON THE EVEN-SELECTED ODD-GOOD BRANCH** because #209 removes the `J7 = 0` escape hatch there.

If a later independent theorem proves

```text
canonicalPolePrimeRieszEndpointScalar L 8 > 0,
```

then the exact boundary identity would force `R9 < R8`; and the retained state already has `R8 < 0`. This still is not a contradiction by itself. No high-order Riesz limit-to-zero or eventual nonnegativity theorem is currently part of this post-#209 state.

# New RH-relevant clues

**LEAD / HYPOTHESIS — complete-functional sign incompatibility.** Seek an independent canonical theorem of the schematic form

```text
0 <= re(star(Λ_L(h)) * h^(7)(0))
```

or another lower bound incompatible with #209's strict negative requirement.

**LEAD / HYPOTHESIS — magnitude incompatibility.** An independent upper bound on

```text
|Λ_L(h)| * |h^(7)(0)|
```

that lies below the #209 compulsory energy budget would also exclude the odd-good branch without requiring an opposite sign theorem.

**LEAD / HYPOTHESIS — Riesz hierarchy.** Search for a genuinely independent high-order limit, compactness, or eventual sign statement which, together with the now-nondegenerate boundary recurrence, would make repeated boundary descent impossible.

# Falsification checks

- A universal opposite-sign theorem may fail on generic source atoms; test that cheaply before theorem investment.
- Do not derive the proposed opposing bound by algebraically rearranging the same odd-sector nonnegativity identity used in #209.
- Do not split pole/archimedean/prime pieces and bound them independently unless cancellation loss is proved harmless; #199/#201 already show that representation dependency is dangerous.
- Endpoint-scalar positivity remains OPEN.
- `R9 < R8 < 0` alone would not close FB-05.
- The simultaneous odd-bad branch remains OPEN.
- The odd-selected first-bad branch remains OPEN.
- Negative-root exclusion remains OPEN.
- **RH remains OPEN.**

# Highest-leverage next moves

1. Synchronize all living docs/control to exact theorem authority #209 while retaining #205 as research evidence and #117 as control semantic authority.
2. Preregister a cheap falsification pass for independent complete-functional sign or magnitude restrictions before another large Lean theorem investment.
3. Prefer the complete canonical source functional over another source-component decomposition.
4. Re-audit the Riesz hierarchy for an independent high-order limit/nonnegativity statement now that the mixed-jet factor is provably nonzero on the retained odd-good branch.
5. Keep the simultaneous odd-bad and odd-selected branches explicitly open.
6. Keep Pair B secondary unless the canonical Pair-D complete-functional route stalls.

# Standing questions

Given everything that is now formally true, what becomes possible that was not possible before?

A hypothetical retained even-selected, odd-good negative state must now satisfy a quantitative complete-source/local-jet anti-alignment, not merely factor nonvanishing.

If this contains a clue toward RH, where does that clue propagate upstream or downstream through the existing mathematics?

It propagates upstream into the exact complete canonical source functional and downstream into the nondegenerate Riesz-8/Riesz-9 boundary recurrence.

What experiment, lemma, reformulation, or connection would most efficiently tell us whether that clue is real?

Falsify candidate independent sign/magnitude restrictions on the exact source-atom class before formalizing them. If one survives, prove it on the same canonical retained state and compose it directly with #209.

The selected formal first break remains `E4A4-SCHUR-FB-05`. R003 remains `DISCOVERY`; confirmatory execution is not authorized. Negative-root exclusion remains OPEN. **RH remains OPEN.**