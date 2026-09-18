# Post-#211 complete-functional representation delta

> **Claim firewall: RH remains OPEN.**

PR #211 is theorem-bearing authority. Validated theorem head `704a69e41871269814ba091e9476fe76b2d09844`; merged theorem commit `dd42e6368e48957c9922a9e917e10f60a2582b9f`; merge tree `a735f6149aeaa9f8358394c33fd6dcee8062f68e`. Latest research-only evidence remains PR #205. Control semantic authority remains PR #117.

# What became formally true

**PROVED.** The deterministic dictionary explicit-formula bridge now supports independent left/right coefficient vectors:

```text
literatureRHS_dictionaryMixedTest_eq_matrixCoefficientPairing
```

so the full literature RHS of the mixed dictionary test is exactly the corresponding coefficient pairing with `dictionaryMatrix`.

**PROVED.** For the exact active source observable
[
h_v(ω) = quadraticNormalSourceAtom K v ω,
]
PR #211 proves `quadraticNormalSourceAtom_zero` and `quadraticNormalSourceAtom_one`, hence (h_v(0)=h_v(1)=0).

**PROVED.** Define
[
Λ_L(h) = (1/2) * literatureRHS (canonicalSourcePhysicalLift L h).
]
Then

```text
explicitCanonicalSourceMoment_eq_completeSourceFunctional
```

proves
[
explicitCanonicalSourceMoment(L,K,v) = Λ_L(h_v).
]

The retained specialization is
```text
evenShiftedExplicitCanonicalSourceMoment_eq_completeSourceFunctional
```
and merged-green #209 can therefore be rewritten on the same retained state as
```text
evenShiftedCompleteSourceFunctionalMixedJet_re_neg_of_even_of_not_oddBad
oddBad_or_completeSourceFunctionalMixedJet_re_neg_of_even
```
that is,
[
ParityBad_odd
quadlorquad
Re(overline{Lambda_Lh_v},h_v^{(7)}(0))<0.
]

PR #211 is a representation/interface theorem. The independent incompatibility required by OBS-059I is not proved.

# What changed

PR #209 proved quantitative coercivity and strict anti-alignment using `explicitCanonicalSourceMoment`. PR #211 proves that this global source moment is exactly one complete explicit-formula functional of the same elementary source observable whose seventh jet appears locally.

The active interface is therefore the exact same-observable global/local pair
```text
Λ_Lh_v versus h_v^(7)(0).
```

This closes the representation prerequisite inside OBS-059I but does not close OBS-059I itself.

The successful proof also revealed that `half_matrixCoefficientPairing_quadraticNormal_scaled_eq_moment` carries the hypothesis `1 ≤ K` as an unused `_hK`. **DERIVED / CLEANUP OPPORTUNITY:** this helper is algebraic and can likely be generalized by removing that hypothesis. This is not the active mathematical frontier.

# Upstream implications

`DictionaryMixedPairing.lean` is a reusable mixed extension of the finite dictionary explicit-formula bridge. Future matrix observables that arise as independent left/right coefficient pairings can now be transported through the theorem-authoritative `literatureRHS` normalization without rederiving pole, prime and archimedean constants separately.

The complete Pair-D functional must remain assembled. PRs #199 and #201 remain warnings that componentwise source decomposition can lose exactly the dependency needed for the sign.

# Downstream implications

The next theoremization target is

```text
SOURCE_COORDINATE_KERNEL_FOR_COMPLETE_FUNCTIONAL
```

namely: derive, from the existing theorem-authoritative `literatureRHS`, dictionary normalization and the proved endpoint identities, the exact source-coordinate integral-plus-prime representation of (Lambda_Lh_v).

Do not prerecord guessed constants or signs. The exact formula must be compiler-derived.

Once that kernel is theorem-backed, the active OBS-059I question becomes concrete: can that exact complete arithmetic functional satisfy the strict anti-alignment and compulsory magnitude budget forced by #209 on a retained even-selected, odd-good negative state?

# Resurrected routes

**LEAD / HYPOTHESIS — complete-functional source analysis.** The old #199/#201 componentwise source-sign route remains consumed, but the complete cancellation-preserving functional is now theorem-backed and can be analyzed as one object.

**LEAD / HYPOTHESIS — zero-side/mixed dictionary transport.** The generic mixed dictionary theorem can potentially express other exact matrix pairings through the same explicit-formula normalization. Any use must preserve the exact retained state and normalization.

**LEAD / HYPOTHESIS — Riesz/global-local composition.** #209 makes the seventh jet nonzero on the odd-good branch; #211 now identifies the global source factor with a complete functional of the same h_v. This makes kernel/repeated-integration questions better posed, but no endpoint-scalar sign or high-order Riesz limit theorem is proved.

# New RH-relevant clues

**LEAD / HYPOTHESIS — kernel/Peano formulation.** After the source-coordinate kernel is exposed, (Lambda_Lh_v) will be a continuous-plus-arithmetic-sampling functional of a physical lift of h_v, while #163 identifies the local seventh jet. A useful independent theorem could arise from a Peano-kernel, reproducing-kernel, extremal, Gram, or repeated-integration representation that controls the angle or magnitude between these two functionals on the canonical source-atom class.

**LEAD / HYPOTHESIS — magnitude incompatibility.** The #209 inequality yields a compulsory global/local budget. An independent upper bound for (|Lambda_Lh_v|,|h_v^{(7)}(0)|) below that budget would exclude the odd-good branch without an opposite-sign theorem.

# Falsification checks

- Do not infer an opposite sign merely from rewriting #209 through #211.
- Do not split pole/archimedean/prime terms and bound them independently unless cancellation preservation is proved harmless.
- Do not differentiate through the physical clamp without proving the required regularity or using the correct one-sided/interior formulation.
- (h_v(0)=h_v(1)=0) alone does not provide all lower-order jet vanishings needed for seven integrations by parts.
- Cheaply falsify any proposed universal sign or magnitude law on the exact canonical source-atom class before committing to a large formal proof.
- The simultaneous odd-bad branch remains OPEN.
- The odd-selected first-bad branch remains OPEN.
- Endpoint-scalar sign remains OPEN.
- Negative-root exclusion remains OPEN.
- **RH remains OPEN.**

# Highest-leverage next moves

1. Synchronize the living documentation/control state through #211.
2. Prove the exact `SOURCE_COORDINATE_KERNEL_FOR_COMPLETE_FUNCTIONAL` without guessing constants or signs.
3. Preregister and cheaply falsify SIGN, MAGNITUDE and RIESZ/kernel incompatibility candidates on the exact source-atom class.
4. Formalize only a candidate that introduces information genuinely independent of the #207/#209 odd-sector self-energy argument.
5. Keep the simultaneous odd-bad and odd-selected branches explicitly open.
6. Keep Pair B secondary unless the complete-functional route stalls.

# Standing questions

What becomes possible now that was not possible before?

The complete source moment is now theorem-identical to one explicit-formula functional of the same source atom whose seventh local jet is constrained by #209.

If this contains a clue toward RH, where does it propagate?

Upstream into the theorem-authoritative explicit-formula/dictionary machinery and downstream into the exact global/local anti-alignment and nondegenerate Riesz boundary.

What is the highest-information next test?

Derive the exact source-coordinate kernel of (Lambda_Lh_v), then attack whether that complete functional can satisfy the #209 anti-alignment or magnitude budget on the exact retained state.

The selected formal first break remains `E4A4-SCHUR-FB-05`. R003 remains `DISCOVERY`; confirmatory execution is not authorized. **RH remains OPEN.**
