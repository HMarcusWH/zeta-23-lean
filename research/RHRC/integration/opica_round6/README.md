# OPICA Round 6 — constraints on the signed Step 4 response

Step 4 and RH remain **OPEN**. The finite theorems, arithmetic experiments and paper reductions below concern the same proof search. They have different evidentiary force.

## Follow the arithmetic

1. [Constraint register](CONSTRAINTS.json) and [generated graph](CONSTRAINT_GRAPH.json). Each entry gives its source. Joint inputs must hold simultaneously, alternatives are separate routes, and context edges do not carry proofs. The 53 original CR records retain both their native disposition and their relevance to closure. The source-register rows are excluded from logical premises.
2. [Finite arithmetic modules](../../../../Zeta23/OPICARound6/PrimeFactorPaths) and [typed audit](../../../../Zeta23/OPICARound6/PrimeFactorPaths/Verify.lean). The 50 finite statements concern cost, support, cancellation and exact source identities. The compiler groups in the [workflow](../../../../.github/workflows/rhrc_opica_round6.yml) check ownership and transitive axioms, including the six earlier declaration anchors. An arithmetic upper for growing cutoffs requires a separate proof.
3. [Prime-factor path reduction](evidence/step4-one-sided-sieve-2026-11-19/PRIME_FACTOR_PATHS.md) and [small and large prime factors](evidence/step4-one-sided-sieve-2026-11-19/SMALL_PART_LARGE_PART.md). On paper, actual opposite-sign matching removes the specified small-cofactor and atypical prime-count paths, with bounded absolute error per whole shell in the weighted one-sided square energy. Spent partners must also be removed. The total cost over the whole shells is logarithmic.
4. [Cone determinant](CONE_CONTINGENCY.md), [finite measurements](CONE_PARITY_RESULTS.json) and [source arithmetic](cone_parity.py). The determinant and product of signed margins can both be large. Their difference recovers the charge on the original arithmetic vertices. The larger finite cutoff in the sensitivity test is labelled in the receipt.
5. [Research collections](DRIVE_RESEARCH_MAP.md), [file survey](DRIVE_SOURCE_SURVEY.json) and [evidence provenance](EVIDENCE_ORIGINS.json). Earlier failures include fixed-origin transfer, all-vector Hankel positivity, source-free stability and isolated prime-power estimates. The original quantitative assumptions stay with their individual carriers.

## The remaining estimate on this route

Fix one polarity. For every positive ε, fix its constant before choosing a lower horizon. Find arbitrarily late native cutoffs X for which the complete weighted sum of squared positive survivor charges on the coarse cells of all whole terminal shells is at most Cε X^ε. Pair selection, both signs, endpoints, cell weights and the original rough Möbius cutoff are specified in the path reduction. The graph lists the independent arithmetic estimate (`ACTUAL_UPPER`) and the kernel-checked transfer to the source criterion (`PAPER_ROUTE_VALIDATION`) as the two outstanding inputs on this route. Other routes have their own open hypotheses.

The cone calculation supplies an adversarial check. In its four-count table, (Nf=4D+ab). Bounding the positive determinant alone at subpower scale contradicts its paper lower bound on whole base cells. Replacing the full signed square by averaged-origin or projected energy also changes the observable.

## Parity excess and deficit on the same cells

The even population's excess and the odd population's shortfall have an exact finite relation to the signed square. For centered counts $e,o$, the error in replacing $[e-o]_+^2$ by $4[e]_+[-o]_+$ lies between zero and $(e+o)^2$. The coefficient four is forced. The Lean module also bounds the sum of the absolute errors with arbitrary nonnegative finite weights. The paper calculation estimates the total discrepancy for the genuine rough source and includes every deleted target and spent partner in the center. The registered Step 4 alternative requires an independent cofinal bound on the full opposed product (`P303_OPPOSED_PRODUCT_UPPER`) and the kernel-checked transfer (`PAPER_ROUTE_VALIDATION`). [Finite Lean theorems](../../../../Zeta23/OPICARound6/PrimeFactorPaths/ParityDeficitProduct.lean) · [Arithmetic reduction and sibling contrasts](evidence/step4-parity-deficit-2026-11-20/SURVIVOR_HAAR_FINGERPRINTS.md)

| Result | What it contributes to the estimate |
|---|---|
| [Divisor gap and signed halves](evidence/step4-parity-deficit-2026-11-20/DIVISOR_GAPS_AND_SIGNED_HALVES.md) | Each complete divisor half annihilates many signed moments. Puncturing the top endpoint recovers the original vertex sign. |
| [Cofactor pairs](evidence/step4-parity-deficit-2026-11-20/SURVIVOR_COFACTOR_PAIRS.md) and [single-fibre precision control](evidence/step4-parity-deficit-2026-11-20/SINGLE_COFACTOR_PARITY_DEFICIT.md) | The earlier aligned selector has relative cancellation and a bounded GCD correction on one fibre. Removing the fibre from that source can create almost full-power opposed energy while preserving the relative estimate. |
| [Unequal prime shares](evidence/step4-parity-deficit-2026-11-20/UNBALANCED_PRIME_SHARES.md) | Two genuine prime baskets before selection have matching continuum contributions. The comparison requires the same cofactor weight in both. |
| [Sharp fingerprint threshold](evidence/step4-parity-deficit-2026-11-20/SHARP_FINGERPRINT_THRESHOLD.md) | At a fixed $(\log X)^K$ cutoff with $K>2$, even conditioning the Euler weights on the observed fingerprints leaves discrepancy energy of exponent $1-2/K$ on the unselected source. The witnesses exceed the typical survivor factor count. |
| [Corrected survivor fingerprints](evidence/step4-parity-deficit-2026-11-20/MOMENT_CORRECTED_SURVIVOR_FINGERPRINTS.md) | A corrected center using the exact removed-row history pays the unsigned histogram error. The predicted signed charge and the large-cofactor parity residual still need a common bound. |

The three finite replays exercise [integer divisor halves](evidence/step4-parity-deficit-2026-11-20/DIVISOR_HALVES_EXACT.json), [ordered cofactor pairs](evidence/step4-parity-deficit-2026-11-20/SURVIVOR_COFACTOR_PAIRS_CHECK.json) and [reconstruction of a cell's fingerprint counts](evidence/step4-parity-deficit-2026-11-20/TRUNCATED_FINGERPRINTS_CHECK.json). Their receipts specify the tested vertices, horizons and negative controls. Each replay verifies its committed result by default. Supply `--output FILE` to export newly calculated bytes after they compare equal.

## Reproduce the graph and finite checks

Run from the repository root with the pinned Lean toolchain for the compiler steps.

```sh
pkg=research/RHRC/integration/opica_round6
python3 -B "$pkg/test_constraint_graph.py"
python3 -B "$pkg/constraint_graph.py" --check --check-rhkg
python3 -B "$pkg/constraint_graph.py" --explain SURVIVOR_ROUTE
python3 -B "$pkg/constraint_graph.py" --explain P303_OPPOSED_PRODUCT_ROUTE
for fixture in divisor_halves survivor_cofactor_pairs truncated_fingerprints; do
  python3 -B "$pkg/evidence/step4-parity-deficit-2026-11-20/check_${fixture}.py"
done
python3 -B -m research.RHRC.integration.opica_round6.cone_parity --check
python3 -B -m unittest research.RHRC.integration.opica_round6.test_source_scope
lake build Zeta23.OPICARound6.PrimeFactorPaths.Verify
lake env lean -DwarningAsError=true -j2 -s262144 Zeta23/OPICARound6/PrimeFactorPaths/Verify.lean
```

The full repository materializer and inherited OPICA acceptance jobs independently check the canonical research products. The Round 6 graph adds source and dependency queries. Its reachability and finite measurements each have a narrower meaning than a theorem on the true field.
