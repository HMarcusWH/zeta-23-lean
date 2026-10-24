# Independent audit: raw sample sign and the Stieltjes product
24 October 2026 (Europe/Stockholm)

Base source: PR #294 head `cea7b2f62ea847c18958cc7385151c8c2b09520d`, tree `377c7f6f36375a4ac35d3f3ad17ee95b340eb9eb`.
Candidate inspected: `work/opica-stage19/SampleSign.lean`, SHA-256 `ba54d44074fc25f636a17fe0bad21fe9e63f6b581f93f89e4f80046009db2c1b`.
This report reviews mathematics and provenance. It does not itself provide a Lean compiler receipt for the candidate.

## Verdict

The candidate statement is mathematically correct, its stated domain includes the necessary nonreal-κ hypothesis, and no circular premise was found. It is **an existing PAPER-level corollary newly being formalized**, not a new mathematical discovery or an independent restriction excluding off-line zeros.

The exact frozen audited paper already states the raw sign in Part III.2, line 416:
“It also gives Im bκ/v > 0.”
The following sentence explicitly warns that independent native information is still needed before one could exclude the parameter. The corresponding copies are:

- `research/RHRC/integration/opica_followup/paper/OPICA_Followup_Final_Audited_Paper_2026-10-21.md:416`;
- `research/RHRC/integration/opica_followup/continuation/2026-10-22/inputs/OPICA_Followup_Final_Audited_Paper_2026-10-21.md:416`.

A targeted search of the current OPICAFollowup Lean sources and consumers found the explicit sign for **M=b/κ**, but no preexisting named raw-b sign theorem. The scratch result therefore appears useful as a small explicit formal corollary. The search is not a compiler-environment proof that no differently named equivalent lemma exists anywhere.

## Algebra and domain audit

Use **b = profileSampleDefect ρ = Σ hρ(n) − 1/2**. This is distinct from the paper's normalization constant `normalizationBrho ρ=(1−2ρ)/κ`; overloading these two b symbols would be a substantive error.

The existing actual diagonal Gram identity is

```text
Q = κ (N + conjugate(b)),
N = integral_0^infinity |h|² > 0,
Q = logForm(h') >= N/4 > 0.
```

For κ≠0, conjugation and division give b=Q/conjugate(κ)−N. Hence, with y=Im κ,

```text
|κ|² Im b = Q y.
```

For y≠0 this yields Im b/y=Q/|κ|²>0 and Im b≠0. The undivided identity remains the correct version at y=0; the strict divided version does not.

The candidate proves Q>0 from the already established log-unitary form identity and positivity of N. It does not assume sample reality, the desired sign, an RH-equivalent upper estimate, or a homogeneous eigenvalue equation. It retains the actual zeta-zero and strip premises. Its helper identifying the diagonal form Gram with logForm uses the actual derivative a.e. equality. No mathematical sign/conjugation flaw was found in that reduction.

In terms of ρ=β+iγ, Im κ=(1−2β)γ. Thus a hypothetical right-strip zero with β>1/2 and γ>0 must have Im b<0. This is a source-consistency consequence, not a contradiction.

The accompanying `real_sample_implies_on_line` lemma is also correct: for an actual strip zero with Im ρ≠0, an explicit hypothesis Im b=0 forces Re ρ=1/2 by contraposition. Its reality premise remains unproved. The compiler log `sample-sign-attempt3.log` reports `[propext, Classical.choice, Quot.sound]` for all three scratch declarations; this auditor did not launch that compiler process or independently confirm its exit status, so the process owner must supply the exact receipt before promotion.

## Why κM is Herglotz: classical mechanism

The actual spectral source has positive measure dω and a(ξ)=ξ²+1/4≥1/4. Existing sources prove only the finite weighted moment ∫a⁻¹dω<∞; **finite unweighted mass is not available**. Define

```text
M(z) = ∫ (a−z)^−1 dω,
B(z) = z M(z).
```

For Im z=y≠0, pointwise algebra gives

```text
Im[z/(a−z)] / y = a/|a−z|².
```

The integral is finite: a/|a−z|² <= (1+|z|/|y|)²/a. It is strictly positive because a≥1/4 and ω≠0. Therefore

```text
Im B(z)/Im z = ∫ a/|a−z|² dω > 0
```

for **every** nonreal z, without a zeta-zero premise. B is holomorphic on the cut complement and maps the upper half-plane strictly to itself.

Do not justify this by splitting z/(a−z)=a/(a−z)−1 into two integrals: those separate integrals can both diverge when ω has infinite mass. Keep the combined convergent kernel.

The source-specific formal consequence follows from b=B(κ) and the established spectral form formula Q=|κ|²∫a/|a−κ|²dω. Thus the diagonal Gram proof and Stieltjes proof give the same identity, through already compatible source representations.

A further **DERIVED** formulation is the Pick kernel

```text
[B(z)−conjugate(B(w))]/[z−conjugate(w)]
    = ∫ a / [(a−z)(a−conjugate(w))] dω.
```

For finitely many upper-half-plane points it is positive semidefinite. At actual zero parameters this is the existing form Gram Q after diagonal κ scaling. It repackages Q-positivity; it does not add an independent positivity law. Degenerate denominators require the undivided or derivative version.

This mechanism is classical Stieltjes theory. [Grabovsky, SIAM J. Appl. Math. 82 (2022), 1135–1166](https://epubs.siam.org/doi/10.1137/21M1392279), [author preprint, Theorems 2.2–2.3](https://arxiv.org/pdf/2101.02775), gives the characterization by both M and zM being Nevanlinna functions. [Eckhardt–Kostenko, *Trace formulas and inverse spectral theory for generalized indefinite strings*, §11](https://link.springer.com/article/10.1007/s00222-024-01287-9), states the same classical characterization and attributes its string-theoretic origin to Krein. The new formal contribution is its exact application to the genuine arithmetic sample, with all actual source/domain identifications.

## Adversarial checks and overinterpretations

1. **Exact nonreal model satisfying all scalar sign/form identities.** Take positive spectral measure δ₁, z=1+i, M(z)=i, B(z)=−1+i, N=2, Q=2. Then Q=z(N+conjugate(B)), Q≥N/4>0 and Im B/Im z=Q/|z|²=1. A one-dimensional self-adjoint operator A=1 with h=−1+i and force g=1 satisfies Ah=z(h+g). Nonreal z is fully compatible with the forcing and both positive forms.
2. **Conjugation control.** Replacing Q/conjugate(z)−N by Q/z−N in that example changes b to −1−i and gives the wrong sign.
3. **Boundary control.** For real κ the divided strict statement fails; the candidate correctly excludes it.
4. **Support control.** If the measure is δ₀, zM(z)=−1 is real; strictness fails. If it is δ₋₁ and z=i, Im[zM(z)]/Im z=−1/2. Positivity of the spectral location, not positivity of the measure alone, is needed.
5. **Zero-measure control.** ω=0 loses strictness. The actual nonzero source is justified by its positive weighted moment.
6. **No uniform bound.** Strict positivity supplies no parameter-uniform lower bound or growing-family conditioning constant.
7. **No sample-reality shortcut.** A universal real-sample assertion at actual off-line candidates would be an independent exclusion assertion requiring its own proof. It cannot be inferred from positivity; the resolvent gives the opposite nonzero imaginary part there.
8. **No new original root.** This optional helper should not be counted as completing another frozen primary root or added to the mandatory 100-root ledger.

The seven exact symbolic/algebraic controls in `sample-sign-exact-controls.json` passed. They include the generic kernel identity and the countermodels above. This is executable falsification evidence, not a Lean proof or an interval estimate for zeta.

## Recommended disposition

If the compiler/axiom/independent-consumer gates pass, record **PROVED (narrow): explicit raw arithmetic sample sign, formalizing the already stated F2 consequence**. Classify novelty as **classical mechanism / source-specific formal corollary**. It is a useful normalization and anti-shortcut theorem; it is not new independent information about which spectral parameters can correspond to zeta zeros.

The highest-information next question remains whether the same actual source or boundary functional satisfies an independently established incompatible bound. The raw sign alone is automatically satisfied across the entire nonreal resolvent domain.

RH OPEN. Step 4 OPEN.

