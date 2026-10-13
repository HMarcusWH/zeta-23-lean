# WP2/WP4 production Eq.(4.4) Python ↔ Lean normalization crosswalk

**Scope:** fixed positive aperture \`L\`, finite centered carrier \`K\`, and fixed cutoff cell \`log Q < L < log(Q+1)\`.  
**Reference authority:** merged Mathlib/Lean repository, not the legacy printed \`finiteMatrix\`.  
**Purpose:** an inspectable *term map*, not a claimed machine proof of Python ↔ Lean semantics.  
**Claim firewall:** RH_OPEN, numerical agreement is never a universal theorem.

| Logical term | Lean reference (source on merged #288) | Python production Arb reference | Critical convention |
|---|---|---|---|
| Indexed source matrix | \`Zeta23/CCM/SourceNormalizationRepair.lean:150\`, \`canonicalSourceMatrix\` | \`canonical_source_arb.py:204\`, \`canonical_source_matrix\` | Finite centered indices \`-K..K\`; **do not** use \`finiteMatrix\` |
| Source Eq.(4.4) identification | \`SourceNormalizationRepair.lean:155\`, \`canonicalSourceMatrix_eq_sourceEq44Matrix\`; \`SourceWeilMatrixReconciliation.lean:219\` | \`canonical_source_matrix\` and independent \`fixed_unit_fixed_q_canonical_source_matrix_arb\` | Exact cutoff-free convention; legacy diagonal shift not present |
| Channel signs | \`CanonicalSourceChannels.lean:58\`, \`canonicalSourceMatrix_eq_pole_sub_arch_sub_prime\` | \`canonical_source_matrix\` assembles \`pole_component - direct_arch_component - prime_component\` | **Pole − arch − prime**; no missing or duplicated correction |
| Pole | \`Components.lean:55\`, \`poleComponent\`; \`CanonicalSourceChannels.lean:23\`, \`canonicalPoleMatrix\` | \`canonical_source_arb.py:157\`, \`pole_component\` | Numerator \`32 L sinh²(L/4)(L²−16π²nm)\` and both denominators |
| Off-diagonal arch primitive | \`Components.lean:33\`, \`alphaL\`; \`SourceWeilMatrixReconciliation.lean:156\`, \`sourceEq44ArchComponent\` | \`canonical_source_arb.py:134\`, \`alpha_L\` and \`:191\`, \`direct_arch_component\` | \`(alpha(m)−alpha(n))/(n−m)\` |
| Diagonal beta | \`Components.lean:41\`, \`betaL\` | \`canonical_source_arb.py:138\`, \`beta_L\` | Exactly \`2gamma−2beta\` |
| Diagonal gamma (source) | \`SourceWeilMatrixReconciliation.lean:105\`, \`sourceEq44GammaL\`; \`:156\`, \`sourceEq44ArchComponent\` | \`canonical_source_arb.py:142\`, \`source_eq44_gamma_L\` | Direct eq.(4.11) LHS + **one** \`wCorrection\`, not the legacy \`cCorrection\` |
| Scalar wCorrection | \`Components.lean:28\`, \`wCorrection\` | \`canonical_source_arb.py:151\`, \`w_correction\` | \`(EulerGamma+log(4π)−log(coth(L/2)))/2\`, counted ONCE in gamma |
| Prime atom basis | \`Kernel.lean:11\`, \`qBasis\` | \`canonical_source_arb.py:164\`, \`q_basis\` | Frequency argument \`y=log q\`; polynomial/trig denominator sign matches |
| Prime powers | \`Components.lean:69\`, \`primeComponent\`; \`CanonicalSourceChannels.lean:35\`, \`canonicalPrimeMatrix\` | \`canonical_source_arb.py:171\`, \`von_mangoldt\`, \`:181\`, \`prime_component\` | \`Λ(p^j)=log p\`; coefficient \`Λ(q)/sqrt(q)\`; cutoff \`q≤Q\` on fixed cell |
| Physical quadratic form | \`CanonicalRegularizedEnergyIdentity.lean:188\`, \`quadraticForm_canonicalSourceMatrix_eq_regularizedEnergy\` | \`Zeta23/CCM/../canonical_source_arb.py\` matrix and exact real carrier Rayleigh quotient | Fixed-vector result, not arbitrary moving-vector F04 interchange |
| Real/Hermitian | \`ConstrainedCanonicalSector.lean:212\`, \`canonicalSourceMatrix_isHermitian\` and \`CanonicalConjugationGeometry.lean:473\` | \`arb_mat\` symmetric source matrix and exact real carrier basis | \`Δ=ad−b²\`; no division by a; nonunitary parity index map |
| Python fixed-unit normalization | \`CanonicalApertureAnalyticPrimitives.lean\` and \`CanonicalApertureContinuity.lean\`, regularized source primitives | \`post175_fb05_q13_fixed_unit_enclosure.py:101\`; \`post177...derivative.py\`, \`post194...second_derivative.py:213\` | Change variable \`t=x/L\`, integrals over \`[0,1]\`, no new diagonal adjustment |
| Fourth-order extension | Same exact \`canonicalSourceMatrix\`; high derivatives are paper/Arb program, **not yet Lean claims** | \`post287/wp4_k3_fourth_order_fallback.py\` and \`wp4_fourth_order_validate.py\` | Must match all 49 entries through order two before order-four certificate could be accepted |

## Acceptance procedure

1. Do an exact read of the original Lean definitions and \`#print axioms\` at the final head.
2. Independently reconstruct the full source via \`canonical_source_arb.py\` and its separate fixed-unit implementation at K2/K3 and actual prime cells. \`post287/wp2_wp4_normalization_gate.py\` compares all entries with Arb enclosures, including the complete 7×7 matrix.
3. Check exact parity basis: \`M0=M1=M2=0\` and reversal symmetry, dimension two in both K3 parity carriers. Do not apply the nonunitary map \`D\` as if norm-preserving.
4. Preserve the **historical unsound determinant-curvature bug as a falsifier**: full-interval \`Δ''\` must use interval \`a,b,d,a',b',d'\` as well as \`a'',b'',d''\`, never replace them by centre values. Both the frozen and full K3 scripts were corrected and are now statically checked for this.
5. At cutoff seams, each certified rational tile encloses an analytic fixed-Q extension. Only its intersection with the physical cutoff cell supplies authority. For true prime atoms, the new entering term vanishes at its seam, preserving continuous gluing.
6. No Python result is promoted to Lean PROVED without a separately checked proof/interface. A successful Arb transcript remains INTERVAL_EVIDENCE; the full K3 claim remains OPEN until both parities and all interval layers pass their numerical and mathematical gates.

This is an audited *mapping of definitions and conventions*. There is no independently compiled theorem here equating Python execution to Lean semantics, nor does a successful finite aperture certificate close RH.

## Rev4 section 14.4 direct functional probe

`wp2_literature_form_arb_probe.py` independently constructs the real
autocorrelation of the two prescribed rational coefficient vectors at
`L=8/5`, `K=2`. It evaluates the literature pole and prime scalars directly,
with independent weights `log 2`, `log 3`, `log 2` at prime powers `2,3,4`.
For the arch scalar it uses the exact digamma integral transformed to
physical space. Since the autocorrelation vanishes beyond L, that tail is
integrated in closed form as `-H(0)*log(1-exp(-2L))`; the remaining finite
integral is evaluated by Arb with the origin singularity removed by sinc
and exponential slopes. No heuristic Fourier cutoff or tail estimate is
used. The matrix backend is used only to compare the resulting scalar.

The transform follows the repository's `ExplicitFormula.lean` definitions
of `literatureRHS` and `gammaBracket` and its physical arch representation;
its interpretation relative to the external papers remains DERIVED.
The normalization gate requires the direct-minus-matrix enclosure to
contain zero and be narrower than `2^(-precision_bits/2)`, and requires
the ratio to contain one. Factor-two and duplicate-arch-correction controls
must be rejected. A finite PASS neither establishes the external hard-window
domain transfer nor validates Zhu/Liu/Groskin coercivity certificates.
