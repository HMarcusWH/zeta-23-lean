# Countermodel and regression-fixture registry

<!-- RHRC_CURRENT_STATE_BEGIN -->
## Current RHRC state

THEOREM AUTHORITY
- merged theorem authority = PR #222
- validated final head = c46939488ead9535a63b547c38d64938a882a9f1
- merge commit = 001f375b4a7e70f69d2b7abb3bed1b9fd04f0ba5
- tree = fd151afbcae3155cc4d32a75da08b6f7e0119099

MERGED THEOREM-STAGE PROVENANCE
- PR #222
- validated theorem head = e42dbce1bbbc68b5cf9612e7c8a8dab2a2eca543
- validated theorem tree = 48d8752950c28e0d3bbd385646e71075abef9e76
- status = MERGED_VIA_PR_222
- theorem family = BIREGULAR_FIRST_BAD_ZERO_SHIFT_NORMAL_FORM

LATEST RESEARCH EVIDENCE
- PR #223
- validated head = 5e01e55544be937b0f0e389f1f279e13a89f2b3a
- merge commit = 8c57ce445a2223dab4a3e8aedbd3db67171e96b0
- tree = 3588cd964a3346b20e359b41c02eb8caaed3221a
- disposition = NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED
- qualified retained points = 0
- retained-state implication = FROZEN_SCOPE_DID_NOT_REACH_RETAINED_STATE

CONTROL AUTHORITY
- PR #117
- selected formal first break = E4A4-SCHUR-FB-05
- active subobligation = OBS-059I
- next research target = RETAINED_BIREGULAR_ZERO_SHIFT_SCALAR_DISCRIMINATION
- R003 phase = DISCOVERY
- confirmatory execution = NOT AUTHORIZED
- terminal claim = RH_OPEN
<!-- RHRC_CURRENT_STATE_END -->

## Current falsification target

Countermodels should now attack proposed **retained-root secular-completion mechanisms** without replacing the retained first-bad/eigenvector hypotheses by arbitrary-vector full-carrier claims. PR #215 has already consumed universal full-carrier source/M4 sign and proportionality in its tested scope.

Countermodels are typed by what they refute.

A synthetic configuration may refute a solver/research claim without being a realizable zeta-zero configuration. Mathematical realizability must be proved separately before a synthetic construction is used against a theorem about zeta.

Reusable countermodel/regression classes include:

- same TightMult-visible data, different hidden label;
- adversarial cancellation across probes;
- matched window/marginal artifacts;
- conditional-input removal;
- finite/truncated agreement with divergent infinite behavior;
- **scalar-shift normalization fixture:** compare `A` with `A+cI`; commutators/eigenvectors/gaps agree while absolute eigenvalues, PSD and inertia can change;
- **carrier-space fixture:** identical pointwise formula on an interval but different zero-extension / ambient-space semantics;
- **source-normalization fixture:** direct source formula and later rewritten display differ by a correction convention;
- **generic regular Schur fixture:** nonnegative predecessor block with a negative zero-shift Schur endpoint and pure-shell response;
- **generic resonance fixture:** zero predecessor block with nonzero shell coupling producing an exact kernel pole and negative spectrum;
- **centered-grid structural fixture:** actual radius-N boundary-flat parity spaces / centered index map / cubic-KKT geometry with a generic reversal-symmetric operator;
- **displacement-preserving diagonal fixture:** preserve the displacement commutator while changing absolute spectral sign;
- **modified-prime-weight sensitivity fixture:** perturb canonical-style prime weights while retaining the finite source architecture to test whether a proposed proof spends the exact arithmetic coefficients;
- **atomwise determinant sign fixture:** test elementary source atoms before attempting positive atom-by-atom Gram/SOS arguments;
- **regular Schur conditioning fixture:** compare final minimizing-trial Schur energy with absolute pole/arch/scalar/prime channel magnitudes;
- **post-#142 analytic regularization fixture:** persistence + minimality + regularity + parity + scalar logarithm can coexist with finite negative states in a generic analytic family;
- **post-#146 translation-not-holomorphy fixture:** `F(z)=-z+Re z` has an affine deck-shift law while remaining nonholomorphic;
- **post-#150 aperture-derivative fixture:** test whether the actual canonical matrix derivative has a uniform Loewner sign before using aperture monotonicity;
- **post-#150 minimizing-Schur derivative fixture:** test whether the exact regular selected-residual Schur value has a uniform derivative sign;
- **post-#150 elementary-atom energy fixture:** test the sign of the elementary source-atom energy on the exact selected-residual geometry;
- **post-#155 D-transport regression fixture:** historical implementation firewall; PR #157 now theoremizes the genuine complex production D-transport and zero-sum rank-two cancellation, so this fixture protects against future regressions rather than recording an open dependency;
- **post-#155 pointwise Riesz-sign fixture:** exact `K=2` even/odd boundary-flat vectors falsify the universal claim that positive Riesz primitives plus endpoint flatness force a pointwise fixed-sign smoothed source-energy integrand; the exact derivative witness is rerun by `check_post155_riesz_pointwise_sign.py` in the RHRC suite;
- **post-#157 boundary-term arithmetic fixture (planned):** once the generic one-step Riesz boundary recurrence exists, test any proposed scalar endpoint-factor sign/monotonicity across fixed cutoff cells and prime-power thresholds before theorem investment;
- **post-#150 selected-residual interval fixture:** reconstruct exact boundary-flat/parity/predecessor/shell geometry, scout the production canonical source numerically, then replay candidate sign failures with Arb enclosures before treating them as rigorous finite falsification evidence.

Historical fixture records:

- `POST_129_STRUCTURAL_COUNTERMODELS_2026_09_08.md`
- `POST_138_ASTRA_DIAGNOSTICS_2026_09_09.md`
- `POST_142_REGULARIZATION_COUNTERMODEL_2026_09_10.md`
- `POST_146_TRANSLATION_NOT_HOLOMORPHY_COUNTERMODEL_2026_09_11.md`
- `POST_150_ARITHMETIC_DIAGNOSTICS_2026_09_12.md`
- `POST_150_SELECTED_RESIDUAL_SCOPE_AUDIT_2026_09_12.md`
- `POST_155_RIESZ_POINTWISE_SIGN_COUNTERMODELS_2026_09_13.md`

Executable exact regression:

```text
python research/RHRC/countermodels/check_post155_riesz_pointwise_sign.py
```

The checker reconstructs the odd source derivatives from the production `sourceEntryReal` formula at `omega=0` and `omega=1/4` using exact rational arithmetic, and verifies the opposite-sign ninth/seventh derivative values for both `K=2` fixtures.

The post-#150 files record a mixture of DERIVED/external calculations, EXPERIMENTAL SIGNAL numerical route falsifications, and rigorously enclosed finite numerical audits. They remain historical records at their original evidence classes.

PR #153 theoremizes the exact finite pole-prime discrepancy identity and full production source-channel discrepancy normal form. PR #155 theoremizes finite discrepancy integrability, anchored Riesz primitives, legal generic repeated integration by parts / conditional Riesz smoothing, source-coordinate oddness, all even endpoint jets, and even-parity `M3=0`.

PR #157 theoremizes the genuine complex production D-transport, boundary-flat jets through order 6, even boundary-flat jets through order 8, exact complete production Riesz order 6 / even order 8, retained transformed negativity, and the ExceptionalZero Riesz-6 negative wrapper.

Therefore complex D-transport and unconditional production Riesz order 6 are no longer open. The stronger retained Riesz-8 result remains conditional on even first-bad parity.

The exact post-#155 `K=2` fixtures kill only the pointwise fixed-sign interpretation. They do not refute the Riesz identities or prove anything about RH.

The actual canonical pole/archimedean/von-Mangoldt channels must supply any decisive exclusion theorem. Historical transformed-residual falsifiers remain regression evidence; the current hostile target is a proposed **retained-root secular-completion mechanism** on the exact forced state.

A regression fixture may protect a semantic firewall even when it is not itself a zeta counterexample.

**Claim firewall:** a generic, synthetic, modified-source or externally computed countermodel does not refute a theorem about the actual canonical CCM source matrix unless realizability or exact source equivalence is separately proved. A rigorous finite Arb enclosure can falsify the finite scoped mechanism it actually checks, but does not become Lean theorem authority and does not by itself certify whole-cell retained ancestry. RH remains OPEN.

---

## Post-#205 executable C1 promotion

The historical post-#129 C1/C2/C3 document remains historical at its original evidence class. PR #205 later reconstructs **C1 specifically** as current repository-reproducible exact research; it does not recover the missing original 37-case oracle or retroactively upgrade the historical `185 / 74 / 140` counts.

Current executable Pair-D C1 certificate:

```text
PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED
fixture = C1
N = 2
K = 3
q_by_abs_index = (1,1,1,-10)
even predecessor form = 70 > 0
odd predecessor form = 10 > 0
even successor witness energy = -130
odd successor witness energy = -410
selected even compressed root = -13/42
reversal_symmetric = true
centered_index_commutator_zero = true
canonical_realizability = false
```

Run it with:

```text
python research/RHRC/countermodels/check_post204_pair_d_exact_geometry.py
python research/RHRC/countermodels/check_post204_pair_d_scope.py
python research/RHRC/countermodels/certify_post204_pair_d_structural_countermodel.py
```

Evidence class:

```text
EXACT EXECUTABLE RESEARCH
RIGOROUS FINITE SYNTHETIC COUNTERMODEL
```

Interpretation: generic predecessor positivity plus the actual radius-3 parity/boundary-flat/shell geometry, reversal symmetry, and centered-index displacement commutation do **not** exclude simultaneous even/odd successor badness. Any successful Pair-D exclusion must therefore use a property of the actual `canonicalSourceMatrix` not shared by C1.

This does not prove canonical realizability, does not refute a Lean theorem, and does not close FB-05, negative-root exclusion, or RH.