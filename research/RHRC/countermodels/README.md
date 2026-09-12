# Countermodel and regression-fixture registry

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
- **post-#150 discrepancy/Riesz fixture:** compare the raw pole/prime discrepancy integral with its high-order Riesz-smoothed form and the remaining arch/scalar budget;
- **post-#150 selected-residual interval fixture:** reconstruct exact boundary-flat/parity/predecessor/shell geometry, scout the production canonical source numerically, then replay candidate sign failures with Arb enclosures before treating them as rigorous finite falsification evidence.

Historical fixture records:

- `POST_129_STRUCTURAL_COUNTERMODELS_2026_09_08.md`
- `POST_138_ASTRA_DIAGNOSTICS_2026_09_09.md`
- `POST_142_REGULARIZATION_COUNTERMODEL_2026_09_10.md`
- `POST_146_TRANSLATION_NOT_HOLOMORPHY_COUNTERMODEL_2026_09_11.md`
- `POST_150_ARITHMETIC_DIAGNOSTICS_2026_09_12.md`
- `POST_150_SELECTED_RESIDUAL_SCOPE_AUDIT_2026_09_12.md`

The post-#150 files record a mixture of DERIVED/external calculations, EXPERIMENTAL SIGNAL numerical route falsifications, and rigorously enclosed finite numerical audits. None of these are Lean theorem authority unless separately formalized and compiler/CI validated.

The actual canonical pole/archimedean/von-Mangoldt channels must supply any decisive exclusion theorem. After #150, analytic regularity itself is theorem-backed; the current falsification target is the arithmetic sign of the exact selected residual.

A regression fixture may protect a semantic firewall even when it is not itself a zeta counterexample.

**Claim firewall:** a generic, synthetic, modified-source or externally computed countermodel does not refute a theorem about the actual canonical CCM source matrix unless realizability or exact source equivalence is separately proved. A rigorous finite Arb enclosure can falsify the finite scoped mechanism it actually checks, but does not become Lean theorem authority and does not by itself certify whole-cell #150 ancestry. RH remains OPEN.
