# Countermodel and regression-fixture registry

Countermodels are typed by what they refute.

A synthetic configuration may refute a solver claim such as "this observable family always separates the classes" without being a realizable zeta zero configuration. Mathematical realizability must be proved separately before a synthetic construction is used against a theorem about zeta.

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
- **centered-grid structural fixture:** use the actual radius-N boundary-flat parity spaces / centered index map / cubic-KKT geometry with a generic reversal-symmetric diagonal operator to test whether a proposed contradiction uses more than generic structure;
- **displacement-preserving diagonal fixture:** add a reversal-symmetric diagonal term commuting with the centered index operator, preserving the displacement commutator while changing absolute spectral sign;
- **modified-prime-weight sensitivity fixture:** perturb canonical-style prime weights while retaining the same finite source architecture to test whether a proposed proof really uses the exact arithmetic coefficients;
- **atomwise determinant sign fixture:** test the first nonzero two-vector determinant coefficient of an elementary source atom before attempting positive atom-by-atom Gram/SOS arguments;
- **regular Schur conditioning fixture:** compare the final minimizing-trial Schur endpoint with the absolute magnitudes of its pole/arch/scalar/prime channel contributions;
- **post-#142 analytic regularization fixture:** an analytic centered diagonal family with an explicit `-log L` scalar term, predecessors positive throughout `L>0`, persistent finite negative witnesses at every aperture, a globally minimal bad size, and common negative behavior in both parities. This refutes generic contradictions from persistence + minimality + regularity + parity + scalar logarithms without saying anything against the actual canonical zeta source;
- **post-#146 translation-not-holomorphy fixture:** `F(z)=-z+Re z` satisfies an affine `2*pi*i` deck-shift law while remaining nonholomorphic. This refutes the inference that translation/deck structure alone establishes complex analyticity.

The post-#128/#129 structural fixtures are documented in `POST_129_STRUCTURAL_COUNTERMODELS_2026_09_08.md`.

The post-#138 Astra discovery/falsification findings are documented in `POST_138_ASTRA_DIAGNOSTICS_2026_09_09.md`. Those findings include DERIVED external symbolic identities and EXPERIMENTAL SIGNAL numerical sensitivity checks; they are not Lean theorem authority or canonical RH counterexamples.

The post-#142 analytic regularization negative control is documented in `POST_142_REGULARIZATION_COUNTERMODEL_2026_09_10.md`. Its role is to enforce

```text
aperture freedom
+ fixed-cell witness persistence
+ cell/global minimal bad size
+ predecessor regularity/positivity
+ parity
+ explicit scalar logarithm
!= arithmetic contradiction.
```

The post-#146 translation/holomorphy negative control is documented in `POST_146_TRANSLATION_NOT_HOLOMORPHY_COUNTERMODEL_2026_09_11.md`. Its role is to enforce

```text
periodic remainder
+ affine deck shift
!= complex differentiability
!= holomorphy.
```

The actual canonical pole/archimedean/von-Mangoldt channels must supply any decisive exclusion theorem, and the actual complex source integrals must supply genuine analytic regularity by theorem rather than by functional-identity analogy.

A regression fixture may protect a semantic firewall even when it is not itself a zeta counterexample.

**Claim firewall:** a generic, synthetic, modified-source or externally computed countermodel does not refute a theorem about the actual canonical CCM source matrix unless realizability or exact source equivalence is separately proved. RH remains OPEN.
