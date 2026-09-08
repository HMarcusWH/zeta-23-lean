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
- **displacement-preserving diagonal fixture:** add a reversal-symmetric diagonal term commuting with the centered index operator, preserving the displacement commutator while changing absolute spectral sign.

The post-#128/#129 structural fixtures are documented in `POST_129_STRUCTURAL_COUNTERMODELS_2026_09_08.md`.

A regression fixture may protect a semantic firewall even when it is not itself a zeta counterexample.

**Claim firewall:** a generic/synthetic countermodel does not refute a theorem about the actual canonical CCM source matrix unless realizability or exact source equivalence is separately proved. RH remains OPEN.
