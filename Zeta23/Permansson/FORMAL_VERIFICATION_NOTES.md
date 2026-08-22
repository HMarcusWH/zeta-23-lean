# Permansson v0.1.6 formal-verification notes

Target: Theorem 3.1 (Joint-process well-posedness), measurable-space core.

The standalone Lean file `GeneralFramework.lean` contains:

- typed construction of the induced joint kernel from `alpha`, `P`, and `U`;
- proof that the induced kernel is Markov when the components are Markov kernels;
- Ionescu-Tulcea construction of the infinite trajectory law;
- probability-measure instance for the path law;
- finite-history transition-pair identity;
- zeroth-prefix/initial-law identity;
- regular conditional transition identity on standard Borel state spaces;
- finite-prefix uniqueness induction;
- projective-limit uniqueness of the full trajectory measure;
- existence-and-uniqueness specification for the path law;
- an integrated machine-form statement of Theorem 3.1.

CI compiles `Zeta23/Permansson/GeneralFramework.lean` directly and separately rejects `sorry` placeholders and custom `axiom` declarations under `Zeta23/Permansson`.

This branch remains a draft verification branch until the integrated existence-and-uniqueness file has passed CI.
