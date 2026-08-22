# Permansson v0.1.6 formal-verification notes

Target: Theorem 3.1 (Joint-process well-posedness), measurable-space core.

`GeneralFramework.lean` owns the construction layer:

- typed construction of the induced joint kernel from `alpha`, `P`, and `U`;
- proof that the induced kernel is Markov when the components are Markov kernels;
- Ionescu--Tulcea construction of the infinite trajectory law;
- probability-measure instance for the path law;
- finite-history transition-pair identity;
- zeroth-prefix/initial-law identity;
- regular conditional transition identity on standard Borel state spaces.

`Theorem31.lean` owns the existence-and-uniqueness layer:

- finite-prefix uniqueness induction;
- projective-limit uniqueness of the full trajectory measure;
- existence-and-uniqueness specification for the path law;
- integrated machine-form statement of Theorem 3.1.

CI compiles `Zeta23/Permansson/Theorem31.lean`, which transitively checks the framework layer, and separately rejects `sorry` placeholders and custom `axiom` declarations under `Zeta23/Permansson`.

This branch remains a draft verification branch until that complete theorem surface has passed CI.
