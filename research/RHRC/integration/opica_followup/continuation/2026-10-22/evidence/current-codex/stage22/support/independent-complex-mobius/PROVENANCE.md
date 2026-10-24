# Independent full complex Mobius consumer

Initial intended mathematical type was written in `INITIAL_INTENDED_TYPE.lean.txt`
before its first elaboration and before inspection of the production
`weighted_mobius_inverse` statement or proof. Its SHA256 is
`65A1985B68C25A03A33739D0509597E24EB31F45BE9D4A78C305E1A38A74986E`.
Seal time recorded by the local clock: `2026-10-24T20:53:18.2484332+02:00`.

Before this point I inspected only the frozen `PUBLIC_ROOTS.json`, `BUILD_SPEC.md`,
`PAPER_CROSSWALK.json`, and the definitions/helper APIs from `WeightedMixing.lean`
needed to express this contract. A declaration-name-only listing of that module
was used to identify the forbidden production block (lines 1400-1483), which was
not opened before the initial type seal. No Validation source, earlier expected
consumer, source-signature override, or copied production statement informed
the initial type.

The independent predicate retains arbitrary genuine complex input, the actual
physical mixture, both real and imaginary coordinate identities in both
directions, all four weighted coordinates, absolute-convolution finiteness with
explicit double integrals, the physical Mobius Jordan pair, and the exact norm.
It is a separate packaging of the frozen mathematical contract, not an assertion
that a copied declaration hash establishes independent authorship.

The owner repository is read-only for this work. Outputs live outside it.

## Elaboration and adaptation record

The initial predicate and theorem type compiled on their first elaboration,
without any change to the sealed mathematical type. The successful initial
source and object are preserved as `IndependentComplexMobius.InitialCore.lean`
and `IndependentComplexMobius.InitialCore.olean`; the compiler log is
`compile-initial.log`. The source prefix containing the entire predicate is
byte-identical to the sealed initial text. Its proof consumes the genuine
`weighted_mobius_inverse` theorem, retaining both imaginary equations. It derives
finite absolute convolution norms and the explicit finite double integrals from
the actual four output-coordinate norms and positive-convolution norm law.

After this initial seal, production inspection identified additional auxiliary
API clauses: each raw positive mixture-coordinate transform, the physical
Mobius/integer lattice unit identity, universal convolution norm multiplicativity,
the integer-comb sum/zeta norm, and the Mobius absolute-coefficient sum/quotient.
These were explicitly added as `postSealMobiusAuxiliaryInterface` and the theorem
`expected_independent_complex_mobius_full_interface`. They are supplementary
postseal interface coverage, not part of the preinspection authorship claim.
The combined source compiled successfully in `compile-full-interface.log`.

Both successful theorem declarations print precisely the standard axiom set
`[propext, Classical.choice, Quot.sound]`; neither has `sorryAx` or a project axiom.

Three deliberately invalid controls each exited 1:

* `ControlMissingImaginary.lean` preserves every root conjunct except replacing
  its imaginary forward/inverse proof fields by `True`. Lean rejects both exact
  imaginary equations of the independently sealed intended core.
* `ControlMissingPhysicalInterface.lean` replaces only the raw physical
  coordinate-interface field by `True`. The core continues to print its standard
  axioms, while the postseal full-interface theorem fails on the missing actual
  `positiveDilationMixture` transform equations.
* `ControlWrongExactNorm.lean` changes the exact norm denominator from
  `zeta(2*a+1)` to `zeta(2*a+2)`. Lean rejects the exact real norm equation and the
  auxiliary complex series/quotient equation.

Negative compiler logs can display `sorryAx` after reporting type errors: these
are Lean's failed-elaboration recovery terms, never accepted artifacts or passing
axiom gates. No negative-control object exists. No failed initial elaboration or
mathematical-type adaptation was suppressed.

## Installation suggestion

The successful standalone `IndependentComplexMobius.lean` is installable without
changing theorem names: it imports only `Zeta23.OPICAFollowup.WeightedMixing` and
uses namespace `Zeta23.OPICAFollowup.Validation`. Its primary new intended-type
consumer is `Zeta23.OPICAFollowup.Validation.expected_independent_complete_complex_mobius`.
The auxiliary declaration is
`Zeta23.OPICAFollowup.Validation.expected_independent_complex_mobius_full_interface`.
Install this file as a fresh Validation leaf and import it from the validation
aggregator, or splice its declarations into the existing validation module after
checking for name collisions. This work did not modify the owner tree, cache,
root inventory, registry, signatures, or claim classifications.
