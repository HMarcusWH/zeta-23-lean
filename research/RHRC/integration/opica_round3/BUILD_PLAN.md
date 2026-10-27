# Round 3 extension: atlas, newborn source consumer and finite evaluator

The user extended the existing PR297 scope on 2026-10-27. This plan adds the
three selected prerequisites for systematic deductions to D01–D04, the #296
precision fix and the existing falsification gates. The archived draft is
research input; the live statements and compiler evidence determine authority.

## Contracts before implementation

1. **Statement atlas and source crosswalk.** Cover every mandatory member of
   the original 76, follow-up 100 and Round 2 forty-root cohorts, retaining
   cohort membership when declarations coincide, and every current Round 3
   public root. Record actual exported Lean types and source hashes separately
   from reviewed semantic annotations. Distinguish theorem hypotheses,
   mathematical inputs and proof-only dependencies. Record source identity,
   aperture/cutoff quantifiers, parity, normalization, moment order, polarity,
   valid adapters, known falsifiers and missing adapters. Unreviewed entries
   remain visibly unreviewed; a shared dependency does not certify compatibility.
2. **D05 at the newborn state.** Reuse the proved corrected complete-source
   identities. Construct a negative witness from the actual D04 Schur branch,
   at the same aperture, cutoff and selected parity, and apply the identity to
   that witness. Cover regular and resonant branches, either selected parity,
   equal cutoff arrivals and the empty K=2 predecessor. Keep the parity map
   distinct from the cutoff inclusion. Retain the operator-output forcing term
   in shifted/kernel compatibility; do not claim that the source alone lies
   in the opposite operator range for an arbitrary negative witness.
3. **Targeted complete-source evaluator.** Compute rigorous finite enclosures
   for the actual canonical Hermitian source and physical pole-neutral parity
   restrictions. Account for pole, Archimedean diagonal and off-diagonal,
   finite prime-power contributions, remaining tails and all numerical errors.
   Bind the formulas to exact source definitions. Bound resources and report
   uncertainty explicitly. Numerical near-zero evidence cannot establish an
   exact kernel, resonance, tie or first bad cutoff.

## Implementation order and ownership

The additional public declaration is
`Zeta23.OPICARound3.first_simultaneous_newborn_source_witnesses`, implemented
by `SchurNegativeWitness` and `NewbornSource`, with an independently stated
consumer in `Validation.NewbornSource`. It preserves D04's least `Ke, Ko` and
returns a constructed native source-witness packet at each parity's own least
cutoff. At `max Ke Ko`, it supplies the selected later parity's packet; equal
arrivals supply both. No claim makes the earlier parity newborn again.

The statement exporter is `Zeta23.RHRC.OpicaRound3AtlasExport`, an audit-only
reader of the compiled environment. `constraint_atlas.py` captures the native
export into external evidence, checks it against the committed JSONL product,
or explicitly writes that one product during local generation. The authored
semantic overlay and schema remain distinct from the generated records. The
mandatory cohort has 221 memberships (76+100+40+five Round 3 roots), with
duplicate declarations retaining all memberships. All 185 historical contacts
are retained as a backlog, including the eighteen triple contacts; their
presence does not claim that all have undergone semantic review.

Review the three exact contracts and existing reusable implementations first.
Implement the independent atlas and arithmetic tracks in parallel with the
formal track. Only one worker may write native Lean build objects. Integrate
the public declarations and exact source allowlist after their identities are
settled. Finalize source pins before refreshing canonical generated products.
Never edit synced project references, frozen ancestor mathematics, toolchain
pins or the original production 76/100/40-root acceptance predicates.

The atlas will separate authored semantic review from deterministic compiler
facts. Generated facts may hash upstream definitions but must not hash a
descriptor that hashes those same facts. Current CI receipts bind the complete
checkout after source finalization. The original 81 canonical products retain
their frozen producer scope; any new atlas products have their own explicit
producer and check-before-rewrite contract.

## Acceptance and adversarial review

The finite numerical contract is point-only: `K` is 2 or 3, the certified
prime cutoff is at most 64, and requested precision and per-case time are
bounded. The three mandatory actual-source cases are `K=2,L=1/2`,
`K=3,L=3/2` (including the prime power 4), and `K=3,L=log 2` at the exact
registered seam. K=2 reports empty neutral carriers. K=3 has a one-dimensional
native neutral space in each parity, so the certified scalar Rayleigh value
covers that entire space. No larger-cutoff, interval-aperture or exhaustive
source-arithmetic campaign is implied.

`source_backend.py` evaluates the direct equation-(4.4) source, including the
closed Archimedean correction. The producer integrates on a fixed unit
interval. `source_checker.py` independently recomputes the same source on
`[0,L]` at higher precision and checks the reported outward bounds. The
prime-power control must certify the strict contribution of 4 to the `(0,0)`
matrix entry, rather than merely return an unresolved status. Regular,
resonant and tie countermodels are exact rational controls and remain
separate from the actual-source cases. The arithmetic trust base includes
the pinned Arb/FLINT backend and reviewed analytic formulas; these are not
Lean certificates.

- Compile D05 and an independent consumer with exact expected types; check
  transitive axioms and reject a stronger, unsupported source-only conclusion.
- Check atlas cohort completeness, exact type/source identity, distinction of
  hypotheses from proof dependencies and incompatible/missing source adapters.
  Mutated source, omitted members and invented compatibility must fail closed.
- Run actual interval arithmetic on bounded source cases in both Python modes,
  including prime-free and nonempty prime-power sources, both parities and
  boundary/seam uncertainty. Verify enclosures independently and test omitted
  arithmetic/tails, incorrect normalization and forged source identity.
- Preserve the existing current runtime, formal and canonical checks. Extend
  the current acceptance job to require and independently reparse all added
  evidence from the same workflow run and exact commit/tree. A successful
  producer summary alone is insufficient.
- Review the complete change set, refresh genuine canonical products once
  sources are frozen, and push the coherent extension to PR297. Long-running
  checks on the previous head do not block that push. Afterwards, save credits
  and handle actual review or CI failures while the remaining checks run.

## Claim boundary

D05 is a same-state source identity and obstruction transport theorem. Finite
enclosures are finite computational evidence, with their numerical trust base
stated. Neither establishes a terminal source sign restriction or an eventual
bound. R3-XD, causal approximation, complete signed observation, original
detector upper bounds, the independent retained-pair radius bound, Step4 and
RH remain OPEN. Finite success never promotes an asymptotic or RH claim.
