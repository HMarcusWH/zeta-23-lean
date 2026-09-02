# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**
>
> This repository contains theorem-backed research infrastructure and formally validated constraints relevant to the Riemann Hypothesis. Green supporting mathematics is progress, not a proof of RH.

## Current authority snapshot

~~~text
theorem-state anchor = PR #100 merge 4427e2a8c8d90dbb7d66d9d96f9a410cecb75df9
validated theorem head = 497adcd6a746d49fd23654cabf4ed8f0c58db8a9
theorem tree = 705ab8b88728a5b90d850eb4b51c01a66811f088
theorem-bearing merged through = PR #100
live GitHub main = authoritative
date = 2026-09-02
RH = OPEN
~~~

Exact PR #100 validation:

~~~text
final head = 497adcd6a746d49fd23654cabf4ed8f0c58db8a9
head tree = 705ab8b88728a5b90d850eb4b51c01a66811f088
merge/main = 4427e2a8c8d90dbb7d66d9d96f9a410cecb75df9
merge tree = 705ab8b88728a5b90d850eb4b51c01a66811f088
RHRC #691 = SUCCESS
Permansson #464 = SUCCESS
CCM build = SUCCESS
ExceptionalZero build = SUCCESS
forbidden-placeholder gate = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
~~~

The exact theorem tree tested at the final PR head is the tree now merged on main.

## Current RH-directed theorem ladder

~~~text
off-line zeta zero
  -> compact C² pole-neutral negative W test                       PROVED
  -> strict aperture collar + legal finite approximation          PROVED
  -> strict finite negative W value                               PROVED
  -> finite canonical negative quadratic direction                PROVED / F1
  -> constrained algebra + Hermitianity + displacement            PROVED / #96
  -> exact moment rank; finrank = 2*N-2                            PROVED / #98
  -> Euclidean constrained sector + canonical symmetry            PROVED / #98
  -> quadraticForm <-> Euclidean inner-self bridge                 PROVED / #98
  -> constrained Euclidean negative direction                     PROVED / #98
  -> exact centered principal-block nesting                       PROVED / #100
  -> every centered moment + localized finite function preserved  PROVED / #100
  -> Euclidean isometric constrained zero extension               PROVED / #100
  -> fixed-L negative constrained tail for all M>=N0              PROVED / #100

NEXT
  reversal/parity and exact parity-sector dimensions
  global first-bad-N / 2D constrained-shell formalization
  constrained orthogonal compression + negative eigenmode
  first bad parity size / one-dimensional new shell
  scalar secular/KKT/displacement rigidity

PARALLEL
  source-faithful G1-B1B -> G1-final -> S-NEG -> G23

RH                                                                 OPEN
~~~

## Exact #100 endpoint

Lean proves that every hypothetical off-critical-line zero forces one fixed L>0 and N0>=2 such that for every M>=N0 there is a nonzero x in euclideanBoundaryFlatSubspace M with strictly negative real inner-self value for canonicalSourceMatrix.toEuclideanLin.

The centered embedding is exact, preserves every centered moment and the represented localized finite function, and is bundled as a Euclidean linear isometry. This is persistent constrained negativity, not yet a compressed eigenmode or a proof of RH.

## Next theorem program

The highest-leverage next slice is reversal/parity.

Use Fin.rev to prove centered-index reversal, simultaneous canonical-matrix reversal invariance, moment parity, displacement-vector oddness, invariance of the constrained sector, compatibility with the #100 embedding, and exact even/odd constrained dimensions.

#100 already implies that fixed-L badness is upward persistent. Therefore a nonempty bad-size set has a first bad N before parity is used. Combined with finrank V_N = 2*N-2, the new constrained shell at N->N+1 has total dimension two. Parity is expected to split that two-dimensional increment into one even and one odd dimension; this must be theorem-locked rather than inferred.

Then build the constrained orthogonal compression and extract a negative constrained eigenmode using finite-dimensional Rayleigh theory.

## Canonical normalization firewall

~~~text
canonicalSourceMatrix = cutoffFreeMatrix = sourceEq44Matrix = dictionaryMatrix
legacyPrintedMatrix = finiteMatrix
~~~

## Permanent firewalls

- OBS-015: source interface is not source negativity.
- OBS-017: raw function-space norm is not Euclidean Rayleigh normalization; #100 separately proves the Euclidean zero-extension isometry, while constrained compression remains open.
- DR-010 fitted small-commutator/eigenvector convergence remains falsified.
- exact low displacement rank alone does not imply positivity; the generic divided-difference displacement identity is diagonal-blind.
- principal-block/quadratic nesting does not imply full operator intertwining or literal nesting of compressed operators.
- green F1/K0-F1/K0-F1E/N-FLOW is not RH.

## Living research records

- research/RHRC/CURRENT_RESEARCH_PLAN.md
- research/RHRC/RESEARCH_LEADS.md
- research/RHRC/CLAIM_REGISTRY.json
- research/RHRC/R003_PROMOTED_BINDINGS.json
- research/RHRC/routes/ROUTE_REGISTRY.json
- research/RHRC/routes/R003_ccm_bridge/README.md
- research/RHRC/RESEARCH_LEADS_POST_100_DELTA.md
- research/RHRC/routes/R003_ccm_bridge/K0F1E_POST_GREEN_EUCLIDEAN_RESET_2026_09_02.md

The external v1.7 handover has reached its retirement condition. External v2.0 should be written against the post-#100 repository state; it is not a repository artifact.

**RH remains OPEN.**
