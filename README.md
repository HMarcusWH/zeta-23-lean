# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**
>
> This repository contains theorem-backed research infrastructure and formally validated constraints relevant to the Riemann Hypothesis. Green supporting mathematics is progress, not a proof of RH.

## Current authority snapshot

~~~text
theorem-state anchor = PR #98 merge 4f212e35fefb339646e294573dcb390dae2f6181
theorem tree = 84a678327fffe6806e1e786ac2e159a5ce628f67
theorem-bearing merged through = PR #98
live GitHub main = authoritative
date = 2026-09-02
RH = OPEN
~~~

Exact PR #98 validation:

~~~text
final head = 723c63badb2ac787c3dfa78369909477af6bc6a4
head tree = 84a678327fffe6806e1e786ac2e159a5ce628f67
merge/main = 4f212e35fefb339646e294573dcb390dae2f6181
merge tree = 84a678327fffe6806e1e786ac2e159a5ce628f67
RHRC #685 = SUCCESS
Permansson #458 = SUCCESS
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
  -> nonzero constrained witness forces N>=2                      PROVED / #98
  -> Euclidean constrained sector + canonical symmetry            PROVED / #98
  -> quadraticForm <-> Euclidean inner-self bridge                 PROVED / #98
  -> constrained Euclidean negative direction                     PROVED / #98

NEXT
  exact centered finite-N nesting / zero-extension persistence
  reversal/parity and parity-sector dimensions
  constrained orthogonal compression + negative eigenmode
  first bad parity size / one-dimensional new shell
  scalar secular/KKT/displacement rigidity

PARALLEL
  source-faithful G1-B1B -> G1-final -> S-NEG -> G23

RH                                                                 OPEN
~~~

## Exact #98 endpoint

Lean proves that every hypothetical off-critical-line zero forces L>0, N>=2 and a nonzero x in EuclideanSpace ℂ (Fin (2*N+1)) with x in euclideanBoundaryFlatSubspace N and strictly negative real inner-self value for canonicalSourceMatrix.toEuclideanLin.

This is a negative constrained direction, not yet a compressed eigenmode.

## Next theorem program

Reopen the exact centered nesting program already designed in historical v0.8/v0.9:

~~~text
iota_{N,M}(i).val = i.val + (M-N)
centeredIndex M (iota i) = centeredIndex N i
canonicalSourceMatrix L M restricted to the central block
  = canonicalSourceMatrix L N
~~~

Then build raw and Euclidean zero-extension maps, prove moment/subspace preservation, Euclidean inner/norm preservation, and exact quadratic preservation.

Do not use prefix Fin inclusion and do not identify the raw function-space norm with the Euclidean norm.

## Canonical normalization firewall

~~~text
canonicalSourceMatrix = cutoffFreeMatrix = sourceEq44Matrix = dictionaryMatrix
legacyPrintedMatrix = finiteMatrix
~~~

## Permanent firewalls

- OBS-015: source interface is not source negativity.
- OBS-017: PR #98 closes coordinate/subspace/quadratic transport; orthogonal compression remains open.
- DR-010 fitted small-commutator/eigenvector convergence remains falsified.
- exact low displacement rank alone does not imply positivity; the generic divided-difference displacement identity is diagonal-blind.
- green F1/K0-F1/K0-F1E is not RH.

## Living research records

- research/RHRC/CURRENT_RESEARCH_PLAN.md
- research/RHRC/RESEARCH_LEADS.md
- research/RHRC/CLAIM_REGISTRY.json
- research/RHRC/R003_PROMOTED_BINDINGS.json
- research/RHRC/routes/ROUTE_REGISTRY.json
- research/RHRC/routes/R003_ccm_bridge/README.md
- research/RHRC/RESEARCH_LEADS_POST_98_DELTA.md
- research/RHRC/routes/R003_ccm_bridge/K0F1E_POST_GREEN_EUCLIDEAN_RESET_2026_09_02.md

The external v1.7 handover has reached its own retirement condition. External v2.0 is due after this repository synchronization; it is not a repository artifact.

**RH remains OPEN.**
