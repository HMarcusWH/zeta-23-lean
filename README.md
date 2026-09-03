# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**
>
> This repository contains theorem-backed research infrastructure and formally validated constraints relevant to the Riemann Hypothesis. Green supporting mathematics is progress, not a proof of RH.

## Current authority snapshot

~~~text
theorem-state anchor = PR #103 merge c7129b1856ea03cdf8b831ae1424140f8a7d90a9
validated theorem head = af43242f55536a8170bf303b9c9558c6a0fccdcf
validated synthetic merge = 16c5ebaa6d6d7e14df853e9a0771ab5ef3b07aba
theorem tree = 56d082947fac6eb4666d0e0666e2c8bcd3c0a7e8
theorem-bearing merged through = PR #103
live GitHub main = authoritative
date = 2026-09-03
RH = OPEN
~~~

Exact PR #103 validation:

~~~text
base = a434737c088ad2651491f0131b6dd6794c129f4c
final head = af43242f55536a8170bf303b9c9558c6a0fccdcf
synthetic merge tested = 16c5ebaa6d6d7e14df853e9a0771ab5ef3b07aba
merge/main = c7129b1856ea03cdf8b831ae1424140f8a7d90a9
validated/merged theorem tree = 56d082947fac6eb4666d0e0666e2c8bcd3c0a7e8
RHRC #704 = SUCCESS
Permansson #477 = SUCCESS
CCM build = SUCCESS
ExceptionalZero build = SUCCESS
R003 normalization/source firewall = SUCCESS
forbidden-placeholder gate = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
~~~

The exact synthetic-merge tree that passed CI is the tree merged on main.

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
  -> constrained Euclidean negative direction                     PROVED / #98
  -> exact centered principal-block nesting                       PROVED / #100
  -> Euclidean isometric constrained N-flow                       PROVED / #100
  -> fixed-L negative constrained tail for all M>=N0              PROVED / #100
  -> exact centered reversal + matrix parity symmetry             PROVED / #102
  -> displacementVector odd + even commutator collapse            PROVED / #102
  -> V_N = V_N^+ direct-sum V_N^-                                 PROVED / #103
  -> D : V_N^+ ≃ₗ[ℂ] V_N^-                                       PROVED / #103
  -> finrank V_N^+ = finrank V_N^- = N-1                          PROVED / #103
  -> Euclidean parity sectors + parity-preserving N-flow          PROVED / #103

NEXT
  compile/import parity-badness module
  theorem-lock D / centered-N-flow compatibility
  exact quadratic parity splitting
  off-line zero -> one fixed bad parity tail
  least bad parity size + one-dimensional successor shell
  constrained orthogonal compression + negative eigenmode
  normal-space / KKT / scalar Schur-Feshbach rigidity

PARALLEL
  source-faithful G1-B1B -> G1-final -> S-NEG -> G23

RH                                                                 OPEN
~~~

## Validated source versus staged source

`Zeta23/CCM/ConstrainedParityGeometry.lean` is imported by `Zeta23.CCM` and was in the exact compiler-tested PR #103 import closure.

`Zeta23/CCM/ParityBadness.lean` is present on main but is **not imported by `Zeta23.CCM`**. Its declarations are therefore staged source, not compiler-validated project theorems. Repository presence and the no-placeholder grep are not substitutes for Lean elaboration. See `research/RHRC/VALIDATION_PROTOCOL.md` and OBS-018.

## What #102 and #103 changed

PR #102 proves the exact reversal chassis: centered-index sign reversal, compatibility with the centered embedding, moment parity, simultaneous reversal invariance of the canonical source matrix, oddness of the displacement vector, matrix-action commutation with reversal, and exact vanishing of the canonical commutator on even boundary-flat vectors.

PR #103 proves more than a parity dimension count. The centered-index operator itself induces a complex-linear equivalence

~~~text
D : V_N^+ ≃ₗ[ℂ] V_N^-.
~~~

The one ambient zero-index kernel of D is removed by boundary-flat moment zero; surjectivity is supplied by an explicit primitive of an odd vector with the central coefficient chosen to restore moment zero. Hence both parity sectors have exact finrank N-1, and exact centered Euclidean N-flow preserves each sector.

## Next theorem program

The first task is to bring the staged parity-badness layer into the authoritative compiler closure. In the same slice, theorem-lock the exact quadratic parity split and use the #100 negative witness plus #102 matrix parity symmetry to extract one fixed bad parity. Exact parity-preserving N-flow should then give a fixed-parity bad tail.

After that, take the least bad size in that parity and theorem-lock the one-dimensional new parity shell. Only then build the constrained orthogonal compression, extract a negative Rayleigh/eigenmode, prove the exact normal-space identity, and derive the scalar constrained Schur/Feshbach/KKT equation.

A high-value upstream compatibility theorem is:

~~~text
D_M (E_{N,M} u) = E_{N,M} (D_N u).
~~~

If true, D relates the one-dimensional even and odd successor quotients as well as the full constrained parity sectors.

## Canonical normalization firewall

~~~text
canonicalSourceMatrix = cutoffFreeMatrix = sourceEq44Matrix = dictionaryMatrix
legacyPrintedMatrix = finiteMatrix
~~~

Scalar identity shifts preserve eigenvectors, commutators and eigenvalue gaps/order, but not PSD, inertia, absolute eigenvalues, trace or determinant.

## Permanent firewalls

- OBS-015: source interface is not source negativity.
- OBS-017: raw function-space norm is not Euclidean Rayleigh normalization.
- OBS-018: merged source presence is not compiler validation; only the exact tested import/build closure is theorem authority.
- DR-010 fitted small-commutator/eigenvector convergence remains falsified.
- D-equivalence is algebraic, not proved unitary; equal parity dimensions do not imply equal spectra.
- ambient commutator collapse does not imply intertwining of future orthogonally compressed operators.
- one-dimensional first-bad shell geometry by itself is not a contradiction.
- green supporting mathematics is not RH.

## Living research records

- research/RHRC/CURRENT_RESEARCH_PLAN.md
- research/RHRC/RESEARCH_LEADS.md
- research/RHRC/CLAIM_REGISTRY.json
- research/RHRC/R003_PROMOTED_BINDINGS.json
- research/RHRC/routes/ROUTE_REGISTRY.json
- research/RHRC/routes/R003_ccm_bridge/README.md
- research/RHRC/VALIDATION_PROTOCOL.md
- research/RHRC/RESEARCH_LEADS_POST_102_DELTA.md
- research/RHRC/RESEARCH_LEADS_POST_103_DELTA.md

External v2.0 should be written against the post-#103 validated repository state; it is not a repository artifact unless explicitly requested.

**RH remains OPEN.**
