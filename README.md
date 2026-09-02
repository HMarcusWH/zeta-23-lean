# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**
>
> This repository contains theorem-backed research infrastructure and formally validated constraints relevant to the Riemann Hypothesis. Green supporting mathematics is progress, not a proof of RH.

## Current authority snapshot

~~~text
main = 8b54a72767c2703351990e2a67354511e9c9b83a
tree = 0fca10d1904d85bd33763cc6728e22c1c5b9ef5d
merged through = PR #94
date = 2026-09-02
RH = OPEN
~~~

Recent theorem-bearing merges:

~~~text
#91 F0-B1C-A raw uniform localized C² approximation
#93 F0-B1C-B legal boundary-flat WCONT approximation
#94 strict finite sign transfer + F1 finite canonical negative obstruction
~~~

Exact F1 validation:

~~~text
PR #94 head = d357c1511dba8678eb3a3a10944596c33a65fa11
merge/main = 8b54a72767c2703351990e2a67354511e9c9b83a
tree = 0fca10d1904d85bd33763cc6728e22c1c5b9ef5d
RHRC #667 = SUCCESS
Permansson #440 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
~~~

## Current RH-directed theorem ladder

~~~text
off-line zeta zero
  -> compact C² pole-neutral h with Re W(h,h)<0                  PROVED
  -> strict aperture collar tsupport h ⊂ (0,L)                  PROVED
  -> legal boundary-flat finite approximation in WCONT topology PROVED
  -> strict finite negative W value                              PROVED
  -> finite canonical negative quadratic direction               PROVED / F1

NOW
  K0-F1 constrained canonical sector

THEN
  constrained negative compression / minimizer
  exact displacement rigidity
  aperture-flow / first-singularity only if still needed

RH                                                         OPEN
~~~

## F1 — finite canonical negative obstruction

PR #94 proves `Zeta23.ExceptionalZero.exists_boundaryFlat_negativeCanonicalSourceQuadraticForm_of_offLine_zero`.

For every hypothetical zeta zero off the critical line, there exist L>0, N>=1 and u such that

~~~text
BoundaryFlatCoefficients N u
Re (quadraticForm (canonicalSourceMatrix L N) u) < 0.
~~~

Boundary-flat means exactly centered moments M0=M1=M2=0.

This is a finite obstruction theorem. It is not canonical positivity and it is not RH.

## Post-F1 finite-wall frontier

Let D=indexMatrix N, M=canonicalSourceMatrix L N and g=displacementVector L N.

Already PROVED:

~~~text
D M - M D = g 1^T - 1 g^T.
~~~

For an F1 witness, the three moment constraints DERIVE

~~~text
1^T u     = 0
1^T D u   = 0
1^T D^2 u = 0.
~~~

The exact constrained commutator collapse on u, Du and D²u is DERIVED/LEAD until theorem-locked.

The next theorem package is K0-F1:

- package the boundary-flat sector as finite linear algebra;
- theorem-lock moment shift under D;
- theorem-lock the descending moment flag;
- expose canonical Hermitianity;
- theorem-lock exact constrained displacement collapse.

Do not assume D preserves the full boundary-flat sector: M3(u)=0 is not available.

## Canonical normalization firewall

~~~text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix.

legacyPrintedMatrix = finiteMatrix.
~~~

Absolute sign/inertia/spectral claims must use the canonical object or explicit scalar-shift bookkeeping.

## Parallel source-faithful route

S-GEOM/G1-B1A is PROVED. S-IFACE/G1-B1B, G1-final, S-NEG and G23 remain OPEN.

OBS-015 remains binding: source interface is not source negativity.

## Permanent firewalls

- OBS-016 remains a generic legality warning; #93 proves the primary R003 escape.
- the correction vector alone is not a legal W test.
- low displacement rank alone is not RH.
- DR-010 fitted small-commutator/eigenvector convergence remains falsified.
- green F1 is not RH.

## Living research records

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS.md`
- `research/RHRC/CLAIM_REGISTRY.json`
- `research/RHRC/routes/ROUTE_REGISTRY.json`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/RESEARCH_LEADS_POST_94_DELTA.md`
- `research/RHRC/routes/R003_ccm_bridge/F1_POST_GREEN_FINITE_WALL_RESET_2026_09_02.md`

Historical settlements remain frozen.

**RH remains OPEN.**
