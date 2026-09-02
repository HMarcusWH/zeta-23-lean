# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**
>
> This repository contains theorem-backed research infrastructure and formally validated constraints relevant to the Riemann Hypothesis. Green supporting mathematics is progress, not a proof of RH.

## Current authority snapshot

~~~text
theorem-state anchor = PR #96 merge 3712746a144d630ee41b89527b098e392822f2c6
theorem tree = 1d43b31bf9750375189a1ccd2e65bc0a662fc7c4
theorem-bearing merged through = PR #96
live GitHub main = authoritative
date = 2026-09-02
RH = OPEN
~~~

Recent theorem-bearing merges:

~~~text
#93 F0-B1C-B legal boundary-flat WCONT approximation
#94 strict finite sign transfer + F1 finite canonical negative obstruction
#96 K0/K1-F1 constrained canonical finite-wall package
~~~

Exact #96 validation:

~~~text
PR #96 head = d628b7332e908701e85ef8ea33309e2bf548f2e5
synthetic merge = 5830d75ec649f065925f5f3a1a7c823d8a5b42b9
validated tree = 1d43b31bf9750375189a1ccd2e65bc0a662fc7c4
merge/main = 3712746a144d630ee41b89527b098e392822f2c6
RHRC #679 = SUCCESS
Permansson #452 = SUCCESS
CCM build = SUCCESS
ExceptionalZero build = SUCCESS
forbidden-placeholder gate = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
~~~

The successful synthetic merge and the merged main commit have the same tree.

## Current RH-directed theorem ladder

~~~text
off-line zeta zero
  -> compact C² pole-neutral h with Re W(h,h)<0                  PROVED
  -> strict aperture collar tsupport h ⊂ (0,L)                  PROVED
  -> legal boundary-flat finite approximation in WCONT topology PROVED
  -> strict finite negative W value                              PROVED
  -> finite canonical negative quadratic direction              PROVED / F1
  -> constrained subspace + moment flag + Hermitianity           PROVED / K0-F1
  -> exact one-channel displacement on u,Du,D²u                  PROVED / K0-F1
  -> nonzero/unit constrained negative canonical witness         PROVED / #96

NOW
  Euclidean/PiLp₂ constrained-sector transport
  exact codimension/rank theorem
  raw quadraticForm ↔ Euclidean inner-self bridge

THEN
  compressed self-adjoint canonical operator
  negative constrained Rayleigh/eigenmode

NEXT DECISION
  KKT + Krylov/Hankel rigidity
  versus parity/reversal
  versus aperture-flow / first-singularity

RH                                                         OPEN
~~~

## F1 and #96 constrained finite obstruction

PR #94 proves `Zeta23.ExceptionalZero.exists_boundaryFlat_negativeCanonicalSourceQuadraticForm_of_offLine_zero`.

PR #96 proves the stronger constrained packaging:

`Zeta23.ExceptionalZero.exists_unit_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero`.

For every hypothetical off-line zeta zero there exist L>0, N>=1 and u such that

~~~text
u ∈ boundaryFlatSubspace N
‖u‖ = 1
Re (quadraticForm (canonicalSourceMatrix L N) u) < 0.
~~~

The norm here is the norm of the raw function type `Fin (...) → ℂ`. It is a valid scale normalization, but it is **not** the Euclidean/PiLp₂ Hilbert normalization required by the planned Rayleigh step.

## K0-F1 — formally closed by PR #96

Let D=`indexMatrix N`, M=`canonicalSourceMatrix L N` and g=`displacementVector L N`.

PR #96 theorem-locks:

~~~text
u ∈ boundaryFlatSubspace N
  ↔ BoundaryFlatCoefficients N u

M_k(Du) = M_{k+1}(u)

u    kills M0,M1,M2
Du   kills M0,M1
D²u  kills M0

Mᴴ = M
~~~

and, for every zero-moment v,

~~~text
[D,M] v = -1 * displacementPairing(L,N,v).
~~~

Hence for boundary-flat u the commutators on u, Du and D²u lie entirely in the all-ones channel.

Do not assume D preserves the full boundary-flat sector: M3(u)=0 is not available.

## Post-#96 derived leads

The following are **DERIVED / not yet theorem-locked**:

- for N>=1 the three moment constraints should have exact codimension 3;
- therefore a nonzero F1/#96 witness should force N>=2;
- the first 4×4 M-weighted Krylov block `<D^a u, M D^b u>` should be real Hankel.

These are active targets/leads, not promoted claims.

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
- raw function-space unit norm is not the Euclidean Rayleigh sphere; see OBS-017.
- the correction vector alone is not a legal W test.
- low displacement rank or one-channel collapse alone is not positivity or RH.
- DR-010 fitted small-commutator/eigenvector convergence remains falsified.
- green F1/K0-F1 is not RH.

## Living research records

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS.md`
- `research/RHRC/CLAIM_REGISTRY.json`
- `research/RHRC/routes/ROUTE_REGISTRY.json`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/RESEARCH_LEADS_POST_96_DELTA.md`
- `research/RHRC/routes/R003_ccm_bridge/K0F1_POST_GREEN_CONSTRAINED_FINITE_WALL_RESET_2026_09_02.md`

Historical settlements remain frozen.

**RH remains OPEN.**
