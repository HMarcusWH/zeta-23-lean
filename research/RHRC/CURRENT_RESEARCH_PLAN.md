# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

~~~text
main = 8b54a72767c2703351990e2a67354511e9c9b83a
tree = 0fca10d1904d85bd33763cc6728e22c1c5b9ef5d
merged through = PR #94
date = 2026-09-02
RH = OPEN
~~~

### Exact F1 theorem state

~~~text
PR #94 final head = d357c1511dba8678eb3a3a10944596c33a65fa11
merge = 8b54a72767c2703351990e2a67354511e9c9b83a
tree = 0fca10d1904d85bd33763cc6728e22c1c5b9ef5d
RHRC #667 = SUCCESS
Permansson #440 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
~~~

## One-screen theorem frontier

~~~text
DONE
  W2-A genuine W -> literatureRHS + summability
  W0 off-line zero -> compact C² pole-neutral negative W test
  W1 strict support collar
  W2-ZS concrete-zeta zero-side evenization
  direct diagonal W identity
  G1-A finite additive restriction
  F0-B1A legal boundary-flat finite carrier
  F0-B1B exact three-mode projection
  WCONT-A quantitative genuine-W continuity
  F0-B1C-A raw uniform localized C² approximation
  F0-B1C-B legal boundary-flat WCONT approximation
  strict finite sign transfer
  F1 canonical finite negative obstruction

NOW
  K0-F1 constrained canonical sector

NEXT DECISION GATE
  constrained negative compression / minimizer
  versus parity/reversal
  versus aperture-flow / first-singularity

PARALLEL SOURCE
  S-GEOM / G1-B1A [proved]
  S-IFACE / G1-B1B
  G1-final
  S-NEG
  G23

RH OPEN
~~~

## 1. What F1 changes

The primary approximation/sign-transfer route is closed. Lean now proves:

~~~text
off-line zero
  -> exists L>0, N>=1, u,
       BoundaryFlatCoefficients N u
       and Re quadraticForm(canonicalSourceMatrix L N) u < 0.
~~~

The active obstruction is finite.

## 2. Exact finite data after F1

BoundaryFlatCoefficients is exactly M0=M1=M2=0.

Let D=indexMatrix N, M=canonicalSourceMatrix L N and g=displacementVector L N.

PROVED:

~~~text
D M - M D = g 1^T - 1 g^T.
~~~

DERIVED:

~~~text
1^T u = 0
1^T D u = 0
1^T D^2 u = 0.
~~~

Do not claim D preserves the full boundary-flat sector; M3(u)=0 is not available.

## 3. K0-F1 — constrained canonical sector

**Status: OPEN / NOW.**

### K0-F1A — subspace packaging

Package the exact three moment constraints as a reusable finite subspace while preserving `BoundaryFlatCoefficients` as the canonical proposition.

Preferred theorem:

~~~text
u ∈ boundaryFlatSubspace N
  <-> BoundaryFlatCoefficients N u.
~~~

### K0-F1B — moment shift

Theorem-lock

~~~text
M_k(Du) = M_{k+1}(u).
~~~

and the descending flag

~~~text
u in V2 -> Du in V1
u in V2 -> D²u in V0.
~~~

### K0-F1C — canonical Hermitianity

Expose the exact Matrix-level Hermitian/conjTranspose theorem required by later spectral APIs. This is packaging, not positivity.

### K0-F1D — constrained displacement collapse

From [D,M]=g1^T-1g^T and 1^T v=0, theorem-lock the exact mulVec identity showing [D,M]v lies in span{1}. Then specialize to u, Du and D²u for boundary-flat u.

The scalar orientation must come from Lean's conventions, not documentation guesswork.

## 4. Why this comes before old parity-first K0

Before F1 the dangerous finite vector was unknown. After F1 it carries three exact moment annihilations, so consuming those constraints against exact displacement has higher information value than building the whole reversal/parity suite first.

Parity remains live downstream.

## 5. Next decision after K0-F1

Test the constrained compression/minimizer route.

Candidate LEAD:

~~~text
F1 negative direction
  -> negative minimum on the unit sphere of V2
  -> P_V M P_V u = lambda u, lambda < 0.
~~~

Equivalent KKT form may be

~~~text
M u = lambda u + a0*1 + a1*d + a2*d^2.
~~~

An F1 witness is not automatically a full eigenvector of M.

## 6. Deferred live routes

- reversal/parity;
- canonical aperture flow / first singularity;
- prime-event derivative jump;
- distinguished resolvent channels;
- source-faithful QW route as independent cross-check.

## 7. Dead/fallback classification

DR-010 remains dead. The exact D/M/g constrained route is distinct.

Primary-route Fourier/legalization fallbacks are demoted after #93/#94.

## 8. Highest-leverage next implementation

~~~text
NEW     Zeta23/CCM/ConstrainedCanonicalSector.lean
MODIFY  Zeta23/CCM.lean
MODIFY  Zeta23/CCM/ClaimBindings.lean
~~~

No source-QW work, aperture-flow code, reversal/parity suite, numerical fitting, or RH claim in that PR.

After green, run a full Post-Green Research Pass.

## Current records

Latest delta: `research/RHRC/RESEARCH_LEADS_POST_94_DELTA.md`.

Latest settlement: `research/RHRC/routes/R003_ccm_bridge/F1_POST_GREEN_FINITE_WALL_RESET_2026_09_02.md`.

**RH remains OPEN.**
