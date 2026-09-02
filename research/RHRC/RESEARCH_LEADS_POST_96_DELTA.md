# RHRC research leads — post-PR #96 delta

> **Claim firewall: RH remains OPEN.**

This file records only the research-state changes created by green/merged PR #96. It does not replace `RESEARCH_LEADS.md`.

## Exact theorem-state anchor

~~~text
PR #96 head = d628b7332e908701e85ef8ea33309e2bf548f2e5
synthetic merge = 5830d75ec649f065925f5f3a1a7c823d8a5b42b9
merge = 3712746a144d630ee41b89527b098e392822f2c6
tree = 1d43b31bf9750375189a1ccd2e65bc0a662fc7c4
RHRC #679 = SUCCESS
Permansson #452 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
forbidden-placeholder gate = SUCCESS
~~~

The synthetic merge and merged main commit have the same tree.

## Promotions

### L-K0F1-01 — constrained canonical sector

**Research status:** PROMOTED / CLOSED  
**Formal status:** PROVED

PR #96 proves:

~~~text
u ∈ boundaryFlatSubspace N
  <-> BoundaryFlatCoefficients N u

M_k(Du)=M_{k+1}(u)

u    kills M0,M1,M2
Du   kills M0,M1
D²u  kills M0

canonicalSourceMatrixᴴ = canonicalSourceMatrix

[D,M]v = -1 * displacementPairing(v)
for every zero-moment v
~~~

and specializes the last identity to u, Du and D²u.

### Normalized constrained F1 obstruction

**Formal status:** PROVED

~~~text
off-line zero
  -> exists L>0,N>=1,u,
       u ∈ boundaryFlatSubspace N
       and ‖u‖=1
       and Re quadraticForm(canonicalSourceMatrix L N,u)<0.
~~~

The norm is the raw function-space norm, not the Euclidean/PiLp₂ Hilbert norm.

## New primary lead

### L-K0F1-02 — Euclidean constrained compression

**Research status:** ACTIVE / HIGHEST-LEVERAGE NEXT  
**Formal status:** OPEN

Build:

~~~text
Euclidean constrained sector
  -> quadraticForm / inner-self bridge
  -> orthogonal compression of canonicalSourceMatrix
  -> compressed self-adjoint operator
  -> negative constrained Rayleigh direction
  -> negative constrained eigenmode.
~~~

Mathlib already supplies `Matrix.toEuclideanLin`, finite-dimensional orthogonal projection, and Rayleigh extremizer/eigenvalue theorems.

The missing work is project-specific transport and compression.

## New cheap strengthening

### L-K0F1-03 — exact codimension three

**Formal status:** DERIVED / OPEN FORMALIZATION

For N>=1, M0,M1,M2 should be independent via the -1,0,+1 Vandermonde minor.

Expected:

~~~text
codim V₂ = 3
finrank V₂ = 2*N-2.
~~~

Since #96 produces a nonzero vector in V₂, this should strengthen the existential mode floor to N>=2.

Do not promote until Lean proves it.

## New composition lead

### L-K0F1-04 — constrained Krylov Hankel block

**Formal status:** DERIVED / LEAD

For

~~~text
H_ab = <D^a u, M D^b u>
~~~

the #96 one-channel commutator plus zero-sum moment flag derives

~~~text
H_(a+1,b)=H_(a,b+1)
for 0<=a,b<=2.
~~~

Hermitianity then suggests the full 4×4 block 0<=a,b<=3 is real Hankel.

This is not positivity. Promotion requires an explicit Lean theorem and a downstream restriction stronger than generic indefinite Hankel structure.

## New firewall

OBS-017: raw function-space norm one is not Euclidean Rayleigh normalization.

Any spectral minimizer/eigenvector proof must pass through an explicit `EuclideanSpace` / PiLp₂ bridge.

## Route ordering change

Before #96:

~~~text
K0-F1
  -> decision among compression / parity / aperture flow.
~~~

After #96:

~~~text
K0-F1 [PROVED]
  -> Euclidean constrained compression [NOW]
  -> negative constrained eigenmode
  -> test KKT/Krylov-Hankel rigidity
  -> parity or aperture flow only as demanded by the resulting obstruction.
~~~

DR-010 remains dead.

S-GEOM/G1-B1A remains proved; S-IFACE/G1-B1B, G1-final, S-NEG and G23 remain open on the parallel source-faithful lane.

**RH remains OPEN.**
