# RHRC current research plan

> **Claim firewall: RH remains OPEN.**
>
> Live GitHub/compiler/CI evidence is authoritative. A documentation-only merge may advance the branch head without changing the theorem-state anchor below.

## Current theorem-state anchor

~~~text
theorem-bearing merge through = PR #96
PR #96 merge = 3712746a144d630ee41b89527b098e392822f2c6
theorem tree = 1d43b31bf9750375189a1ccd2e65bc0a662fc7c4
date = 2026-09-02
RH = OPEN
~~~

### Exact #96 validation

~~~text
PR #96 final head = d628b7332e908701e85ef8ea33309e2bf548f2e5
synthetic merge = 5830d75ec649f065925f5f3a1a7c823d8a5b42b9
synthetic tree = 1d43b31bf9750375189a1ccd2e65bc0a662fc7c4
merged tree = 1d43b31bf9750375189a1ccd2e65bc0a662fc7c4
RHRC #679 = SUCCESS
Permansson #452 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
forbidden-placeholder gate = SUCCESS
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
  K0-F1 constrained subspace packaging
  K0-F1 moment shift / descending flag
  K0-F1 canonical Hermitianity
  K0-F1 exact one-channel displacement collapse
  K0-F1 normalized constrained negative witness

NOW
  K0-F1E Euclidean/PiLp₂ constrained-sector transport
  K0-F1E exact rank/codimension of the moment constraints
  K0-F1E raw quadraticForm <-> Euclidean inner-self bridge

THEN
  K0-F1F compressed self-adjoint canonical operator
  K0-F1F negative constrained Rayleigh/eigenmode

NEXT DECISION GATE
  KKT + Krylov/Hankel rigidity
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

## 1. What #96 made formally true

Let

~~~text
D = indexMatrix N
M = canonicalSourceMatrix L N
g = displacementVector L N
V₂ = boundaryFlatSubspace N.
~~~

PR #96 proves:

~~~text
u ∈ V₂
  <-> BoundaryFlatCoefficients N u
  <-> M0(u)=M1(u)=M2(u)=0.

M_k(Du)=M_{k+1}(u).

u    kills M0,M1,M2.
Du   kills M0,M1.
D²u  kills M0.

Mᴴ=M.
~~~

The exact canonical displacement now collapses on every zero-moment vector:

~~~text
[D,M]v = -1 * displacementPairing(L,N,v)
whenever M0(v)=0.
~~~

Therefore for every boundary-flat u:

~~~text
[D,M]u
[D,M]Du
[D,M]D²u
~~~

all lie in the one-dimensional all-ones forcing channel.

The pairing is bilinear, not Hermitian.

## 2. Exact normalized constrained F1 endpoint

PR #96 proves:

~~~text
off-line zero
  -> exists L>0,N>=1,u,
       u ∈ V₂
       and ‖u‖=1
       and Re quadraticForm(M,u)<0.
~~~

The witness is also theoremized as nonzero before normalization.

**Norm firewall:** the displayed norm is the norm on the raw function type `Fin (...) -> ℂ`. It is a valid homogeneous normalization. It is not the Euclidean/PiLp₂ norm consumed by Mathlib's Rayleigh theory.

## 3. K0-F1E — Euclidean/Hilbert transport

**Status: OPEN / NOW.**

Use the existing Mathlib finite Hilbert chassis:

~~~text
EuclideanSpace ℂ (Fin (2*N+1))
Matrix.toEuclideanLin
Submodule orthogonal projection
Analysis.InnerProductSpace.Rayleigh
~~~

### K0-F1E-A — Euclidean sector packaging

Transport the three moment kernels to a complex subspace of

~~~text
EuclideanSpace ℂ (Fin (2*N+1)).
~~~

The transport must preserve the coordinate equations exactly.

### K0-F1E-B — exact rank and codimension

For N>=1, theorem-lock linear independence of

~~~text
1, d, d²
~~~

on the centered grid, for example through the -1,0,+1 coordinates / Vandermonde minor.

Target:

~~~text
codim V₂ = 3
finrank V₂ = 2*N-2.
~~~

This is currently DERIVED, not PROVED.

### K0-F1E-C — strengthen the F1 mode floor

Composition target:

~~~text
nonzero u ∈ V₂ and N>=1
  -> N>=2.
~~~

This should strengthen the current existential witness from N>=1 to N>=2.

Status: DERIVED / OPEN FORMALIZATION.

### K0-F1E-D — quadratic-form / Hilbert bridge

Prove the exact convention-compatible identity between

~~~text
quadraticForm M u
~~~

and the Euclidean inner-self value of

~~~text
M.toEuclideanLin.
~~~

Do not guess inner-product argument order or conjugation orientation; let Lean fix it.

## 4. K0-F1F — constrained compression and negative eigenmode

**Status: OPEN / NEXT.**

Let P_V be the orthogonal projection onto the Euclidean version of V₂.

Build the compressed operator on V₂, conceptually

~~~text
T_V = P_V M |_V.
~~~

Targets:

1. T_V is self-adjoint.
2. #96 supplies a negative Rayleigh direction after Euclidean transport.
3. The finite-dimensional Rayleigh infimum is negative.
4. Mathlib's `LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional` or the equivalent minimizer theorem supplies a constrained eigenmode:

~~~text
T_V u = lambda u
lambda < 0
u != 0.
~~~

This is a compressed eigenvector, not automatically a full eigenvector of M.

## 5. KKT ambient form

After exact codimension three and the constrained eigenmode are proved, the expected ambient reformulation is

~~~text
M u = lambda u + a0*1 + a1*d + a2*d²
with lambda < 0.
~~~

Status: LEAD / OPEN.

Do not promote this merely from the existence of a constrained negative direction.

## 6. Post-#96 Krylov/Hankel clue

For a boundary-flat u define

~~~text
H_ab = <D^a u, M D^b u>.
~~~

Using the proved one-channel commutator collapse and zero sums of u,Du,D²u, the following is DERIVED for 0<=a,b<=2:

~~~text
H_(a+1,b) = H_(a,b+1).
~~~

Together with Hermitianity, this suggests the full 4×4 block for 0<=a,b<=3 is real Hankel.

**Status: DERIVED / LEAD; not theorem-locked.**

Promotion value: this may convert the first constrained Krylov sector into a truncated moment/Hankel object that can be composed with the future negative constrained eigenmode.

## 7. Falsification checks

- A real Hankel matrix can be indefinite.
- One-channel commutator collapse does not imply positivity.
- D does not preserve V₂; M3(u)=0 is unavailable.
- A constrained eigenvector is not a full eigenvector of M.
- Low displacement rank remains generic finite structure, not RH.
- The raw #96 norm-one theorem is not a Euclidean Rayleigh theorem.
- Global PSD of canonicalSourceMatrix would be substantially stronger than the currently proved constrained obstruction and must not be treated as a cheap lemma.
- Source QW remains a separate lane under OBS-015.

## 8. Deferred live routes

### Parity/reversal

Still live. It becomes more valuable after a constrained eigenmode exists because parity could split the compressed problem and may supply additional automatic odd-moment cancellation.

### K1 aperture flow / first singularity

Still live. Defer until the constrained spectral object is explicit unless a positive fixed-N anchor becomes independently available.

### K2 singular kernel/displacement rigidity

Still live downstream of compression/parity. Do not assume one-dimensional kernel.

### Source-faithful route

S-GEOM/G1-B1A is proved. S-IFACE/G1-B1B, G1-final, S-NEG and G23 remain OPEN as an independent cross-check.

## 9. Dead/fallback classification

DR-010 remains dead. The exact D/M/g route now has a theoremized constrained one-channel collapse but makes no fitted-generator, asymptotic-small-commutator or spectral-gap inference.

Primary-route Fourier/legalization fallbacks remain demoted after #93/#94.

## 10. Highest-leverage next implementation

Primary theorem package:

~~~text
Euclidean constrained sector
  -> exact codim/rank
  -> N>=2 strengthening
  -> quadratic-form/inner-product bridge
  -> compressed self-adjoint operator
  -> negative constrained eigenmode.
~~~

Do not mix parity, aperture flow, source-QW work or a global positivity claim into the first Euclidean bridge PR unless the compiler exposes a genuine dependency.

## Current records

Latest delta: `research/RHRC/RESEARCH_LEADS_POST_96_DELTA.md`.

Latest settlement: `research/RHRC/routes/R003_ccm_bridge/K0F1_POST_GREEN_CONSTRAINED_FINITE_WALL_RESET_2026_09_02.md`.

**RH remains OPEN.**
