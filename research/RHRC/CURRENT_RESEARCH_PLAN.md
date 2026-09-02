# RHRC current research plan

> **Claim firewall: RH remains OPEN.**
>
> Live GitHub/compiler/CI evidence is authoritative. A documentation-only merge may advance the branch head without changing the theorem-state anchor below.

## Current theorem-state anchor

~~~text
theorem-bearing merge through = PR #98
final head = 723c63badb2ac787c3dfa78369909477af6bc6a4
merge = 4f212e35fefb339646e294573dcb390dae2f6181
theorem tree = 84a678327fffe6806e1e786ac2e159a5ce628f67
RHRC #685 = SUCCESS
Permansson #458 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
date = 2026-09-02
RH = OPEN
~~~

## One-screen frontier

~~~text
DONE
  W2-A / W0 / W1 / W2-ZS
  G1-A
  F0-B1A/B1B/WCONT/F0-B1C-A/B
  strict finite sign transfer
  F1 canonical finite negative obstruction
  K0-F1 constrained algebra / Hermitianity / displacement
  K0-F1E exact rank and finrank 2*N-2
  K0-F1E N>=2 floor
  K0-F1E Euclidean constrained sector
  K0-F1E canonical Euclidean symmetry
  K0-F1E quadraticForm <-> Euclidean inner-self
  K0-F1E off-line zero -> Euclidean constrained negative direction

NOW
  N-FLOW-A exact centered finite-N nesting
  N-FLOW-B raw + Euclidean zero-extension preservation

THEN
  PARITY reversal invariance and parity dimensions
  K0-F1F orthogonal constrained compression
  K0-F1F negative constrained eigenmode
  first bad parity size
  one-dimensional new constrained shell
  scalar constrained secular equation
  KKT normal-space identity + Krylov/Hankel composition

IF NEEDED
  K1 aperture flow / prime-event first crossing

PARALLEL SOURCE
  G1-B1B -> G1-final -> S-NEG -> G23

RH OPEN
~~~

## Exact #98 state

For V_N = euclideanBoundaryFlatSubspace N and M_N(L) = canonicalSourceMatrix.toEuclideanLin, PR #98 proves finrank V_N = 2*N-2 for N>=1, the N>=2 floor for nonzero constrained witnesses, symmetry of M_N(L), the exact quadraticForm/inner-self bridge, and:

~~~text
off-line zero
  -> exists L>0,N>=2,x != 0,
       x ∈ V_N
       and Re <M_N(L)x,x> < 0.
~~~

This is a negative constrained direction, not a compressed eigenmode.

## N-FLOW-A — exact centered finite nesting

**OPEN / HIGHEST-LEVERAGE NEXT THEOREM SLICE.**

Resurrect the exact finite algebraic slice from historical v0.8/v0.9.

For N<=M define:

~~~text
iota_{N,M}(i).val = i.val + (M-N).
~~~

First prove centeredIndex preservation, then:

~~~text
(canonicalSourceMatrix L M).submatrix iota iota
  = canonicalSourceMatrix L N.
~~~

**Kill condition:** if exact nesting fails, stop. Approximate nesting is not a silent substitute. Prefix Fin inclusion is wrong.

## N-FLOW-B — raw and Euclidean extension

Define raw central zero extension independently of the Euclidean map.

Prove M0/M1/M2 preservation and boundary-flat preservation.

Then define the Euclidean extension and prove directly:

~~~text
<extendE x,extendE y> = <x,y>
||extendE x|| = ||x||
extendE(V_N) <= V_M
quadratic value is preserved.
~~~

Do not use the raw function-space norm to prove Euclidean isometry.

Consequence: a fixed-L negative constrained direction persists to every larger truncation. This is infrastructure, not by itself RH progress.

## PARITY

Use Fin.rev.

Prove centered-index reversal, matrix reversal invariance, oddness of displacementVector, moment parity, and V_N invariance.

Then theorem-lock parity dimensions rather than inferring them from total dimension growth. Expected for N>=2:

~~~text
finrank V_N^even = N-1
finrank V_N^odd  = N-1.
~~~

Only after this may the project claim one new dimension per parity sector when N grows by one.

## K0-F1F — constrained spectral extraction

Build the operator directly on the constrained subtype with:

~~~text
V_N.orthogonalProjectionOnto ∘ M_N(L) ∘ V_N.subtypeL.
~~~

Prove symmetry and equality of constrained and ambient inner-self values on V_N. Feed in #98 and Mathlib Rayleigh theory to obtain lambda<0 and a nonzero constrained eigenvector.

Also prove the cheaper ambient negative-eigenvalue corollary as a spectral API sanity check.

## First bad parity size

Define badness by existence of a negative direction in a fixed parity constrained sector.

After nesting/parity preservation, bad sizes are upward closed. Well-ordering gives the first bad N*.

If parity dimensions are proved, the orthogonal complement of the embedded previous parity sector inside the first-bad parity sector has finrank one.

At lambda<0 the previous retained block A is nonnegative, hence A-lambda I is positive and invertible. This creates a scalar constrained secular equation.

**Firewall:** this is not automatically the historical ambient coordinate-shell Schur complement.

## KKT

Before asserting an ambient residual formula, prove:

~~~text
V_N^perp = span_C {1,d,d²}.
~~~

Only then derive M u = lambda u + a0*1 + a1*d + a2*d². Parity may reduce the residual channels.

## Krylov/Hankel

Theorem-lock the exact range of H_(a+1,b)=H_(a,b+1) implied by #96. Test whether the negative parity eigenmode + reduced KKT residual + exact displacement + Hankel recurrence creates a genuine finite obstruction. If not, demote it.

## K1 remains deferred

Continuity in L, prime-power birth continuity, canonical derivative jump, positive anchor and first L crossing remain live. The prime-event jump must be rederived on canonicalSourceMatrix after #73. Do not confuse identity I with all-ones J.

Open K1 only after the finite-N/parity/spectral state is explicit unless a positive fixed-N anchor appears independently.

## Parallel/dead lanes

- source-faithful G1-B1B/G1-final/S-NEG/G23 remains independent;
- DR-010 remains dead;
- R002/Bombieri remain comparator lanes without exact transfer;
- low displacement rank alone is insufficient because the generic divided-difference displacement is diagonal-blind.

## External roadmap

The v1.7 retirement condition has fired. Produce the external v2.0 handover after this repo synchronization; do not create it inside this PR.

**RH remains OPEN.**
