# RHRC current research plan

> **Claim firewall: RH remains OPEN.**
>
> Live GitHub/compiler/CI evidence is authoritative. A documentation-only merge may advance the branch head without changing the theorem-state anchor below.

## Current theorem-state anchor

~~~text
theorem-bearing merge through = PR #100
final validated head = 497adcd6a746d49fd23654cabf4ed8f0c58db8a9
merge = 4427e2a8c8d90dbb7d66d9d96f9a410cecb75df9
theorem tree = 705ab8b88728a5b90d850eb4b51c01a66811f088
RHRC #691 = SUCCESS
Permansson #464 = SUCCESS
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
  N-FLOW exact centered finite-N embedding and coherent composition
  N-FLOW exact canonical principal-block nesting
  N-FLOW every centered moment preserved by zero extension
  N-FLOW localized finite function preserved exactly
  N-FLOW Euclidean zero extension is a linear isometry
  N-FLOW constrained membership + canonical quadratic value preserved
  N-FLOW off-line zero -> fixed-L negative constrained tail for all M>=N0

NOW
  PARITY centered-index reversal and matrix invariance
  PARITY moment/displacement parity and constrained-sector invariance
  PARITY exact even/odd constrained dimensions
  formalize global badness / upward closure / first bad N / total 2D shell

THEN
  K0-F1F orthogonal constrained compression
  K0-F1F negative constrained eigenmode
  parity-resolved first bad size
  one-dimensional new constrained parity shell
  scalar constrained secular equation
  KKT normal-space identity + Krylov/Hankel composition

IF NEEDED
  K1 aperture flow / prime-event first crossing

PARALLEL SOURCE
  G1-B1B -> G1-final -> S-NEG -> G23

RH OPEN
~~~

## Exact #100 state

For V_N = euclideanBoundaryFlatSubspace N and M_N(L) = canonicalSourceMatrix.toEuclideanLin:

PR #98 proves finrank V_N = 2*N-2 for N>=1, the N>=2 floor for nonzero constrained witnesses, symmetry of M_N(L), the exact quadraticForm/inner-self bridge, and one negative constrained direction from any off-line zero.

PR #100 proves exact centered embeddings E_{N,M} for N<=M, coherent composition, exact canonical principal-block nesting, preservation of every centered moment and the represented localized finite function, Euclidean isometry, constrained-sector transport, and preservation of the canonical quadratic value. It upgrades the exceptional-zero endpoint to:

~~~text
off-line zero
  -> exists L>0,N0>=2,
       for every M>=N0
       exists x_M != 0,
         x_M ∈ V_M
         and Re <M_M(L)x_M,x_M> < 0.
~~~

This is persistent constrained negativity at one fixed aperture. It is not a compressed eigenmode, positivity theorem, finite-to-infinite theorem, or RH theorem.

## Derived immediately from #98 + #100

**DERIVED / not yet separately theorem-locked:** for fixed L, define Bad_L(N) by existence of a nonzero negative constrained direction in V_N. #100 gives upward persistence:

~~~text
N <= M and Bad_L(N) -> Bad_L(M).
~~~

Hence any nonempty bad-size set has a least N*. No parity theorem is required for existence of the global first bad size.

Also, because finrank V_N = 2*N-2 and E_{N,N+1} is an isometric injection into V_{N+1}, the orthogonal complement of the embedded V_N inside V_{N+1} has total finrank two. Parity is required before splitting that 2D increment into one even and one odd dimension.

**Firewall:** neither statement implies literal operator intertwining M_M E = E M_N or literal nesting of orthogonally compressed operators.

## PARITY — highest-leverage next theorem slice

Use Mathlib Fin.rev.

Prove:

~~~text
centeredIndex N i.rev = - centeredIndex N i
reversal commutes with centered embedding
canonicalSourceMatrix is invariant under simultaneous reversal
indexMatrix anti-commutes with reversal
centeredMoment N k (R u) = (-1)^k * centeredMoment N k u
displacementVector is odd under reversal
boundaryFlatSubspace and euclideanBoundaryFlatSubspace are reversal-invariant
~~~

Then define even/odd constrained sectors and theorem-lock their exact dimensions. Expected for N>=2:

~~~text
finrank V_N^even = N-1
finrank V_N^odd  = N-1.
~~~

Do not infer the 1+1 parity growth merely from total finrank growth by two.

Promising composition to falsify aggressively: if displacementVector is odd, its bilinear pairing with an even vector should cancel under reversal. Together with the #96 constrained displacement identity this may force a stronger commutator collapse in the even sector. This is a LEAD until formalized.

## Global first-bad finite shell

Formalize Bad_L(N), the #100 upward-closure theorem, least bad N*, and the previous-size nonnegativity statement.

Before parity, the new constrained shell at N* has total dimension two. This already gives a 2x2 fallback finite-shell problem.

After exact parity dimensions, refine badness to parity sectors. The first bad parity shell should then have finrank one.

## K0-F1F — constrained spectral extraction

Build the operator directly on the constrained subtype with:

~~~text
V_N.orthogonalProjectionOnto ∘ M_N(L) ∘ V_N.subtypeL.
~~~

Prove symmetry and equality of constrained and ambient inner-self values on V_N. Feed the negative direction into Mathlib finite-dimensional Rayleigh theory to obtain lambda<0 and a nonzero constrained eigenvector.

Also prove the cheaper ambient negative-eigenvalue corollary as a spectral API sanity check.

A second high-value theorem is monotonicity of the constrained minimum Rayleigh value in N. #100 gives the correct variational ingredients — isometric inclusion and exact quadratic preservation — even though the compressed operators themselves need not literally nest.

## First bad parity size / scalar shell

After parity preservation and exact parity dimensions, define parity-resolved badness and take the first bad size N* in the bad parity sector.

The orthogonal complement of the embedded previous parity sector inside the first-bad parity sector then has finrank one.

At lambda<0 the retained previous constrained block is nonnegative, hence A-lambda I is strictly positive and invertible. This creates a scalar constrained secular equation.

**Firewall:** this constrained shell is not automatically the historical ambient coordinate-shell Schur complement.

## KKT

Before asserting an ambient residual formula, prove:

~~~text
V_N^perp = span_C {1,d,d²}.
~~~

Only then derive M u = lambda u + a0*1 + a1*d + a2*d². Parity may reduce the residual channels.

## Krylov/Hankel

#100 preserves every centered moment under extension. Pair this with the #96 displacement package and, ideally, theorem-lock exact compatibility of the centered-index operator with zero extension.

Then formalize the exact range of H_(a+1,b)=H_(a,b+1) implied by #96. Test whether the negative parity eigenmode + reduced KKT residual + exact displacement + Hankel recurrence creates a genuine finite obstruction. If not, demote it.

## K1 remains deferred

Continuity in L, prime-power birth continuity, canonical derivative jump, positive anchor and first L crossing remain live. The prime-event jump must be rederived on canonicalSourceMatrix after #73. Do not confuse identity I with all-ones J.

Open K1 only after the finite-N/parity/spectral state is explicit unless a positive fixed-N anchor appears independently.

## Parallel/dead lanes

- source-faithful G1-B1B/G1-final/S-NEG/G23 remains independent;
- DR-010 remains dead;
- R002/Bombieri remain comparator lanes without exact transfer;
- low displacement rank alone is insufficient because the generic divided-difference displacement is diagonal-blind;
- finite-to-infinite convergence remains dormant: #100 proves exact finite nesting, not topology, determinant convergence, closure, or zero transfer.

## External roadmap

The v1.7 retirement condition has fired. External v2.0 should be produced against the post-#100 theorem state after this repository synchronization; do not create it inside this PR.

**RH remains OPEN.**
