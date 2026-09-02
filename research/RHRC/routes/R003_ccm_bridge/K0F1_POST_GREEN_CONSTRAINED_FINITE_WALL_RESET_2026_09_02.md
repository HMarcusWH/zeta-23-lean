# K0-F1 post-green constrained finite-wall reset — 2026-09-02

> **RH remains OPEN.**
>
> This is the post-green settlement for PR #96. It records exactly what became theorem-backed and what the successful proof changes in the active finite-wall program.

## Exact validation authority

~~~text
PR #96 = K0/K1-F1 constrained canonical finite-wall package
final head = d628b7332e908701e85ef8ea33309e2bf548f2e5
validated synthetic merge = 5830d75ec649f065925f5f3a1a7c823d8a5b42b9
validated tree = 1d43b31bf9750375189a1ccd2e65bc0a662fc7c4
merged main commit = 3712746a144d630ee41b89527b098e392822f2c6
merged tree = 1d43b31bf9750375189a1ccd2e65bc0a662fc7c4
RHRC #679 = SUCCESS
Permansson #452 = SUCCESS
~~~

RHRC #679 passed the RHRC claim/regression suite, cutoff-free normalization lock, dictionary external-oracle guards, source normalization firewall, R004 scalar-shift audit, external-reference dependency rejection, CCM build, ExceptionalZero build and forbidden-placeholder rejection.

Permansson #452 passed its theorem build and placeholder/extra-axiom rejection.

Promoted theorem surfaces print only

~~~text
[propext, Classical.choice, Quot.sound]
~~~

with no sorryAx.

Codex review was unavailable because the review account reported its usage limit. This is absence of review evidence, not negative evidence.

## What became formally true

### PROVED — exact constrained subspace

`boundaryFlatSubspace N` is theoremized and

~~~text
u ∈ boundaryFlatSubspace N
  <-> BoundaryFlatCoefficients N u.
~~~

The project proposition remains canonical; the subspace is linear-algebra packaging.

### PROVED — exact moment shift and descending flag

~~~text
M_k(Du)=M_{k+1}(u).
~~~

For boundary-flat u:

~~~text
u    kills M0,M1,M2
Du   kills M0,M1
D²u  kills M0.
~~~

No theorem claims D preserves the full boundary-flat sector.

### PROVED — canonical Hermitianity

~~~text
canonicalSourceMatrix(L,N)ᴴ
  = canonicalSourceMatrix(L,N).
~~~

This is Hermitianity only, not positivity.

### PROVED — exact one-channel constrained displacement

For positive L and every v with M0(v)=0:

~~~text
[D,M]v
  = -1 * displacementPairing(L,N,v).
~~~

The scalar is the bilinear sum

~~~text
sum_i displacementVector(L,N,i) * v_i
~~~

with no conjugation.

For boundary-flat u the theorem is specialized to

~~~text
u
Du
D²u.
~~~

Thus the first three F1 Krylov commutators lie entirely in the all-ones forcing channel.

### PROVED — quadratic scaling

~~~text
quadraticForm A (c • u)
  = star(c) * c * quadraticForm A u.
~~~

### PROVED — normalized constrained negative witness

For every hypothetical off-line zero:

~~~text
exists L>0,N>=1,u,
  u != 0
  and u ∈ boundaryFlatSubspace N
  and ‖u‖=1
  and Re quadraticForm(canonicalSourceMatrix L N,u)<0.
~~~

The unit norm is the norm on the raw finite function type.

## What changed

Before #96 the project had two independent facts:

~~~text
F1 negative vector with M0=M1=M2=0
and
[D,M]=g1^T-1g^T.
~~~

The interaction was a LEAD.

After #96, Lean proves that the moment constraints consume the g*1^T side of the displacement on every zero-sum vector and force the first three F1 Krylov commutators into one distinguished channel.

The project can therefore stop treating the dangerous finite vector as an arbitrary negative direction. The next problem is the spectral geometry of a Hermitian canonical operator on an exact constrained sector.

## Upstream implications

### DERIVED — exact codimension should be three

For N>=1, the centered grid contains -1,0,+1. The restrictions of

~~~text
1
d
d²
~~~

to those coordinates form a nonsingular degree-2 Vandermonde system.

Therefore the three moment functionals should be linearly independent.

Expected:

~~~text
codim boundaryFlatSubspace N = 3
finrank boundaryFlatSubspace N = 2*N-2.
~~~

This is not yet theorem-locked.

### DERIVED — F1 mode floor should strengthen to N>=2

If N=1, exact codimension three in a three-dimensional ambient coefficient space would make the constrained sector zero.

#96 proves the dangerous vector is nonzero.

Therefore an off-line-zero witness should require N>=2.

This is DERIVED / OPEN FORMALIZATION.

### API simplification

Mathlib already supplies the intended finite spectral chassis:

~~~text
EuclideanSpace
Matrix.toEuclideanLin
finite-dimensional orthogonal projection
Analysis.InnerProductSpace.Rayleigh
~~~

The project should use that instead of building a bespoke minimizer framework.

## Downstream implications

### OPEN — Euclidean constrained transport

The current coefficient type is the raw function type

~~~text
Fin (2*N+1) -> ℂ.
~~~

The Rayleigh chassis lives naturally on

~~~text
EuclideanSpace ℂ (Fin (2*N+1))
= PiLp 2 (fun _ => ℂ).
~~~

The first downstream theorem package must bridge those carriers and preserve the moment equations and quadratic form.

### OPEN — constrained self-adjoint compression

After Euclidean transport, build the orthogonal compression of M to V₂.

Target:

~~~text
T_V self-adjoint
and
off-line zero -> negative Rayleigh direction for T_V.
~~~

### OPEN — negative constrained spectral mode

Use finite-dimensional Rayleigh theory to obtain

~~~text
T_V u = lambda u
lambda < 0
u != 0.
~~~

This is a constrained eigenvector, not automatically a full eigenvector of M.

### LEAD — KKT ambient residual

After exact codimension three:

~~~text
M u = lambda u + a0*1 + a1*d + a2*d².
~~~

This remains OPEN.

## Resurrected routes

### Parity/reversal — strengthened but still deferred

Parity becomes more useful after a constrained eigenmode exists. If a spectral mode can be chosen in a parity sector, additional odd-moment cancellation may extend the zero-sum Krylov chain.

No parity theorem was added by #96.

### Aperture flow / first singularity — still live

The canonical L-flow remains a plausible second-stage rigidity route, especially after a negative constrained eigenvalue is explicit.

Do not open it before the Euclidean constrained spectral object unless an independent positive anchor demands it.

### DR-010 — still dead

The exact D/M/g route is not the fitted small-commutator route.

#96 uses exact D, exact M, exact displacement and exact moment constraints. It does not infer eigenvector convergence from a small commutator or collapsing spectral gaps.

## New RH-relevant clues

### DERIVED / LEAD — 4×4 real Hankel Krylov block

Define

~~~text
H_ab = <D^a u, M D^b u>.
~~~

For 0<=a,b<=2, the #96 one-channel theorem gives

~~~text
[D,M]D^b u ∈ span{1},
~~~

while the moment flag gives

~~~text
D^a u ⟂ 1.
~~~

Using self-adjointness of D and M:

~~~text
H_(a+1,b)=H_(a,b+1).
~~~

Together with Hermitian symmetry, this implies at the mathematical level that the 4×4 block indexed by 0<=a,b<=3 should be real Hankel.

Status: DERIVED / OPEN FORMALIZATION.

Potential value:

- truncated moment formulations;
- Hankel determinant/minor constraints;
- Krylov/Lanczos structure;
- composition with a negative constrained eigenmode;
- parity extension of the moment chain.

This is not a positivity theorem.

### LEAD — compressed spectral obstruction may be the right finite wall

F1 only needs negativity on V₂. Therefore global PSD of M may be stronger than necessary.

A more focused terminal route is:

~~~text
off-line zero
  -> negative constrained eigenmode
  -> exact KKT + Krylov/Hankel + parity/arithmetic restrictions
  -> rule out the admissible negative compressed mode.
~~~

This is a research strategy, not a result.

## Falsification checks

- Real Hankel matrices can be indefinite.
- Low displacement rank does not imply positivity.
- One-channel commutator collapse does not imply positivity.
- D does not preserve V₂.
- Only M0,M1,M2 are known to vanish.
- A constrained eigenvector is not a full M eigenvector.
- The #96 norm-one witness is not a Euclidean Rayleigh-sphere theorem.
- Global canonical PSD would be RH-strength on the present route and must not be treated as a cheap finite lemma.
- Source-QW remains separate under OBS-015.
- Numerical agreement is not a theorem.

## Highest-leverage next moves

1. Add the Euclidean/PiLp₂ constrained carrier.
2. Prove exact codimension three.
3. Formalize the N>=2 witness strengthening.
4. Prove the raw quadratic-form / Euclidean inner-self identity.
5. Build the compressed self-adjoint canonical operator.
6. Prove a negative constrained eigenmode using Mathlib Rayleigh theory.
7. Theorem-lock or falsify the 4×4 Hankel/Krylov recurrence.
8. Only then choose between KKT/parity and aperture-flow as the next rigidity layer.

These moves maximize mathematical information gain because they turn an arbitrary negative direction into a canonical constrained spectral object before adding more arithmetic or symmetry machinery.

## Standing questions

### Given everything now formally true, what becomes possible that was not possible before?

The project can now formulate a genuine finite-dimensional self-adjoint constrained spectral problem around the exact F1 sector rather than around an arbitrary negative vector.

### If this contains a clue toward RH, where does it propagate?

Upstream into exact rank/codimension of the moment constraints; downstream into constrained Rayleigh/KKT structure; laterally into parity and aperture-flow; and structurally into the distinguished all-ones/Krylov-Hankel channels.

### What test most efficiently tells us whether the clue is real?

Formalize the Euclidean compressed negative eigenmode and then ask whether the #96 commutator/moment identities impose a non-generic restriction on that mode. If they do not, the route should pivot quickly to parity or aperture-flow rather than infer positivity from low-rank structure.

**RH remains OPEN.**
