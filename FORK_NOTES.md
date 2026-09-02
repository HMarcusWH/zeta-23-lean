# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

~~~text
theorem-state anchor = PR #96 merge 3712746a144d630ee41b89527b098e392822f2c6
theorem tree = 1d43b31bf9750375189a1ccd2e65bc0a662fc7c4
theorem-bearing merged through = PR #96
live GitHub main = authoritative
RH = OPEN
~~~

## Recent permanent theorem packages

~~~text
#89 WCONT-A quantitative genuine-W continuity
#91 F0-B1C-A raw uniform localized C² approximation
#93 F0-B1C-B legal boundary-flat WCONT approximation
#94 strict finite sign transfer + F1 canonical finite negative obstruction
#96 constrained canonical finite-wall package
~~~

## What #96 closed

PR #96 turns the post-F1 moment/displacement observations into production finite linear algebra.

PROVED:

~~~text
boundaryFlatSubspace N
  = exact linear packaging of M0=M1=M2=0

M_k(Du) = M_{k+1}(u)

u    -> M0=M1=M2=0
Du   -> M0=M1=0
D²u  -> M0=0

canonicalSourceMatrixᴴ = canonicalSourceMatrix

[D,M]v = -1 * displacementPairing(v)
for every zero-moment v
~~~

The collapse is specialized to u, Du and D²u for every boundary-flat u.

PR #96 also proves that any hypothetical off-line zero forces a nonzero, norm-one vector in `boundaryFlatSubspace N` with strictly negative canonical quadratic value.

## Exact #96 authority

~~~text
head = d628b7332e908701e85ef8ea33309e2bf548f2e5
synthetic merge = 5830d75ec649f065925f5f3a1a7c823d8a5b42b9
merge = 3712746a144d630ee41b89527b098e392822f2c6
tree = 1d43b31bf9750375189a1ccd2e65bc0a662fc7c4
RHRC #679 = SUCCESS
Permansson #452 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
~~~

## Current primary frontier

~~~text
Euclidean/PiLp₂ transport of the constrained sector
  -> exact codim(V₂)=3 and F1 witness N>=2
  -> compressed self-adjoint canonical operator
  -> negative constrained spectral mode
  -> KKT / Krylov-Hankel rigidity
  -> parity or aperture-flow only as demanded by the obstruction
~~~

The current `‖u‖=1` theorem uses the raw function-space norm. Do not feed it directly into Hilbert/Rayleigh APIs; the Euclidean bridge is a separate theorem obligation.

## Post-#96 structural clue

With D=indexMatrix N and M=canonicalSourceMatrix L N, the exact commutator on the first F1 Krylov vectors lands in the all-ones channel, while u,Du,D²u have zero coefficient sum.

DERIVED / OPEN TO FORMALIZATION:

~~~text
H_ab = <D^a u, M D^b u>, 0<=a,b<=3
~~~

should form a real Hankel 4×4 block.

This is not positivity. It is a candidate rigidity structure to compose with the future constrained eigenmode.

## Canonical finite object

~~~text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix.

legacyPrintedMatrix = finiteMatrix.
~~~

Sign-sensitive finite claims must use `canonicalSourceMatrix`.

## Dead-route clarification

DR-010 remains falsified. #96 uses the exact analytic D and exact canonical commutator, not a fitted small-commutator generator or spectral-gap heuristic.

**RH remains OPEN.**
