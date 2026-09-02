# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

~~~text
main = 8b54a72767c2703351990e2a67354511e9c9b83a
tree = 0fca10d1904d85bd33763cc6728e22c1c5b9ef5d
merged through = PR #94
RH = OPEN
~~~

## Recent permanent theorem packages

~~~text
#88 F0-B1B exact boundary-flat projection
#89 WCONT-A quantitative genuine-W continuity
#91 F0-B1C-A raw uniform localized C² approximation
#93 F0-B1C-B legal boundary-flat WCONT approximation
#94 strict finite sign transfer + F1 canonical finite negative obstruction
~~~

## Canonical finite object

~~~text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix.

legacyPrintedMatrix = finiteMatrix.
~~~

Sign-sensitive finite claims must use `canonicalSourceMatrix`.

## What #93 closed

`Zeta23.CCM.exists_boundaryFlatFinite_WCONT_approx` constructs legal boundary-flat finite hard-window vectors arbitrarily close to any strict-collar C² target in exactly the two L1 quantities consumed by WCONT-A.

OBS-016 remains a general firewall, but its primary-route escape is now proved.

## What #94 closed

PR #94 proves strict finite sign transfer and F1:

~~~text
off-line zero
  -> exists L>0,N>=1,u,
       M0(u)=M1(u)=M2(u)=0
       and Re quadraticForm(canonicalSourceMatrix L N) u < 0.
~~~

The approximation/legalization/sign-transfer phase is closed on the primary internal route.

## Current primary frontier

~~~text
K0-F1 constrained canonical sector
  -> constrained compression / negative minimizer
  -> exact displacement rigidity
  -> aperture-flow / crossing only if required.
~~~

The pre-F1 parity-first order is no longer binding because F1 supplies three exact moment annihilations on the dangerous vector.

## Structural clue

With D=indexMatrix N and M=canonicalSourceMatrix L N,

~~~text
[D,M] = g 1^T - 1 g^T
~~~

is PROVED, while

~~~text
1^T u = 0
1^T D u = 0
1^T D^2 u = 0
~~~

is DERIVED for an F1 witness. Exact collapse is not yet separately formalized.

## Dead-route clarification

DR-010 remains falsified. K0-F1 uses the exact analytic D and exact canonical commutator, not a fitted small-commutator generator or spectral-gap heuristic.

**RH remains OPEN.**
