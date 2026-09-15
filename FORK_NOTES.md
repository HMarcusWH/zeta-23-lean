# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

```text
THEOREM AUTHORITY
PR #184
head  = a756494ebe7e2530715e996b9a9a341fbe07c683
merge = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e
tree  = 6c77cd470809959a403b3bcc5f08d39f4076fa4c

LATEST RESEARCH EVIDENCE
PR #190
head  = 8701920b0da18ae6595ad0eee55c1f6cb291a94f
merge = f87da9fde71dd1e74419c6ae5848eee3787c27e4
tree  = af8774b65c898de221a5bf32977ccff3407a7b2d
RHRC #1096 = SUCCESS
Permansson #869 = SUCCESS

CONTROL SEMANTIC AUTHORITY
PR #117
selected first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

## Theorem package remains #184

Lean theorem authority still ends at the complex-Hermitian/log-cover package:

```text
P = d - |b|^2/a
M~(t) = -t I + R~(t)
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0
```

with exact fixed-cell attachment to production and N2 predecessor/canonical-shell reconstruction plus orthogonality. The arithmetic premise needed for the sign step remains open.

## Research progression after #184

```text
#186  broad remainder domination -> DOMINATION_SIGNAL_MIXED
#188  frozen normalization-safe selector audit
#189  every individual frozen selector abstractly separable from target sign
#190  complete seven-selector vector jointly separable from target sign
```

#190 certifies an exact ambient pair with the same full strong vector and same nonboundary threshold signature but opposite target signs. Therefore every nonempty subset of the seven frozen strong observables is also insufficient inside that ambient normalized algebra.

This does not establish canonical arithmetic realizability of either reflected state.

## Current route

Do not continue mining Boolean/threshold combinations of the same seven observables. The live bottleneck is now the image of the actual production map inside the larger normalized state space.

A concrete clue comes from the current production derivative decomposition:

```text
scalar_shift = 2*cCorrection'(L) I
arch_signed  = -arch_direct - scalar_shift
```

so `arch_signed` and `scalar_shift` are coupled by construction and arise at the same aperture. #190's abstract reflection deliberately treats the hidden scalar coordinate as independently variable while holding the observed arch coordinate fixed.

The next research PR should progressively impose production constraints on the #190 twin and identify the first exact relation that destroys it. If no such relation appears before full canonical reconstruction, Pair A should be downgraded rather than rescued with another fitted selector.

## Permanent warnings

- theorem authority remains #184;
- research authority advances to #190 only as executable research evidence;
- #186 killed broad domination, not #184;
- #190 killed selector composition only in its declared ambient algebra;
- production realizability is still OPEN;
- finite-width H1 remains separate;
- global Schur monotonicity remains quarantined;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**