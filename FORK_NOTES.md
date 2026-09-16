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
PR #193
head  = 085634ca7dafe4d9f598b2b5e081be80e050ba8c
merge = fdd6606f85e92bf632b4cdaf1d4af85f6fa5b195
tree  = db569150046459f4b87a931d3e8d01054bbbedff
RHRC #1109 = SUCCESS
Permansson #882 = SUCCESS
post-190 canonical realizability audit #5 = SUCCESS
post-192 parity trajectory rigidity #3 = SUCCESS

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
#192  Layer 0 -> Layer 5 canonical production realizability audit executed
#193  fixed-Q Q14 parity-trajectory rigidity audit -> TRAJECTORY_RIGIDITY_UNRESOLVED
```

#192 excludes the specific negative-scalar #190 witness once the exact scalar-aperture identity is imposed, but an adversarial positive-scalar reflected pair survives that identity and the bounded canonical replay does not prove general nonexistence. Among the six primary production states, the replay has 0/15 seven-vector overlaps; that is a bounded structural signal only.

#193 then evaluates the inherited parity trajectory using

```text
J = o'e - e'o
P2 = L*J/(o*e)
```

and certifies `e>0`, `o>0`, `J>0`, `P2>0` at all six exact inherited centers. Its finite-width cover nevertheless returns 63 `H1_UNRESOLVED`, 33 `J_UNRESOLVED`, no signed J cells, and overall `TRAJECTORY_RIGIDITY_UNRESOLVED`.

## Current route

The canonical production realizability ladder is completed research history, not the next experiment. The live bottleneck is neighborhood propagation of the positive exact-center trajectory orientation.

Do not resume selector mining, repeat the #192 replay, or merely raise the #193 subdivision/precision budget. On the **same frozen Q14 hull**, compare:

```text
#193 first-order Wronskian enclosure
vs direct P2 log-slope enclosure
vs centered second-order/Taylor enclosure
```

The research question is whether one of those sharper representations can rigorously certify `J(L)>0` throughout the inherited hull. Six positive centers are not a monotonicity theorem.

## Permanent warnings

- theorem authority remains #184;
- research authority advances through #193 only as executable/finite research evidence;
- #190 killed selector composition only in its declared ambient algebra;
- #192 killed the specific reflected witness, not the general reflected class;
- #193 did not find a fold;
- first-order finite-width nonresolution does not falsify monotonicity;
- `J>0` on the Q14 hull remains OPEN;
- finite-width H1 remains separate;
- global Schur monotonicity remains quarantined;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**
