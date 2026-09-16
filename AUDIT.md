# RHRC formal audit — theorem authority through PR #184; research evidence through PR #193

> **RH remains OPEN.**

Live GitHub head + exact compiler/CI evidence outrank this prose.

## Authority split

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

## Formal theorem state

No Lean theorem has been added after PR #184. The formal production-facing package still proves, in its exact scopes:

```text
Hermitian P = d - |b|^2/a
contact-local determinant/pivot derivative orientation transfer under H1
full frozen parity production family M~(t) = -t I + R~(t)
exact fixed-cell bridge to parityCompressedCanonical
N2 predecessor/canonical-shell reconstruction
canonical shell != 0
predecessor ⟂ shell
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0
```

Still not proved: source-specific remainder domination, contact existence/uniqueness, opposing first-bad orientation on the same state, first-bad exclusion, negative-root exclusion or RH.

## Research audit: #186 -> #193

### #186 -> #190 — ambient selector surface consumed

#186 returned `DOMINATION_SIGNAL_MIXED`. #188 froze the normalization-safe selector surface. #189 showed every selector individually ambiently separable from the target sign. #190 then certified the exact reflected pair with identical complete seven-vector and identical nonboundary threshold signature but opposite target signs:

```text
JOINT_EXACT_VECTOR_SEPARABLE
JOINT_THRESHOLD_SIGNATURE_SEPARABLE
```

Thus all 127 nonempty selector subsets are insufficient in that ambient algebra.

### #192 — canonical production realizability ladder

The historical Layer 0 -> Layer 5 canonical production realizability audit was executed rather than remaining a future plan:

```text
Layer 0  AMBIENT_NORMALIZED
Layer 1  SOURCE_CHANNEL_COUPLING
Layer 2  SCALAR_APERTURE
Layer 3  COMMON_ARCH_APERTURE
Layer 4  COMMON_SCHUR_GEOMETRY
Layer 5  CANONICAL_PRODUCTION
```

The specific #190 negative-scalar witness is excluded when the exact positive scalar-aperture identity is imposed. An adversarial exact positive-scalar reflected construction shows that scalar positivity alone does not kill the general reflection mechanism. The bounded full canonical replay remains `UNRESOLVED` for general twin existence; among the six primary production states it reports 0/15 seven-vector overlaps. Search failure is not nonexistence.

### #193 — parity trajectory rigidity

PR #193 reuses the fixed-Q Q14 trajectory and the inherited P1/P2 graph. It defines only the equivalent orientation quantity

```text
J = o'e - e'o
P2 = L*J/(o*e)
sign(P1') = sign(P2) = sign(J)   under L,e,o>0
```

All six exact inherited primary centers certify:

```text
e > 0
o > 0
J > 0
P2 > 0
```

But the frozen finite-width cover reports:

```text
96 evaluated cells
63 H1_UNRESOLVED
33 J_UNRESOLVED after H1 recovery
0 J_NEGATIVE
0 J_POSITIVE
TRAJECTORY_RIGIDITY_UNRESOLVED
```

The whole inherited Q14 hull therefore remains unresolved. This does **not** locate a fold and does **not** falsify trajectory monotonicity. It identifies insufficiency of the current first-order centered enclosure representation/budget to certify neighborhood orientation.

## Current post-green frontier

Do not repeat #192 and do not simply turn up #193 depth/precision on the identical graph. On the **same frozen Q14 hull**, compare a sharper finite-width representation:

```text
A. first-order Wronskian enclosure        [#193 baseline]
B. direct P2 log-slope enclosure
C. centered second-order/Taylor enclosure
```

The bounded research target is `J(L)>0` throughout that inherited hull. Six positive centers are only a structural signal; they are not hull positivity.

If a complete signed cover eventually certifies `J>0`, then bounded strict monotonicity of P1 follows and distinct apertures on that branch cannot share the complete seven-vector. That consequence is research-level until separately formalized.

## Claim firewall

```text
#184 theorem package
  -/-> source-specific sign law

#190 joint ambient separability
  -/-> canonical arithmetic separability

#192 specific-witness exclusion
  -/-> general reflected-class exclusion

6/6 positive #193 centers
  -/-> J>0 on the hull

first-order enclosure failure
  -/-> trajectory monotonicity failure
```

Global Schur monotonicity remains quarantined. Negative-root exclusion remains OPEN. The terminal zeta/Mathlib seam remains OPEN. **RH remains OPEN.**
