# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

Live GitHub head + exact compiler/CI evidence are authoritative dynamically.

```text
THEOREM AUTHORITY
latest theorem-bearing PR = #184
validated theorem head = a756494ebe7e2530715e996b9a9a341fbe07c683
merged theorem commit = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e
validated theorem tree = 6c77cd470809959a403b3bcc5f08d39f4076fa4c

LATEST RESEARCH-EVIDENCE ANCHOR
merged research PR = #193
validated research head = 085634ca7dafe4d9f598b2b5e081be80e050ba8c
merged research commit = fdd6606f85e92bf632b4cdaf1d4af85f6fa5b195
validated research tree = db569150046459f4b87a931d3e8d01054bbbedff
RHRC run #1109 = SUCCESS
Permansson run #882 = SUCCESS
post-190 canonical realizability audit #5 = SUCCESS
post-192 parity trajectory rigidity #3 = SUCCESS
research disposition = TRAJECTORY_RIGIDITY_UNRESOLVED

CONTROL SEMANTIC AUTHORITY
PR #117 merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
selected first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

The theorem, research and control anchors are intentionally separate. Research green is not theorem promotion.

## Theorem frontier

The compiler-validated theorem ladder remains through PR #184. Lean proves the complex-Hermitian 2x2 Schur calculus, the frozen production family on the logarithmic cover, the exact fixed-cell bridge to `parityCompressedCanonical`, N2 predecessor/canonical-shell reconstruction and orthogonality, and

```text
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0.
```

PR #184 does **not** prove source-specific remainder domination, contact existence/uniqueness, an opposing first-bad orientation, negative-root exclusion or RH.

## Completed research history

```text
#186  broad production-remainder domination on the frozen Q14 panel
      -> DOMINATION_SIGNAL_MIXED

#188  frozen normalization-safe selector audit

#189  every individual frozen selector
      -> exact ambient semantic separability from target sign

#190  complete seven-dimensional strong selector vector
      -> JOINT_EXACT_VECTOR_SEPARABLE
      -> JOINT_THRESHOLD_SIGNATURE_SEPARABLE
      -> all 127 nonempty subsets also insufficient in ambient algebra

#192  Layer 0 -> Layer 5 canonical production realizability audit
      -> specific negative-scalar #190 witness excluded by exact scalar-aperture identity
      -> adversarial positive-scalar reflected construction survives that identity
      -> full six-primary production replay has 0/15 seven-vector overlaps
      -> general reflected-twin mechanism remains UNRESOLVED

#193  fixed-Q Q14 parity-trajectory rigidity audit
      -> J = o'e - e'o is an equivalent orientation graph for inherited P1/P2
      -> 6/6 exact inherited centers: e>0, o>0, J>0, P2>0
      -> 96 finite-width evaluated cells:
           63 H1_UNRESOLVED
           33 J_UNRESOLVED after H1 recovery
            0 J_NEGATIVE
            0 J_POSITIVE
      -> TRAJECTORY_RIGIDITY_UNRESOLVED
```

The post-#190 canonical-realizability vocabulary remains part of the completed history because it is a real consumed research layer and is regression-locked. It is no longer the active frontier.

## Current active path — FB-05 / canonical trajectory rigidity

PR #193 did **not** locate a fold. It exposed a finite-width representation bottleneck despite uniformly positive exact-center orientation.

Do not:

```text
resume selector mining or threshold refits
repeat the #192 Layer 0 -> Layer 5 production replay
merely increase #193 subdivision/precision on the same first-order graph
infer J>0 on the hull from six positive centers
```

The next research target is the exact same frozen Q14 primary hull, with the same inherited Q/N/K/parity state and no target labels, but a sharper neighborhood representation. Compare:

```text
A. #193 first-order Wronskian enclosure
B. direct P2 log-slope enclosure
C. centered second-order / Taylor enclosure
```

The finite research goal is:

```text
J(L) > 0 throughout the frozen Q14 hull
```

If rigorously certified on that bounded branch, then under `L,e,o>0`:

```text
P2 = L*J/(o*e)
sign(P1') = sign(P2) = sign(J)
J>0 -> P1' > 0
```

so distinct apertures on that bounded canonical branch cannot share the same `P1`, and therefore cannot share the complete seven-vector. This remains research-level finite evidence until separately theoremized.

## Current open obligations

```text
higher-order centered Q14 parity-trajectory enclosure                    OPEN / ACTIVE
J(L) > 0 on the full inherited Q14 hull                                 OPEN
actual N2 production remainder scalar derivative witnesses              OPEN
actual production HasDerivAt Schur identity                              OPEN
same-state first-bad opposing contact orientation                        OPEN
centered finite-width H1 / q13 whole-cell contact classification         OPEN
sourceMoment <-> M4 canonical-state rigidity                              OPEN
simultaneous even/odd bad exclusion                                       OPEN
odd-selected first-bad branch closure                                     OPEN
negative-root exclusion                                                    OPEN
outside-strip/trivial-zero terminal seam                                  OPEN
RiemannHypothesis                                                          OPEN
```

## Permanent firewalls

- compiler/CI evidence outranks prose;
- theorem authority remains #184 until a later Lean-bearing PR passes the theorem gates;
- #190 closes the frozen selector surface only in its declared ambient normalized algebra;
- #192 excludes the specific #190 witness but not the general reflected class;
- #193 exact-center positivity is not finite-width monotonicity;
- `TRAJECTORY_RIGIDITY_UNRESOLVED` is not evidence that a fold exists;
- another depth/precision increase on the identical first-order graph is not a new mechanism;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**

See `research/RHRC/CURRENT_RESEARCH_PLAN.md`, `research/RHRC/RESEARCH_LEADS.md`, `research/RHRC/FB05_INCOMPATIBILITY_PROGRAM.md`, and `research/RHRC/RESEARCH_LEADS_POST_193_PARITY_TRAJECTORY_DELTA.md` for the current execution route.
