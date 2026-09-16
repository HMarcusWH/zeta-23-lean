# Post-#193 research delta — Q14 parity-trajectory frontier

> **Claim firewall: RH remains OPEN.**
>
> This is the required post-green research pass after merged research PR #193. It distinguishes Lean theorem authority, rigorous finite research, derived consequences, leads and open obligations.

## Authority snapshot

```text
THEOREM AUTHORITY
latest theorem-bearing PR = #184
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

CONTROL AUTHORITY
PR #117
selected first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

# What became formally true

**PROVED:** nothing new in Lean after #184.

The exact theorem state remains the #184 complex-Hermitian production/log-cover Schur package, including the fixed-cell production bridge, N2 predecessor/canonical-shell reconstruction and orthogonality, and the conditional identity/sign interface

```text
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0.
```

PR #192 and PR #193 are research-only. They do not promote theorem authority, close FB-05, exclude negative roots, or prove RH.

# What became research-certified

## PR #192 — canonical production realizability

The formerly planned Layer 0 -> Layer 5 audit is now executed research history:

```text
Layer 0  AMBIENT_NORMALIZED
Layer 1  SOURCE_CHANNEL_COUPLING
Layer 2  SCALAR_APERTURE
Layer 3  COMMON_ARCH_APERTURE
Layer 4  COMMON_SCHUR_GEOMETRY
Layer 5  CANONICAL_PRODUCTION
```

Research-certified conclusions:

- the exact #190 negative-scalar reflected witness is `EXACT_TWIN_EXCLUDED_BY_IDENTITY` once the actual positive scalar-aperture law is imposed;
- an exact adversarial reflected construction using positive scalar-law values is `EXACT_TWIN_SURVIVES` at that identity layer;
- bounded later production layers remain `UNRESOLVED` for general reflected-twin existence;
- the six inherited primary production states give 0/15 seven-vector overlaps, a bounded structural signal only.

## PR #193 — parity trajectory rigidity

PR #193 reuses the inherited P1/P2 selectors and evaluates the derived orientation graph

```text
J = o'e - e'o.
```

At all six inherited exact primary centers the Arb point evaluation certifies:

```text
e > 0
o > 0
J > 0
P2 > 0
```

The finite-width first-order centered cover evaluates 96 cells and returns:

```text
63 H1_UNRESOLVED
33 J_UNRESOLVED after H1 recovery
0 J_NEGATIVE
0 J_POSITIVE
TRAJECTORY_RIGIDITY_UNRESOLVED
```

The whole frozen Q14 hull therefore remains unresolved at finite width. #193 did not find a fold.

# What changed

Before #192 the central question was whether the #190 ambient reflected twin survived progressively more canonical production structure. #192 answered that for the specific witness and showed why scalar positivity alone does not close the reflected class.

Before #193 trajectory rigidity was a fallback lead. #193 makes it the active bottleneck. The key new pattern is:

```text
uniformly positive exact-center orientation
+
no signed finite-width cells under the first-order graph
```

That moves the problem from pointwise realizability to rigorous neighborhood propagation.

The correct interpretation is narrower than monotonicity and stronger than a generic numerical failure:

> the current first-order centered parity-trajectory enclosure is dependency-limited on the frozen Q14 hull.

# Upstream implications

The #193 graph shows that no new selector is required to express the relevant local orientation. The inherited quantities already satisfy the derived identities

```text
J = o'e - e'o,
P2 = L*J/(o*e),
```

and, under `L,e,o>0`,

```text
sign(P1') = sign(P2) = sign(J).
```

**DERIVED:** the next abstraction should therefore target a sharper enclosure of an already-existing invariant/ratio rather than a larger selector vocabulary.

Upstream objects worth revisiting:

- the centered H1 recovery graph from #180/#181 ancestry;
- higher derivative / second-order bounds already available in the fixed-Q derivative backend;
- ratio/log-derivative formulations that may reduce `o'e-e'o` interval dependency;
- exact normalization relationships that let P2 be enclosed directly without separately multiplying four dependent interval factors.

The production definition itself should not be widened: same Q, same N/K, same parity, same six inherited centers and same hull remain the comparison domain.

# Downstream implications

If a complete finite-width cover certifies

```text
J(L) > 0
```

throughout the frozen Q14 hull, then on that bounded branch and under the already checked positivity prerequisites:

```text
P2 > 0
P1' > 0
P1 strictly monotone
```

**DERIVED:** distinct apertures on that bounded branch cannot share the same P1, and hence cannot share the complete seven-vector.

That would eliminate the distinct-aperture reflected-twin mechanism on this bounded canonical branch without adding selector #11 or fitting a threshold.

This would still be research-level finite evidence. A theorem-level use in FB-05 would require a separately formalized exact statement attached to the same retained/contact state.

# Resurrected routes

The following earlier machinery is newly relevant because #193 localized the obstruction to finite-width representation:

- centered H1 / mean-value recovery;
- second derivative bounds;
- local Taylor models;
- interval Newton / Krawczyk-style localization where an actual zero question arises;
- direct log-slope/ratio enclosures instead of expanded Wronskian products.

These were not sufficient reasons to run another experiment before the canonical path was known. After #192/#193 they are now attached to a concrete same-hull orientation question.

Still dead or consumed:

- selector subset mining over G1/P1/P2/C1-C4;
- threshold refits on the six-state panel;
- repeating the Layer 0 -> Layer 5 realizability ladder;
- blind depth/precision increases on the unchanged first-order #193 graph.

# New RH-relevant clues

**LEAD / HYPOTHESIS:** `J(L)>0` may hold throughout the frozen Q14 primary hull.

Why it is interesting:

- all six exact inherited centers independently have positive J/P2 orientation;
- no evaluated finite-width cell certifies negative J;
- the failure mode is loss of enclosure sign rather than observed exact-center sign reversal;
- strict P1 monotonicity would give a canonical aperture fingerprint on the bounded branch and remove a class of same-observation twins.

A second clue is representational:

**LEAD / HYPOTHESIS:** direct enclosure of `P2 = L(o'/o-e'/e)` or a centered second-order form may preserve dependency substantially better than the expanded first-order Wronskian `o'e-e'o`.

Neither clue is a theorem.

# Falsification checks

Fastest adversarial tests:

1. **Boundary check:** evaluate whether J can approach or cross zero near hull endpoints even though inherited centers are positive.
2. **Dependency check:** run the identical cells through direct P2/log-slope and second-order centered graphs; if all representations wrap zero at the same places, the problem may be mathematical rather than representational.
3. **Normalization check:** verify sign conclusions are invariant under the frozen parity normalizations used by P1/P2.
4. **H1 check:** ensure any ratio or Schur interpretation is applied only where the needed positivity/nonzero prerequisites are certified.
5. **No-label check:** target sign and post-hoc classification labels must remain unavailable to the enclosure selection.
6. **Same-domain check:** no Q/N/parity expansion, center movement or hull shrinkage is allowed merely to obtain a sign.
7. **Point-vs-neighborhood check:** do not infer a cover from 6/6 positive centers.
8. **Analog-system check:** verify the same enclosure method does not mechanically manufacture monotonicity in synthetic controls with known folds.
9. **Circularity check:** a P2-based enclosure may use the inherited P2 graph, but it may not assume the monotonicity it is intended to establish.
10. **Finite/global check:** even a successful Q14 hull certificate is not arbitrary-Q or global first-bad closure.

# Highest-leverage next moves

1. Freeze the exact #193 hull and inherited center schedule as the comparison domain.
2. Implement a direct P2/log-slope enclosure with the same inputs and no target labels.
3. Implement a centered second-order/Taylor enclosure using available derivative bounds.
4. Compare both against the #193 first-order Wronskian baseline cell-by-cell.
5. Require an explicit complete signed cover before reporting bounded monotonicity.
6. If one representation succeeds, isolate why its dependency graph is tighter and seek the smallest theorem-level identity behind that gain.
7. If all fail, distinguish genuine near-zero trajectory behavior from remaining interval dependency before changing mathematical route.

The next intended research PR is therefore:

```text
R003: sharpen positive Q14 parity-trajectory enclosure after #193
```

# Standing questions

> Given everything that is now formally true, what becomes possible that was not possible before?

We can stop asking whether the specific #190 twin survives the first obvious canonical production identities and instead study whether the actual canonical one-dimensional aperture trajectory is locally injective through an inherited observable.

> If this contains a clue toward RH, where does that clue propagate upstream or downstream through the existing mathematics?

Upstream it points to dependency-reduced derivative/ratio representations. Downstream it could remove the distinct-aperture same-seven-vector mechanism needed to evade the current FB-05 observation surface, after which the remaining task is to attach the restriction to the exact retained/contact state.

> What experiment, lemma, reformulation, or connection would most efficiently tell us whether that clue is real?

Compare first-order J, direct P2 log-slope and centered second-order/Taylor enclosures on the identical frozen Q14 hull and demand a complete signed cover. That maximizes information gain while keeping the population, selectors and claim surface fixed.

## Open

`J>0` on the hull, arbitrary-Q trajectory rigidity, FB-05, negative-root exclusion and RH are all OPEN.
