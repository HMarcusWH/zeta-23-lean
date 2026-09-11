# RHRC Control v2 — deterministic evidence-gated research routing + retroactive memory

> **Authority firewall:** Control v2 is a research-routing diagnostic. It cannot promote Lean theorems, write claim authority, emit the terminal RH answer, or turn numerical/search output into RH evidence. **RH remains OPEN.**

## Separate theorem and control anchors

```text
theorem-state anchor = PR #148 merge fcd301ae4c1b58196ff7fca18128243f1d35a87b
validated theorem head = 77c2d14511004ba380b080e08b4943b267ebd863
validated theorem tree = 91d537ee64b8f613bebdcf12110deba486276d35
RHRC #930 / run 34619665717 = SUCCESS
Permansson #703 / run 34619665725 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
```

PR #148 advances theorem authority. This post-#148 synchronization changes routing metadata, not the controller's capability/authority model.

## Current routed frontier

```text
A4b0  kernel/source zero-shift transport                       PROVED / RETIRED
A4b1  absolute canonical source energy                         PROVED / #136 / RETIRED
A4b2a exact one-step determinant + sufficiency reduction       PROVED / #137
A4R0  aperture freedom + regularity/frozen-source scaffold     PROVED / #140
A4R1a fixed-cell same-witness persistence                      PROVED / #142
A4R1b frozen/log-cover predecessor scaffold                    PROVED / #144
A4R1b scalar removable analyticity + production bridge         PROVED / #145-#146
A4R1b fixed-unit alpha/beta/gamma parameter holomorphy         PROVED / #148
A4R1b assembled source/predecessor holomorphy                  NOW
A4R1b determinant nonidentity + dense regularity               AFTER ASSEMBLY
A4R1c cell-minimal regular first-bad selection                 AFTER DENSITY
A4b2r regular minimizing-trial Schur-energy sign               AFTER A4R1c
A4b2b universal one-step domination                            BROAD FALLBACK
GLOBAL first-bad exclusion                                     AFTER A4b2r OR independent domination
```

The stable controller action ID remains `E4_A4_REGULAR_APERTURE_SELECTION`. The action ID still names the same route; only its first-break specification has moved forward as theorem prerequisites closed.

## Why routing changed after #148

PR #148 proves genuine complex parameter holomorphy of the exact fixed-unit archimedean cores:

```text
complexAlphaCore
complexBetaCore
complexGammaCore
```

on the connected strip `|Im z|<pi`, together with strip-wide analyticity of `complexRegularizedArchScale` and zero-freeness of the divided sinh denominator there.

Therefore the old FB-01 "prove fixed-unit parameter-integral holomorphy" is complete.

The remaining analytic work is now assembly on one common production source domain:

```text
scalar branch control
+ pole denominator zero-freeness
+ elementary/frozen prime-source analyticity
+ #148 arch-core holomorphy
-> complexFrozenCanonicalSourceRemainder holomorphy
-> complexFrozenIntrinsicPredecessorRemainder holomorphy
-> lifted predecessor holomorphy on a connected cover domain.
```

No successor positivity, determinant sign, regular Schur sign, negative-root exclusion, or RH premise may be assumed.

## Selected action — E4_A4_REGULAR_APERTURE_SELECTION

The active theorem attempt has three sequential first breaks:

1. assemble the exact frozen source/predecessor and lifted predecessor into genuine holomorphic families on one common domain;
2. prove the relevant determinant is not identically zero and derive dense regular apertures, splitting off the zero-dimensional predecessor case;
3. production-package the cell-minimal bad-size selection and intersect dense regularity with the #142 persistent-negative open set.

The first break should aggressively test the scalar right-half-plane lead on the punctured arch strip, because that could put the production principal log on the same domain as the #148 arch cores.

## Translation/deck-law negative control

The exact #144 deck identity is not an analyticity theorem. The reusable countermodel remains

```text
F(z) = -z + Re z.
```

It has the relevant affine imaginary-translation behavior while being nonholomorphic. Translation/deck structure alone cannot discharge FB-01.

## Cell-minimal selection

The preferred derived selection remains:

```text
K* = min { K | exists L in I_Q, AnyParityBad L K }.
```

Every smaller size is good in both parities throughout the cell. This quantifier order is essential: taking a first bad size at one aperture and then moving the aperture would not preserve predecessor nonnegativity.

#142 preserves one selected bad witness on an open `J`. Dense regularity only needs to hit that `J` at predecessor size `N*=K*-1`.

## Determinant nonidentity lead

Once lifted predecessor holomorphy is available, use the exact deck law

```text
Ahat(z+2*pi*i) = Ahat(z) - (2*pi*i) I.
```

If `det Ahat` were identically zero, one fixed finite operator would be forced to admit too many distinct scalar shifts as eigenvalues. The intended proof is a finite characteristic-polynomial root count.

This is still a **LEAD / HYPOTHESIS** until Lean proves it. Holomorphy and nonidentity are separate obligations.

## Next action — E4_A4_REGULAR_SCHUR_ENERGY_SIGN

After the production regular cell-minimal first-bad state is theorem-backed, use the existing unique-preimage interface

```text
A x0 = b.
```

The intended forced countercertificate is

```text
Ecanonical(c-x0)=Re S0<0.
```

The closing sign target remains

```text
Ecanonical(c-x0)>=0.
```

A potentially narrower certificate than universal domination is `q_c>=0` plus `Delta(x0)>=0`, but only after theoremizing that the zero-shift coupling is real and handling the `q_A(x0)=0` case. This is not yet a proved reduction.

## Universal domination fallback

`E4_A4_CANONICAL_ONE_STEP_DOMINATION` remains routable but deliberately demoted. It should become primary again only if a genuinely independent canonical arithmetic mechanism is found.

## Deterministic routing consequence

The base score formula is unchanged. The action inputs now encode the post-#148 state:

- regular-aperture selection remains selected;
- fixed-unit archimedean parameter holomorphy is closed;
- FB-01 is assembled source/predecessor/lifted holomorphy;
- FB-02 is determinant nonidentity/dense regularity;
- FB-03 is production cell-minimal composition;
- regular Schur sign remains explicit but carries dependency debt until regular selection closes;
- universal domination remains admissible but is not selected merely because it would close the route if proved.

This is routing metadata, not theorem evidence.

## CI expectations

`tools/run_suite.py` runs Control-v2 unit tests. The RHRC workflow real-history smoke run must assert:

- theorem anchor is #148;
- theorem merge/tree correspond to the exact validated #148 state;
- control anchor remains #117;
- frontier remains `FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_APERTURE_SELECTION`;
- selected action remains `E4_A4_REGULAR_APERTURE_SELECTION`;
- terminal claim remains `RH_OPEN`;
- controller theorem authority and terminal-claim mutation remain false.

Newest research implications:

`../RESEARCH_LEADS_POST_148_PARAMETER_HOLOMORPHY_GREEN_DELTA.md`

**RH remains OPEN.**
