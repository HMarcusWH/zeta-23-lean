# RHRC Control v2 — deterministic evidence-gated research routing + retroactive memory

> **Authority firewall:** Control v2 is a research-routing diagnostic. It cannot promote Lean theorems, write claim authority, emit the terminal RH answer, or turn numerical/search output into RH evidence. **RH remains OPEN.**

## Separate theorem and control anchors

```text
theorem-state anchor = PR #150 merge fb92d5749d6f7a65cfc9129d49d8213219c059db
validated theorem head = b1be9eca5f544d4356ea88089c0f7264f75d2220
validated theorem tree = 999ef44d44855cdffd5be5843e9f072867c0a7a8
RHRC #971 / run 34690959720 = SUCCESS
Permansson #744 / run 34690959699 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
```

PR #150 advances theorem authority. This post-#150 synchronization changes routing metadata and regression locks, not the controller's capability/authority model.

## Current routed frontier

```text
A4b0  kernel/source zero-shift transport                       PROVED / RETIRED
A4b1  absolute canonical source energy                         PROVED / #136 / RETIRED
A4b2a exact one-step determinant + sufficiency reduction       PROVED / #137
A4R0  aperture freedom                                         PROVED / #140
A4R1a fixed-cell same-witness persistence                      PROVED / #142
A4R1b analytic/log-cover/determinant regularity                PROVED / #144-#150
A4R1c cell-minimal regular first-bad selection                 PROVED / #150
A4b2r exact regular negative selected residual                 PROVED / #150
A4b2r independent selected-residual nonnegative sign           NOW
A4b2b universal one-step domination                            BROAD FALLBACK
GLOBAL first-bad exclusion                                     AFTER A4b2r OR independent domination
```

The completed `E4_A4_REGULAR_APERTURE_SELECTION` action is retired from the routable registry.

The selected stable action is now:

```text
E4_A4_REGULAR_SCHUR_ENERGY_SIGN
```

under frontier

```text
FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN.
```

## Why routing changed after #150

PR #150 closes all three former A4R first breaks:

1. assembled actual-production source/predecessor/lifted holomorphy;
2. determinant nonidentity plus open-interval actual predecessor regularity;
3. production cell-minimal regular first-bad selection and exact negative canonical source-channel endpoint.

Therefore keeping `E4_A4_REGULAR_APERTURE_SELECTION` selected would route back to completed theorem work.

The unresolved problem is now arithmetic:

```text
#150 forced state:
  regular predecessor
  unique A x0=b
  exact Ecanonical(c-x0)<0

missing independent theorem:
  Ecanonical(c-x0)>=0.
```

## Selected action — E4_A4_REGULAR_SCHUR_ENERGY_SIGN

The action is now staged through five first breaks:

1. retain/export the full #150 first-bad ancestry if the compressed outer endpoint loses hypotheses needed by arithmetic work;
2. reproduce/theoremize the exact pole integral and pole-minus-prime discrepancy identity;
3. theoremize boundary-flat Taylor annihilation and the resulting Riesz-smoothed discrepancy identities;
4. use interval-certified canonical calculations to falsify overbroad candidate sign mechanisms before long theorem work;
5. prove the independent scoped sign `Ecanonical(c-x0)>=0` on the exact forced state.

The first three are information-preserving reductions. They are not substitutes for the final sign theorem.

## Evidence-class firewall for the new arithmetic route

Current project labels:

```text
#150 regular selected negative-energy certificate     PROVED
A>0 from A>=0 + regular + Hermitian finite block       DERIVED unless packaged
pole/prime discrepancy identity                        EXTERNAL DERIVED
boundary-flat omega^7 / even omega^9 expansion         DERIVED
sixth/eighth-order Riesz smoothing                     DERIVED / LEAD
raw Loewner/Schur monotonicity failures                 EXPERIMENTAL SIGNAL
final selected-residual nonnegative sign                OPEN
```

Control v2 must not collapse these labels.

## Current negative controls

The regular-Schur action must remember:

- universal one-step domination is not a research reduction when obtained by restating successor positivity;
- generic shell/parity/KKT/displacement structure is insufficient without exact canonical source values;
- atomwise positive determinant/SOS is quarantined;
- loose independent channel majorants are conditioning-hostile;
- post-#150 numerical probes disfavor global aperture Loewner monotonicity, global minimizing-trial Schur monotonicity and universal positive atom energy;
- the `L*coth(L/2)` aperture coordinate and log-cover deck coordinate are distinct; no common-lattice identity is available without an explicit theorem.

## Universal domination fallback

`E4_A4_CANONICAL_ONE_STEP_DOMINATION` remains routable but deliberately demoted. It should become primary again only if a genuinely independent canonical arithmetic mechanism is found.

## Deterministic routing consequence

The base score formula is unchanged. The post-#150 action inputs make `E4_A4_REGULAR_SCHUR_ENERGY_SIGN` the highest-scoring admissible action under complete retro/first-break contracts.

This is routing metadata, not theorem evidence.

## CI expectations

`tools/run_suite.py` runs Control-v2 unit tests. The RHRC workflow real-history smoke run must assert:

- theorem anchor is #150;
- theorem merge/tree correspond to the exact validated #150 state;
- control anchor remains #117;
- frontier is `FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN`;
- selected action is `E4_A4_REGULAR_SCHUR_ENERGY_SIGN`;
- completed `E4_A4_REGULAR_APERTURE_SELECTION` is no longer routable;
- terminal claim remains `RH_OPEN`;
- controller theorem authority and terminal-claim mutation remain false.

Newest research implications:

`../RESEARCH_LEADS_POST_150_REGULARIZATION_CLOSED_ARITHMETIC_FRONTIER_DELTA.md`

**RH remains OPEN.**
