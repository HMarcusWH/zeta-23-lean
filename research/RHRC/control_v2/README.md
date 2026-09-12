# RHRC Control v2 — deterministic evidence-gated research routing + retroactive memory

> **Authority firewall:** Control v2 is a research-routing diagnostic. It cannot promote Lean theorems, write claim authority, emit the terminal RH answer, or turn numerical/search output into RH evidence. **RH remains OPEN.**

## Separate theorem and control anchors

```text
theorem-state anchor = PR #153 merge 474a88d76ecd2f4eee6178685b2e8d8b104171ca
validated theorem head = b6622dadab911008c0a7238e9dc711c6f9946302
validated theorem tree = dd69f1c612047f2d2f15a7ba158664634284b42e
RHRC #994 / run 34709905190 = SUCCESS
Permansson #767 / run 34709905198 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
```

PR #153 advances theorem authority. This synchronization changes routing metadata and regression locks, not the controller's capability/authority model.

## Current routed frontier

```text
A4b0  kernel/source zero-shift transport                       PROVED / RETIRED
A4b1  absolute canonical source energy                         PROVED / #136 / RETIRED
A4b2a exact one-step determinant + sufficiency reduction       PROVED / #137
A4R   regular first-bad construction                           PROVED / #140-#150
A4b2r exact regular negative selected residual                 PROVED / #150
FB-01 retained full first-bad/Schur certificate                PROVED / #153
FB-02 exact finite pole-prime discrepancy                      PROVED / #153
FB-03 source-energy endpoint jets + generic smoothing          NOW / theorem dependency
FB-04 interval-certified transformed sign falsification        OPEN / first decisive gate
A4b2r independent selected-residual nonnegative sign           OPEN
A4b2b universal one-step domination                            BROAD FALLBACK
GLOBAL first-bad exclusion                                     AFTER scoped sign OR independent domination
```

The selected stable action remains:

```text
E4_A4_REGULAR_SCHUR_ENERGY_SIGN
```

under frontier

```text
FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN.
```

## Why routing changes after #153

Two first breaks from the post-#150 plan are now consumed theorem prerequisites:

1. **FB-01:** retain the whole-cell first-bad ancestry and full negative-energy Schur state — PROVED / #153;
2. **FB-02:** theoremize exact pole-minus-prime discrepancy under production normalization — PROVED / #153.

The remaining route begins with FB-03:

```text
What endpoint jets of sourceAtomRealEnergy are ACTUALLY forced
by exact boundary-flat/parity hypotheses?
```

The controller must not silently encode the historical answer “order seven generically, order nine in even parity” as theorem state. Those orders remain DERIVED/LEAD until Lean proves them.

## Selected action — E4_A4_REGULAR_SCHUR_ENERGY_SIGN

The action now has three open first breaks:

1. **FB-03 — information-producing theorem dependency.** Determine the true endpoint-jet order and prove a generic iterated-primitive / repeated-integration-by-parts identity instantiated only to that order.
2. **FB-04 — first decisive falsifier.** Feed the exact #153 discrepancy and theorem-backed FB-03 transformed representation into interval-certified canonical calculations. A certified violating state kills the scoped sign mechanism.
3. **FB-05 — closing theorem.** Prove the independent scoped sign `Ecanonical(c-x0)>=0` on the exact retained #153 forced state.

Control-v2 intentionally scores decisive falsifiers differently from chronological theorem dependencies. Therefore `_selected_first_break` may still report FB-04 as the cheapest decisive gate even though a transformed FB-04 claim cannot be specified until FB-03 supplies its exact representation.

That is not a contradiction: routing priority and implementation dependency are separate concepts.

## Evidence-class firewall

Current project labels:

```text
retained first-bad certificate                              PROVED / #153
retained negative-energy Schur certificate                  PROVED / #153
off-line zero -> retained certificate                       PROVED / #153
pole-prime discrepancy identity                             PROVED / #153
full source-channel discrepancy normal form                 PROVED / #153
A>0 from A>=0 + regular + finite Hermitian                  DERIVED unless packaged
historical omega^7 / even omega^9 endpoint expansion        DERIVED / LEAD
historical sixth/eighth-order Riesz formulas                DERIVED / LEAD
raw Loewner/Schur monotonicity failures                     EXPERIMENTAL SIGNAL
#152 interval harness                                       TOOLING / scoped certification
final selected-residual nonnegative sign                    OPEN
```

Control v2 must not collapse these labels.

## Current negative controls

The regular-Schur action must remember:

- universal one-step domination is not a research reduction when obtained by restating successor positivity;
- generic shell/parity/KKT/displacement structure is insufficient without exact canonical source values;
- atomwise positive determinant/SOS is quarantined;
- loose independent channel majorants are conditioning-hostile;
- after #153, splitting pole and prime back apart discards an exact theorem-backed cancellation interface unless the loss is explicitly justified;
- post-#150 numerical probes disfavor global aperture Loewner monotonicity, global minimizing-trial Schur monotonicity and universal positive atom energy;
- the `L*coth(L/2)` aperture coordinate and log-cover deck coordinate are distinct;
- source-atom smoothness does not prove the historical high-order endpoint zero;
- finite Arb certification does not become Lean theorem authority or automatically certify whole-cell ancestry.

## Universal domination fallback

`E4_A4_CANONICAL_ONE_STEP_DOMINATION` remains routable but deliberately demoted. It should become primary again only if a genuinely independent canonical arithmetic mechanism is found.

## Deterministic routing consequence

The base score formula is unchanged. `E4_A4_REGULAR_SCHUR_ENERGY_SIGN` remains the highest-scoring admissible top-level action under complete retro/first-break contracts.

This is routing metadata, not theorem evidence.

## CI expectations

`tools/run_suite.py` runs Control-v2 unit tests. The RHRC workflow real-history smoke run must assert:

- theorem anchor is #153;
- theorem merge/tree correspond to the exact validated #153 state;
- control anchor remains #117;
- frontier is `FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN`;
- selected action is `E4_A4_REGULAR_SCHUR_ENERGY_SIGN`;
- completed FB-01/FB-02 are no longer represented as open first breaks of that action;
- FB-03 wording requires actual endpoint-jet discovery rather than a pre-assumed order-seven/order-nine result;
- terminal claim remains `RH_OPEN`;
- controller theorem authority and terminal-claim mutation remain false.

Newest research implications:

`../RESEARCH_LEADS_POST_153_CERTIFICATE_DISCREPANCY_GREEN_JET_FRONTIER_DELTA.md`

**RH remains OPEN.**
