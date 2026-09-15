# RHRC Control v2 — deterministic evidence-gated research routing + retroactive memory

> **Authority firewall:** Control v2 is a research-routing diagnostic. It cannot promote Lean theorems, write claim authority, emit the terminal RH answer, or turn numerical/search output into RH evidence. **RH remains OPEN.**

## Separate authority anchors

```text
THEOREM AUTHORITY
latest theorem-bearing PR = #184
merge = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e
head  = a756494ebe7e2530715e996b9a9a341fbe07c683
tree  = 6c77cd470809959a403b3bcc5f08d39f4076fa4c

LATEST RESEARCH EVIDENCE
merged research PR = #190
head  = 8701920b0da18ae6595ad0eee55c1f6cb291a94f
merge = f87da9fde71dd1e74419c6ae5848eee3787c27e4
tree  = af8774b65c898de221a5bf32977ccff3407a7b2d
RHRC #1096 = SUCCESS
Permansson #869 = SUCCESS
research disposition = JOINT_EXACT_VECTOR_SEPARABLE / JOINT_THRESHOLD_SIGNATURE_SEPARABLE

CONTROL SEMANTIC AUTHORITY
PR #117
merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
```

The theorem, research and control anchors are intentionally distinct.

## Routed frontier

```text
FB-05A generic real Schur/contact orientation calculus             PROVED / #182
FB-05B Hermitian production/log-cover Schur drift decomposition    PROVED / #184
FB-05C broad remainder domination on frozen panel                  FALSIFIED / #186 research
FB-05D frozen selector family                                      AUDITED / #188
FB-05E individual selector sufficiency in ambient algebra          CLOSED / #189 research
FB-05F joint seven-selector sufficiency in ambient algebra         CLOSED / #190 research
FB-05G canonical production realizability of the reflected twin    NOW / selected research bottleneck
```

The selected action remains `E4_A4_REGULAR_SCHUR_ENERGY_SIGN` under frontier `FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN`. The selected first-break ID remains `E4A4-SCHUR-FB-05`.

## Why routing changes after #190

#186 killed the simple universal domination premise on the frozen finite panel. #188-#190 then tested whether the mixed sign split could be explained by the predeclared normalization-safe state observables.

PR #190 supplies an exact ambient rational pair with:

```text
same complete seven-dimensional strong selector vector
same nonboundary ZERO/ONE threshold signature
opposite normalized target signs
```

Therefore Control-v2 must not recommend another combination, threshold refit or subset search over the same G1/P1/P2/C1-C4 surface.

The next information target is the difference between the ambient normalized state space and the image of actual canonical production.

## Selected action — E4_A4_REGULAR_SCHUR_ENERGY_SIGN

The sole live first break is still an independently meaningful canonical arithmetic restriction on the exact same retained/contact state. What changed is the search object.

### Highest-information research lane

Audit **canonical realizability** of the post-#190 reflected twin.

The actual executable source decomposition already couples source channels:

```text
scalar_shift = 2*cCorrection'(L) I
arch_signed  = -arch_direct - scalar_shift
```

so the hidden scalar coordinate used by #190 is not obviously free when one requires a common production aperture.

Required progression:

```text
ambient normalized algebra
 -> source-channel construction identity
 -> scalar-aperture law
 -> common direct-arch derivative
 -> common Schur geometry
 -> full same-L canonical source reconstruction
```

The controller should treat exact identity exclusion as strong research information and failed bounded searches only as `UNRESOLVED`.

### Formal infrastructure lane

Actual production derivative witnesses and an instantiated `HasDerivAt` Schur identity remain useful. Formalize the smallest production relation shown by the research audit to be decisive; do not theoremize weak scalar positivity or revive universal domination just because they are easy to state.

### Pair-A decision rule

If a canonical production relation kills the twin, attempt to compose it with #184 and an independently proved opposing first-bad property on the exact same state. If a genuine canonical twin survives full production constraints, downgrade Pair A and prioritize other incompatibility pairs.

## Evidence firewall

```text
#184 Hermitian/log-cover package          PROVED
#186 mixed domination                     RIGOROUS FINITE RESEARCH
#188 selector audit                       RIGOROUS FINITE RESEARCH
#189 individual semantic independence     EXACT EXECUTABLE RESEARCH
#190 joint semantic independence          EXACT EXECUTABLE RESEARCH
canonical realizability                   OPEN
FB-05 closure                             OPEN
negative-root exclusion                   OPEN
RH                                        OPEN
```

## CI expectations

`tools/run_suite.py` runs Control-v2 tests. The workflow smoke must continue to assert:

- theorem anchor #184;
- control anchor #117;
- unchanged frontier/action/first-break IDs;
- controller theorem authority false;
- terminal-claim mutation false;
- terminal claim `RH_OPEN`.

The post-#190 sync tests additionally guard the latest research evidence, ambient-vs-canonical firewall, consumed selector surface and retro vocabulary.

Newest implications: `../RESEARCH_LEADS_POST_190_JOINT_SELECTOR_SEPARABILITY_DELTA.md`.

**RH remains OPEN.**