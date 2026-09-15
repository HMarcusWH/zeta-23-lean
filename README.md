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
merged research PR = #190
validated research head = 8701920b0da18ae6595ad0eee55c1f6cb291a94f
merged research commit = f87da9fde71dd1e74419c6ae5848eee3787c27e4
validated research tree = af8774b65c898de221a5bf32977ccff3407a7b2d
RHRC run #1096 = SUCCESS
Permansson run #869 = SUCCESS
research disposition = JOINT_EXACT_VECTOR_SEPARABLE / JOINT_THRESHOLD_SIGNATURE_SEPARABLE

CONTROL SEMANTIC AUTHORITY
PR #117 merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
selected first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

The theorem, research and control anchors are intentionally separate. Research green is not theorem promotion.

## Theorem frontier

The compiler-validated theorem ladder remains through PR #184. In particular Lean proves the complex-Hermitian 2x2 Schur calculus, the frozen production family on the logarithmic cover, the exact fixed-cell bridge to `parityCompressedCanonical`, N2 predecessor/canonical-shell reconstruction and orthogonality, and

```text
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0.
```

PR #184 does **not** prove source-specific remainder domination, contact existence/uniqueness, an opposing first-bad orientation, negative-root exclusion or RH.

## Research progression through #190

```text
#186  broad production-remainder domination on the frozen Q14 panel
      -> DOMINATION_SIGNAL_MIXED
      -> simple universal domination falsified in tested scope

#188  frozen normalization-safe selector audit
      -> seven strong selectors + three diagnostic remainder components

#189  exact semantic-independence audit
      -> every individual frozen selector is abstractly separable from target sign

#190  exact joint-separability audit
      -> complete seven-dimensional strong vector can remain identical
      -> same nonboundary ZERO/ONE threshold signature
      -> opposite normalized FB-05 target signs
      -> all 2^7 - 1 = 127 nonempty subsets are therefore also insufficient
         inside the audited ambient normalized algebra
```

The #190 countermodel is an **ambient algebra countermodel**. It is not claimed to be an actual canonical arithmetic CCM state.

## Current active path — FB-05 canonical realizability

The frozen selector-mining programme has done its job. The next question is no longer

```text
which combination of G1/P1/P2/C1-C4 predicts the target sign?
```

because #190 closes that observation surface in the ambient normalized algebra.

The live question is now:

```text
which canonical production realizability constraint forbids the #190 reflected twin?
```

Actual production channels are more constrained than the #190 ambient coordinates. In the research derivative backend,

```text
scalar_shift = 2*cCorrection'(L) I
arch_signed  = -arch_direct - scalar_shift
```

so `arch_signed` and `scalar_shift` are not independent production coordinates. This is a **lead**, not yet a theorem excluding all reflected twins.

The next research pass should impose actual common-aperture production structure progressively and identify the first constraint that destroys the opposite-target twin. Only then should that constraint be considered for Lean formalization.

## Current open obligations

```text
canonical production realizability of the post-#190 ambient twin      OPEN / ACTIVE
actual N2 production remainder scalar derivative witnesses             OPEN
actual production HasDerivAt Schur identity                            OPEN
contact-local contradiction-producing arithmetic restriction           OPEN
same-state first-bad opposing contact orientation                       OPEN
centered finite-width H1 / q13 whole-cell contact classification        OPEN
sourceMoment <-> M4 canonical-state rigidity                            OPEN
simultaneous even/odd bad exclusion                                     OPEN
odd-selected first-bad branch closure                                   OPEN
negative-root exclusion                                                  OPEN
outside-strip/trivial-zero terminal seam                                OPEN
RiemannHypothesis                                                        OPEN
```

## Permanent firewalls

- compiler/CI evidence outranks prose;
- theorem authority remains #184 until a later Lean-bearing PR passes the theorem gates;
- #186 falsifies only broad domination in its frozen finite scope;
- #189/#190 prove executable algebraic separability only in their declared ambient model;
- ambient reflected twins are not automatically canonical production states;
- do not resume arbitrary selector composition, threshold refitting, or subset search on G1/P1/P2/C1-C4;
- actual production relations must use the same state, aperture, parity, normalization and production object;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**

See `research/RHRC/CURRENT_RESEARCH_PLAN.md`, `research/RHRC/RESEARCH_LEADS.md`, `research/RHRC/FB05_INCOMPATIBILITY_PROGRAM.md`, and the post-#190 research delta for the current execution route.