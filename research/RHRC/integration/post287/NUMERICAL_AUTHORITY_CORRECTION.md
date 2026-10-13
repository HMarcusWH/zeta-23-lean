> **Follow-up after the repair (source `31512dbb`):** Guarded K2-even 1,310-tile/192-bit verification and K2-odd 350-tile independent verification succeeded. Frozen K3 SECOND 18/18 prescribed boxes PASS, *not* full K3. The source-pinned 30-layer full K3 campaign returned `UNRESOLVED` with 26 complete and 4 incomplete even layers (35 unresolved intervals), see [run 38332529352](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/38332529352). All earlier affected NaN-acceptance certificates remain INVALIDATED. No past artifact is retroactively rebound to a newer commit. D2 Full deferred, RH_OPEN.

---

# Indeterminate Taylor curvature: certificate authority correction

Date: 2026-10-13. RH_OPEN. This correction is independent of the older
centre-only determinant-curvature error. Passing compiler gates does not
repair a numerical certificate, and passing numerical jobs does not supply
Lean proof terms.

## Reproduced acceptance defect

The Q4-even artifact of
[manual run 38326458483](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/38326458483)
contains an accepted whole-cell tile with both `second_a_interval` and
`second_delta_interval` equal to `nan`. Its positive recorded lower bounds
were calculated by silently dropping the unknown Taylor remainder:

`min(arb(0), arb('nan').lower())` evaluates to `arb(0)`.

An indeterminate enclosure cannot establish that curvature is nonnegative.
Replacing it by zero is unsound. The no-search K3 checker repeated the
producer's evaluator, so its higher-precision PASS did not reject this bug.
The same unchecked curvature floor appears in the post287 K2 even and odd
Taylor paths. The invalidated manual campaign was stopped, and all artifacts
remain available as historical execution output.

## Forensic disposition of the old outputs

| Old output | Accepted rows with non-finite diagnostics | Rows recording finite diagnostics | Authority |
|---|---:|---:|---|
| d214 M51 K2 even, 1,205 rows | 4: Q1 two, Q2 one, Q4 one | 1,201 | Complete M51 certificate invalidated; guarded replay required |
| Manual K2 odd prerequisite, 266 rows | 4: Q1 one, Q2 two, Q4 one | 262 | Complete prerequisite certificate invalidated; guarded replay required |
| Eight available manual K3 layers, 459 rows | 10: Q1 even four, Q1 odd two, Q2 even two, Q2 odd one, Q4 even one | 449 | No full K3 certificate; affected layer passes invalidated |
| Corrected-formula frozen 18-box gate | Leaf curvatures omitted from old summary | Not inferable from summary | Guarded gate replay required |

Finite diagnostic strings are useful forensic data; this count is not a
retroactive independent verification of those rows or of full coverage.
Old records must not be relabelled to match repaired source digests.

The older legacy M51 path used a nan-preserving remainder rule, so this
specific min defect does not invalidate that rule. Its old rational upper
endpoint, however, lies below exact log16 and does not supply the missing
post287 full-window assertion. Preserve both limitations separately.

## Required repair and acceptance

Before any Taylor interval can be accepted, every value used by its lower
bound must be finite, especially the interval curvature/remainder. An
indeterminate evaluation must subdivide within the fixed budget or become
UNRESOLVED; it must never supply a positive tile by discarding a remainder.
Regression controls must reproduce the rejected nan case as well as finite
positive and genuinely negative curvature cases.

Corrected-source normalization, M51, K2 odd, frozen feasibility and full K3
receipts must be harvested again with their exact source hashes. The existing
method-selection and resource limits remain in force. A successful complete
campaign still requires all 30 checked layers and a fresh non-partial global
receipt; an incomplete campaign retains its exact unresolved disposition.

The formal K2 M51 premise and K3 hWindows premise remain explicit. Neither
the old outputs nor any repaired Python receipt instantiates those Lean
hypotheses. No RH or unconditional Lean window claim follows.
