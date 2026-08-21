# Connes/CvS external reference map

This directory is a **reference/oracle transplant only**.  Nothing here is in the Lean theorem dependency graph and nothing here may promote an RHRC mathematical claim.

Pinned working source: `HMarcusWH/connes-cvs-` commit `5a66d0cd177ef8b8ad1c2c93165b8d56ca40292c` (fork of Akiva Groskin's `connes-cvs-`).  The software is MIT licensed; see `LICENSE`.

## What PR #33 carries over

### 1. Cutoff-free CCM closed-form matrix

Source:

`papers/2_guinand_weil_dictionary_tail_order/scripts/verify_dictionary_threeroute.py`

Blob SHA:

`90576ea92835fff2f9dd2e3aa63ad99829bd17e5`

Local adapted reference:

`closed_form_ccm_reference.py`

The transplanted formulas are the paper package's Route 1 implementation: hypergeometric/digamma/Lerch closed forms for the archimedean entries, exact finite prime-power source, exact pole source, full centered-frequency entries, and the reversal-even block.  The local wrapper additionally exposes the full `(-N,...,N)` matrix so it can be compared entrywise to the fork-owned `Zeta23.CCM` / R004 executable model.

### 2. Exact finite source quotient

Source:

`papers/2_guinand_weil_dictionary_tail_order/scripts/audit_full_matrix_source_quotient.py`

Blob SHA:

`61ef2494805b86cbc3687b8028fd704762f47956`

Status in this PR: provenance pinned, theorem/code port deferred to the planned generic source-calculus PR.  The source audit verifies that the finite divided-difference source map factors through exactly `2N+1` coordinates: `omega`, `sin(2*pi*k*omega)`, and `omega*cos(2*pi*k*omega)` for `1 <= k <= N`.

### 3. Prime-power cutoff-flow rank-one jump

Source:

`papers/3_matrix_von_mangoldt_measure/scripts/check_canonical_scale.py`

Blob SHA:

`360a2b8bc5b6dd32f160b9dd2e31446783426952`

Status in this PR: provenance pinned, formal port deferred.  The external guard checks the prime-path event law

`Delta Q'_N = -2 Lambda(q)/(sqrt(q) log(q)) * 11^T`

at every prime-power threshold in its test range.

### 4. Parity-safe numerical ground state

Source:

`connes_cvs/operator.py`

Blob SHA:

`07dde0ca2f2811ebbf80fc4d2e2fff6869d4e7fa`

Status in this PR: provenance only.  The implementation explicitly checks exact centrosymmetry before projecting to the reversal-even sector; this is a useful numerical contract for the later parity/even-simple campaign.

## Normalization question this PR must settle

There are currently three objects/conventions in play:

1. fork-owned CCM matrix `M`, implemented formally in `Zeta23.CCM` and mirrored by `research/RHRC/routes/R004_prolate_v2/run_commutator_gauntlet_v2.py`;
2. Groskin/CCM cutoff-free finite matrix `Q_inf`;
3. the inherited explicit-formula `WeilGram` normalization used by the R003 diagnostics.

PR #29 found numerically

`WeilGram = 2 M + 4 cCorrection(L) I`.

PR #33 does **not** assume that relation is the primitive CCM identity.  It first compares `M` directly against `Q_inf`, channel by channel and entry by entry.  The resulting `CCM_NORMALIZATION_LOCK_v1.json` records the exact convention map that later Lean work is allowed to target.

## Authority boundary

- External Python: reference and falsification oracle only.
- RHRC receipts: evidence/provenance only.
- Lean/comparator: theorem authority.
- No file in this directory may be imported by `Zeta23`.
