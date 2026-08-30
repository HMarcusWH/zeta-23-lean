# Connes/CvS external reference map

This directory is a **reference/oracle transplant only**. Nothing here is in the Lean theorem dependency graph and nothing here may promote an RHRC mathematical claim.

Pinned working source: `HMarcusWH/connes-cvs-` commit `5a66d0cd177ef8b8ad1c2c93165b8d56ca40292c` (fork of Akiva Groskin's `connes-cvs-`). The software is MIT licensed; see `LICENSE`.

## Physically preserved reference code

### 1. Cutoff-free CCM closed-form matrix — added by PR #33

Source:

`papers/2_guinand_weil_dictionary_tail_order/scripts/verify_dictionary_threeroute.py`

Blob SHA:

`90576ea92835fff2f9dd2e3aa63ad99829bd17e5`

Local adapted reference:

`closed_form_ccm_reference.py`

The transplanted formulas are the paper package's Route 1 implementation: hypergeometric/digamma/Lerch closed forms for the archimedean entries, exact finite prime-power source, exact pole source, full centered-frequency entries, and the reversal-even block. The local wrapper additionally exposes the full `(-N,...,N)` matrix so it can be compared entrywise to the fork-owned `Zeta23.CCM` / R004 executable model.

### 2. Finite Guinand--Weil dictionary — added at the start of PR #35

Source:

`papers/2_guinand_weil_dictionary_tail_order/scripts/verify_dictionary_threeroute.py`

Blob SHA:

`90576ea92835fff2f9dd2e3aa63ad99829bd17e5`

Local adapted reference:

`finite_dictionary_reference.py`

The preserved reference subset contains the paper package's finite dictionary machinery only:

```text
v -> symmetric centered coefficients u
  -> T_v
  -> K_v closed form / independent Volterra quadrature
  -> ghat_v
  -> g_v closed form / independent physical-space quadrature.
```

The zero-side summation and archimedean-tail routines are deliberately omitted from the local adapter. PR #35 uses this file only as a finite-object regression oracle while Lean formalizes the dictionary independently.

## Pinned sources for later formal ports

### 3. Exact finite source quotient

Source:

`papers/2_guinand_weil_dictionary_tail_order/scripts/audit_full_matrix_source_quotient.py`

Blob SHA:

`61ef2494805b86cbc3687b8028fd704762f47956`

Formal port remains deferred to planned PR #38. The source audit verifies that the finite divided-difference source map factors through exactly `2N+1` coordinates: `omega`, `sin(2*pi*k*omega)`, and `omega*cos(2*pi*k*omega)` for `1 <= k <= N`.

### 4. Prime-power cutoff-flow rank-one jump

Source:

`papers/3_matrix_von_mangoldt_measure/scripts/check_canonical_scale.py`

Blob SHA:

`360a2b8bc5b6dd32f160b9dd2e31446783426952`

Formal port remains deferred to planned PR #39. The external guard checks the prime-path event law

`Delta Q'_N = -2 Lambda(q)/(sqrt(q) log(q)) * 11^T`

at every prime-power threshold in its test range.

### 5. Parity-safe numerical ground state

Source:

`connes_cvs/operator.py`

Blob SHA:

`07dde0ca2f2811ebbf80fc4d2e2fff6869d4e7fa`

Formal parity/extremal-spectrum work remains deferred to planned PR #40. The implementation explicitly checks exact centrosymmetry before projecting to the reversal-even sector.

## Normalization lock inherited from PR #33 and formalized by PR #65

There are three objects/conventions in play:

1. fork-owned CCM matrix `M`, implemented formally in `Zeta23.CCM`;
2. the cutoff-free finite source convention `Q_inf`;
3. inherited explicit-formula `WeilGram` normalization used by earlier R003 diagnostics.

PR #33's independent audit identified

```text
Q_inf = M + 2*cCorrection(L)*I
```

with primitive map

```text
alpha_reference = alpha_ours
beta_reference  = beta_ours
gamma_reference = gamma_ours - cCorrection(L)
pole_reference  = pole_ours.
```

PR #65 formalizes that source convention independently in
`Zeta23/CCM/CutoffFreeMatrix.lean` and proves

```text
cutoffFreeMatrix = finiteMatrix + 2*cCorrection(L)*I
cutoffFreeMatrix = dictionaryMatrix
zeroSideMatrix   = cutoffFreeMatrix       (for L > 0).
```

The source cutoff/lambda convention is also theorem-locked:

```text
L = log c = 2*log(lambda),  c = lambda^2
```

for positive `lambda`.

The earlier PR #29 finite diagnostic

```text
WeilGram = 2*M + 4*cCorrection(L)*I
```

therefore remains consistent with

```text
WeilGram = 2*Q_inf.
```

The last displayed `WeilGram` equality is **not** promoted by this source-map
note unless separately bound to a Lean theorem.  PR #65's theorem authority is
the finite cutoff-free source-convention map listed above.

## Authority boundary

- External Python: reference and falsification oracle only.
- RHRC receipts: evidence/provenance only.
- Lean/comparator: theorem authority.
- No file in this directory may be imported by `Zeta23`.
