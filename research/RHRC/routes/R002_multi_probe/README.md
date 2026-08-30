# R002 — Multi-probe tomography → Gram/operator observables

Search over a predeclared family of apertures/test functions/probes rather than
one compression. The candidate must identify information absent from the
TightMult certificate and survive the G03/G04/G05 sanity fixtures.
Promotion condition: an exact separation theorem, not a classifier score.

## Locked objects

- **Probe family:** the taper grid `τ_k = T + 2πk/L`, `k < d ≈ LT/2π`, with
  `φ` supported in `[−L/2, L/2]`, `L = λ·l`, `l = log(T/2π)`, `X = e^L`.
- **Observable:** the *spectrum* of the windowed Gram `G̃(T)`, whose zero-side
  and prime-side expressions are unconditionally equal
  (`ZeroConfig.Gz_eq_Gp` + `paperInputs_zeta`). The retained channel is the
  **eigenvalue sign / forbidden direction**, i.e. the negative index `n₋`,
  which the paper's certificate never uses.
- **Block object:** `ZeroSide.ZeroBlockData.pair_term`'s exact off-line pair
  block `2m(xxᵀ − yyᵀ)`, `u = x + iy`, with `y = 0` exactly for on-line zeros.

## Proof-search ladder

| step | statement | status |
|---|---|---|
| P0 | off-line pair block has a strictly negative direction, with an explicit witness and an exact value | **CLOSED** (`dotProduct_pairBlock_orthoWitness`, `..._neg`) |
| P1 | on-line configurations and the TightMult mock have no such direction | **CLOSED** (`dotProduct_nonneg_of_onLineCombination`) |
| P2 | the two are therefore not equal — block-level separation | **CLOSED** (`not_onLineCombination_of_pairBlock`) |
| P3 | windowed visibility: the negative direction survives the PSD on-line bulk | **OPEN** — masking; visible iff `δL ≳ √(6/λ)`, and unconditionally at `λ > 1` where the grid oversamples (§3 of the feasibility certificate) |
| P4 | arithmetic leg: `∫\|W\|²ν_X ≥ −θ` for all band-limited `W` | **OPEN and RH-equivalent** in the `∀(T, λ>1)` limit (Weil's criterion) — see OBS-009 |
| P5-original | naive CCM identity `M_{λ,N} = ½·WeilGram` with no diagonal correction | **REFUTED AS STATED** — the diagonal archimedean correction is real |
| P5-corrected | exact normalized CCM ↔ raw truncated-character kernel zero side: `rawKernelZeroSideMatrix = 2·M + 4·cCorrection(L)·I` | **CLOSED / PROVED IN LEAN** — `R002_KERNEL_ZERO_SIDE_BRIDGE` |

P0–P2 are proved in `Zeta23/ExceptionalZero/ProbeGramNegativity.lean`
(sorry-free, standard axioms only). P3 remains open and P4 remains RH-equivalent.
The original P5 statement remains refuted; the corrected raw-kernel normalization
is now theorem-backed by `Zeta23/CCM/RawKernelZeroSideBridge.lean`.

## Feasibility certificate

`MULTI_PROBE_GRAM_OPERATOR_FEASIBILITY_2026_08_21.md` — six candidate families,
scalar-collapse audit against OBS-008, every-δ bookkeeping with numerical
validation, online-double adversary, named unconditional mechanisms, ranking,
decision token `PROMOTE_ONE_CANDIDATE_TO_FORMALIZATION`.

Killed there, with decisive reasons: **R002-B** (odd moment `tr G̃³` — needs
ternary Λ-correlation to relative precision `1/N`), **R002-E** (L² aperture
coherence — collapses to OBS-008 by linearity plus Cauchy–Schwarz), **R002-F**
(full-diagonal majorization — δ-insensitive at leading order). Both kills are
recorded as DR-006.

## R002-D — raw truncated-character kernel bridge: original conjecture refuted, corrected normalization proved

Numerical result obtained 2026-08-21 (claim cap
`FINITE_NUMERICAL_DIAGNOSTIC_ONLY`, script `check_ccm_weil_bridge.py`): for the
even two-sided test `K_{nm}(y) = q_basis(n,m,|y|,L)` attached to R004's CCM
matrix, two of the three explicit-formula channels match **exactly**, to 10
digits, with a uniform factor 2:

```
h_{nm}(i/2) + h_{nm}(−i/2)              = 2 · pole_component(n,m,L)
Σ_k Λ(k)k^{−1/2}(K(log k) + K(−log k))  = 2 · prime_component(n,m,L)
```

The archimedean channel does **not**: the ratio to `arch_component` is
consistent with `−2` on the off-diagonal entries (−1.90 … −1.97, within the
quadrature truncation tail) but clearly not on the diagonal (−1.59 at `(0,0)`,
−0.75 at `(1,1)`, stable across λ). The assembly test agrees: off-diagonal
`(1,0)` matches the Weil zero-side sum within the zero tail, both diagonals are
off by a near-constant ≈ 1.064.

**So `M_{λ,N} = ½·(Weil Gram)` is FALSE as stated — and the gap is localized to
the diagonal archimedean term**, which is exactly where R004 uses a separate
formula (`2γ_L(n) − 2β_L(n)`) instead of the off-diagonal divided difference,
and exactly the part of `M` that the displacement identity leaves unconstrained
(`[D,M]` vanishes on the diagonal identically).

**Historical state on 2026-08-21.** Numerical archaeology found the residual
`c(L)·δ_{nm}` with `c(L) = 4·c_correction(L)`; the diagonal-only structure was
recognized as structural because `K_{nm}(0)=2δ_{nm}`. At that point the corrected
statement `M = ½·(WeilGram-c(L)I)` was still only numerical, and the direct route
was blocked by the piecewise-`C¹` raw kernel.

**Current theorem state after PR #64.** The direct-`EF_lit` obstruction is no
longer relevant. The production dictionary basis satisfies exactly

```text
dictionaryBasisTest = 1/2 * kernel.
```

Its entrywise zero side was legalized independently in R003, and #62 proves the
exact production bridge. PR #64 scales that theorem-authoritative object back to
the original raw `qBasis/kernel` convention and proves

```text
rawKernelZeroSideMatrix
  = 2 * zeroSideMatrix
  = 2 * finiteMatrix + 4*cCorrection(L)*I.
```

The theorem-authoritative source is
`Zeta23.CCM.rawKernelZeroSideMatrix_eq_two_finiteMatrix_add_four_correction`.
Thus the **original no-correction identity remains refuted**, while its corrected
diagonal-shift successor is **PROVED**. No new mollifier, archimedean quadrature,
or direct nonsmooth explicit-formula application is needed.

Scope firewall: this closes the R002-D **centered truncated-character
`qBasis/kernel` bridge**. It does **not** identify `finiteMatrix` with the general
taper-grid `G̃(T)` used by R002-A; that would require an additional exact
basis/parameter map. P3 masking therefore remains untouched.

## Dumbassery checks

- The block-level separation is **not** a windowed-visibility theorem: the
  on-line bulk can mask the negative direction (P3).
- `n₋ ≥ 1` at block level does **not** imply RH; the arithmetic leg (P4) is
  RH-equivalent, per OBS-009.
- The historical `λ > 1` every-δ oversampling signal is **outside the current
  production `Params.Valid` envelope**, which theoremically requires
  `λ ≤ 1`. PR #66 makes this firewall explicit. The old experiment remains an
  experimental route-design signal, not a theorem about the current valid
  production family.
- Numerical `λ_min < 0` in the synthetic diagnostic is a finite computation on a
  synthetic zero lattice; it is not evidence about ζ.
- The old finite numerical factor-two diagnostic is now superseded by the exact
  raw-kernel theorem above. That theorem does not upgrade the general taper-grid
  visibility problem or provide positivity.


## D0-R — R002 taper-grid versus canonical CCM: specialization only

PR #65 made the canonical finite CCM object theorem-authoritative:

```text
zeroSideMatrix
  = cutoffFreeMatrix
  = finiteMatrix + 2*cCorrection(L)*I.
```

PR #66 then audits whether the general R002-A taper-grid object is actually the
same object in another basis.

The answer is **specialization only**.

The theorem-level firewalls are:

```text
Gz = Az + Ez
Gz = Az  <->  Ez = 0
1 < P.lam  ->  not P.Valid
tau_k = T + k*hgrid
```

and a supplied response-coordinate map acts on each symmetric rank-one R002
atom by transpose congruence.

The companion falsifier
`compare_r002_ccm_probe_families.py` confirms the useful positive part of the
old intuition: the current CCM `qBasis` is exactly the elementary closed form
of the real-symmetrized shifted correlation of **hard-window Fourier
characters**. Direct quadrature agrees.

However, replacing the hard window by an R002-style smooth plateau/ramp taper
changes the entries. More importantly, the production R002 and CCM objects
still differ theorem-visibly in index type, carrier, taper, zero truncation, and
parameter set.

Therefore PR #66 does **not** promote

```text
G-tilde(T) = zeroSideMatrix
```

or any universal congruence/compression theorem.

The correct D0-R settlement is:

```text
SPECIALIZATION_ONLY
generic R002 masking remains an R002-side obligation
and is not a CCM critical-path bottleneck.
```

See `D0_R_R002_CCM_MAP_AUDIT_2026_08_30.md` for the exact object table,
proof/experiment labels, and claim firewall.

## Route-specification adaptation — 2026-08-21 (DISCOVERY phase, logged)

The route previously named only "a predeclared multi-probe family" with no
observable fixed. It is now specialized to the **negative-index channel of the
windowed Gram**, and claim `R002_MULTI_PROBE_SEPARATION` is restated to the
block-level statement actually proved (with its transversality hypothesis
`gramDet x y ≠ 0` explicit) rather than the earlier open-ended wording. The
claim registry carries the corresponding `adaptation_note`.

## Non-claims

- No RH evidence, no RH route closure, no promotion of `C_RH`.
- No windowed-visibility theorem, no arithmetic upper bound.
- The corrected raw truncated-character kernel/CCM identity is theorem-backed.
  PR #66 classifies the hard-window character relation as specialization-only;
  no identity with the full smooth-taper R002-A `G̃(T)` is claimed.
- Historical finite numerical diagnostics remain evidence only; the promoted
  corrected bridge is the Lean theorem named above.
