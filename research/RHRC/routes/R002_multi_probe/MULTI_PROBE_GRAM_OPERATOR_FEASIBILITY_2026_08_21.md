# R002 multi-probe → Gram/operator feasibility certificate — 2026-08-21

Mandatory design gate for route `R002_multi_probe`, produced **before** terminal
Lean coding, per the OBS-008 escape requirement ("a named new information
channel must come with a *new, weaker-looking but sufficient* zero-side leg
whose matching upper bound is provable by an identified unconditional
mechanism — and the pair must be exhibited before terminal coding").

> **Post-PR #66 D0-R status note (2026-08-30).** This file is retained as the
> historical 2026-08-21 feasibility certificate. Its `lambda > 1` oversampling
> discussion is an EXPERIMENTAL route-design signal, not a theorem about the
> current production-valid R002 family: the current Lean definition
> `Params.Valid` includes `lam_le_one : P.lam <= 1`. PR #66 also classifies
> the generic smooth-taper R002-to-CCM relation as **SPECIALIZATION_ONLY**; see
> `D0_R_R002_CCM_MAP_AUDIT_2026_08_30.md`.

Status legend for every assertion below:
`[LEAN]` proved in this repository (name given) · `[CLASSICAL]` standard
unconditional mathematics · `[DERIVED]` computed here, elementary, not yet
formalized · `[NUM]` finite numerical diagnostic, claim cap
`FINITE_NUMERICAL_DIAGNOSTIC_ONLY` · `[CONJ]` conjectural.

---

## 0. The design constraint we are working against

`Zeta23.ExceptionalZero.arithmeticSideSubexponential_iff_criticalLine` `[LEAN]`
proves the R001 scalar target is *equivalent* to RH. The generic form of that
wall (OBS-008): for any exact observable `O`, once the zero-side leg
"off-line zero ⇒ `¬P(O)`" is proved, the matching upper-bound leg
"unconditional ⇒ `P(O)`" is RH-strength by construction. **Observable
engineering can only relocate the difficulty.** The legitimate goal is
therefore a relocation into a statement that (i) is better posed (no
δ-threshold, no exponent race), and (ii) has a *named* candidate unconditional
mechanism. Sections 1–7 evaluate six candidates on exactly that basis.

---

## 1. Candidate inventory

Common setup (all `[LEAN]`, `Zeta23/Defs.lean`, `Zeta23/ZeroSide.lean`):
probe grid `τ_k = T + 2πk/L`, `k < d ≈ LT/2π`, taper `φ` supported in
`[−L/2, L/2]`, `L = λ·l`, `l = log(T/2π)`, `X = e^L = (T/2π)^λ`. The Gram
matrix has two exactly equal expressions — zero side
`G_kl = Σ_ρ m_ρ φ̂(γ_ρ−τ_k)φ̂(γ_ρ−τ_l)` and prime side
`G_kl = ∫ φ̂(τ−τ_k)φ̂(τ−τ_l) ν_X(τ)dτ`, `ν_X = μ + Π_X + P_X` — unconditionally
for ζ (`ZeroConfig.Gz_eq_Gp` + `paperInputs_zeta`). Hat units `Ĝ = G/(aL²)`.

### R002-A — NEG-INDEX (flagship)

**Definition.** `P(G) := "λ_min(G̃(T)) ≥ −θ"`, equivalently `n₋^θ(G̃(T)) = 0`;
the multi-probe object is the full spectrum of the windowed Gram, not a scalar
moment. Information retained: **eigenvalue sign / forbidden direction**.

**Zero-side mechanism** `[LEAN]` for the algebra, `[DERIVED]` for the scales.
`ZeroSide.pair_term`: an off-line pair `{ρ, 1−ρ̄}`, `ρ = ½+δ+iγ`, contributes
*exactly* `2m(xxᵀ − yyᵀ)` where `u = x+iy`, `u_k = φ̂((γ−τ_k) − iδ)`. Writing
`r_k = γ−τ_k` and using `φ` real even,
```
x_k = ∫ φ(v) cosh(δv) cos(r_k v) dv,     y_k = ∫ φ(v) sinh(δv) sin(r_k v) dv
```
so `y_k = −δ·φ̂′(r_k) + O(δ³)`. **On-line zeros give real vectors** (`y = 0`,
`ZeroSide.star_v_of_onLine`), so `y ≠ 0` ⟺ off-line: the −`yyᵀ` direction is
an exact off-line signature, and `blockA_decomp` shows it is the *only* source
of non-positivity in `A`.

**Named unconditional control theorem.** The Rayleigh quotient at any real `w`
is, by `Gz_eq_Gp`, *exactly*
```
wᵀ G w = ∫ |W(τ)|² ν_X(τ) dτ,      W(τ) := Σ_k w_k φ̂(τ−τ_k).
```
So `P(G)` **is** Weil positivity restricted to band-limited tests of bandwidth
`L` localized at height `T`. Mechanism name: **band-limited Weil positivity**
(Weil's criterion, restricted support). See §5 for its exact grade.

**Failure mode.** Masking by the PSD on-line bulk — quantified in §3, and it is
regime-dependent, which is the substantive finding of this document.

**Relation to R001.** Disjoint channel: R001 measures norm growth of a scalar in
an aperture parameter; A measures a spectral *sign* at fixed aperture. R001's
detector is an exponential race; A's is a linear-algebra obstruction.
**Relation to R003/CCM.** Direct — see R002-D: the CCM matrix appears to be an
instance of the same Weil–Gram family.

**Status: LIVE (promoted at block level; see §7).**

### R002-B — ODD-MOMENT

**Definition.** `tr G̃³` (and multi-θ `n₊^θ/n₋^θ` profiles). Information
retained: eigenvalue signs via an odd moment — genuinely outside the TightMult
quadruple `(tr, ‖·‖_F², integer atoms, n₊)`.

**Zero-side mechanism.** A visible negative eigenvalue `−ε` shifts `tr Ĝ³` by
`−ε³` plus interaction terms `[DERIVED]`.

**Failure mode (decisive).** The bulk is `tr Ĝ³ ≍ N·λ^{−3}` with
`N ≍ Tl/2π` `[DERIVED]`; the signal is `O(ε³) = O(1)`. Detection needs the
cubic main term to *relative* precision `1/N`, i.e. an asymptotic for the
ternary correlation `Σ_{n,m,l} Λ(n)Λ(m)Λ(l)(nml)^{−1/2}W(log n, log m, log l)`
on the near-multiplicative diagonal `l ≈ nm`, with power-saving uniformity.
No unconditional mechanism exists at that strength `[CLASSICAL]`; the two
proven moments (`moments_of_traces`) do not extend to the third.
**Status: KILLED** (recorded as DR-006).

### R002-C — CROSS-WINDOW COHERENCE

**Definition.** Two-center cross-Gram `G^{(T,T′)}_{kl}` built from the *unused*
off-diagonal frame identity `Σ_k φ̂(τ−τ_k)φ̂(τ′−τ_k) = L·Φ(τ−τ′)`
(`Taper.hasSum_phiHatR_mul` `[LEAN]`). Information retained: relative phase
between two windows. Zero side: an off-line pair contributes coherently in the
same `y`-direction at both centers. Unconditional control: `lem_ends_nu`
`[LEAN]` is density-generic and applies verbatim.
**Failure mode.** Same masking arithmetic as A, with no compensating gain
identified; the cross terms decay like `Φ(T−T′)` and lose the localization that
makes A's signal grow. **Status: SECOND TIER (open, not promoted).**

### R002-D — CCM ≡ WEIL–GRAM BRIDGE (R003/R004 unification)

**Definition.** The conjecture that R004's finite CCM matrix
`M_{λ,N} = Pole − Arch − Prime` (Fourier indices `n,m ∈ [−N,N]`,
`L = 2 log λ`) is the Weil explicit-formula zero-side Gram in the truncated
character family on `[0,L]`, i.e. with the even two-sided test
`K_{nm}(y) := q_basis(n,m,|y|,L)` and `h_{nm}(z) := ∫K_{nm}(y)e^{izy}dy`:
```
Σ_ρ m_ρ h_{nm}(γ_ρ)  =  2 · M_{nm}     (conjectured exact identity)
```

**Evidence obtained this session** `[NUM]`, script `check_ccm_weil_bridge.py`
(this directory), λ ∈ {2, 3}, `(n,m) ∈ {(0,0),(1,0),(1,1),(2,1),(−1,1),(2,−2)}`.

*Two channels match exactly* — agreement to 10 digits on every tested entry:
```
  h_{nm}(i/2) + h_{nm}(−i/2)                        = 2 · pole_component(n,m,L)
  Σ_k Λ(k)k^{−1/2}(K(log k) + K(−log k))            = 2 · prime_component(n,m,L)
```

*The archimedean channel does **not** match with a uniform factor*, so the
conjecture **is false as stated**. The measured ratios
`[(1/2π)∫h(r)·bracket(r)dr] / arch_component(n,m,L)` split sharply by position:

| entry | λ = 2 | λ = 3 | verdict |
|---|---|---|---|
| (1,0), (−1,1) | −1.9488 | −1.9692 | off-diagonal: consistent with −2 within the `R = 400` truncation tail `≍ log R/R ≈ 0.015` absolute, which for `\|arch\| ≈ 0.23` is `≈ 0.065` in ratio |
| (2,−2) | −1.9013 | −1.9392 | same |
| **(0,0)** | **−1.5907** | **−1.5852** | **inconsistent**: `\|arch\| = 2.60`, so truncation moves the ratio by only `≈ 0.006` |
| **(1,1)** | **−0.7483** | **−1.0626** | **inconsistent** |

The assembly test corroborates the same split: against the Weil zero-side sum
over the first 200 zeros, the off-diagonal `(1,0)` gives
`2·M = 0.14257` vs `0.12991` (difference −0.0127, the right size and sign for
the unaccounted positive zero tail), whereas both diagonals `(0,0)` and `(1,1)`
are off by a near-constant `≈ 1.064`.

**Conclusion (precise, and more useful than a match).** The CCM matrix shares
the Weil form's pole and prime channels exactly (factor 2), and plausibly its
off-diagonal archimedean channel; the discrepancy is **localized to the diagonal
archimedean term**, which is exactly where R004's construction uses a separate
formula (`2γ_L(n) − 2β_L(n)`) rather than the divided difference used
off-diagonal. Note independently that R004's displacement identity
`[D,M] = g1ᵀ − 1gᵀ` leaves the diagonal completely unconstrained (`0 = 0`
there) — so the diagonal is precisely the part of `M` that neither the
displacement identity nor the Weil comparison pins down.

**Consequence for R003.** The bridge is *not* an identity as conjectured, but
the gap is now an identified, single-channel discrepancy rather than an unknown.
The sharpened R003 question is: **is there a choice of diagonal normalization
for which `M_{λ,N}` becomes exactly `½ ·` (Weil zero-side Gram in this basis)?**
If yes, the displacement identity becomes an exact statement about the explicit
formula (R004 ladder step **J5**).

**Remaining obstacles.** (i) the off-diagonal archimedean match needs a
higher-accuracy quadrature (tail-corrected or contour-deformed) to be asserted
rather than merely "consistent with"; (ii) `K_{nm}` is continuous but only
piecewise `C¹` (kink at `y = 0`), hence **not** a legal `C_c²` test for
`EF_lit` — formalization would need a mollified family and a limit.
**Status: LIVE, conjecture-as-stated REFUTED, sharpened question recorded.**

### R002-E — APERTURE-COHERENCE L²

**Definition.** `G_ij(A) = (1/A)∫₀^A F_i(a)conj(F_j(a))da` over the R001
filtered families; `P` = boundedness/PSD-limit.
**Collapse (decisive)** `[DERIVED]`. `paperFT`, `weilZeroFilter` and
`literatureRHS` are all **linear in the test** `[LEAN]`, so
`Σ_i ū_i F_i = F_{k_u}` for `k_u := Σ_i ū_i k_i`: the matrix is exactly the
scalar family indexed by the probe span, carrying no information beyond it.
And L²-subexponentiality still implies RH: splitting `∫₀^∞e^{−za}|F|` over unit
blocks and applying Cauchy–Schwarz,
`∫₀^∞ e^{−(Re z)a}|F| ≤ Σ_j e^{−(Re z)j}(∫_j^{j+1}|F|²)^{1/2} < ∞` for
`ε < Re z`, so the Laplace transform is holomorphic on `Re z > 0` and the
`ExposedPole` contradiction runs verbatim `[LEAN]` for the machinery.
Hence **P is fully RH-equivalent**, and its arithmetic side is the DR-004
dilution wall.
**Status: KILLED** (recorded as DR-006).

### R002-F — FULL-DIAGONAL MAJORIZATION

**Definition.** The `g_c`-diagonal channel retained by
`ZeroSide.RankTraceMult.sum_gc_eigenvalues_ge` `[LEAN]`, which carries the whole
diagonal `{m_j‖v_j‖²}` rather than the two numbers TightMult collapses it to.
**Failure mode.** `‖v_j‖²` varies with `δ` only at second order and is bounded
by the frame identity `Σ_kφ̂(γ−τ_k)² = aL²` independently of `δ`; the channel is
δ-insensitive at leading order `[DERIVED]`.
**Status: SECOND TIER (open, not promoted).**

---

## 2. Scalar-collapse audit (vs OBS-008)

| Cand. | Collapses to a known RH-equivalent scalar? | Grade |
|---|---|---|
| A | No *as a scalar* — it is a spectral sign, and the arithmetic leg is band-limited Weil positivity, not `ArithmeticSideSubexponential`. But by Weil's criterion the ∀(T,λ) family is again RH-equivalent (§5). | **RELOCATED, not reduced** |
| B | No (new scalar, outside TightMult quadruple) — but dies on detection precision. | independent kill |
| C | No; same masking structure as A, no gain. | second tier |
| D | Not an observable — an identity. Cannot collapse. | n/a |
| E | **Yes, fully** — linear-span collapse + Cauchy–Schwarz ⇒ OBS-008 verbatim. | **EQUIVALENT** |
| F | No; dies on δ-insensitivity. | independent kill |

No candidate is promoted on the basis of being "a different-looking RH". A is
promoted only for the **block-level separation theorem** it proves outright
(§4, §7), not for a claimed RH route.

---

## 3. Every-δ test with explicit scale bookkeeping (candidate A)

For a flat taper (`a = 1`), `Σ_k φ̂(γ−τ_k)² = aL²` `[LEAN]`; the derivative
analogue by the same Poisson/tight-frame argument `[DERIVED]` is
`Σ_k φ̂′(γ−τ_k)² = L∫v²φ(v)²dv ≈ L⁴/12`. Hence, for `δ ≪ 1/L`:

| quantity | scale (hat units `Ĝ = G/aL²`) |
|---|---|
| signal `2m‖y‖²/(aL²)` | `m δ²L²/(6a)` |
| bulk Rayleigh at `w = y/‖y‖` | `≈ 1/(λa)` (zero density `l/2π`, off-diagonal frame identity, Parseval `∫Φ′² = 2π∫v²φ⁴`) |
| tail `θ₀` | `≍ log T/T → 0` `[LEAN]` `Tail.prop_tail` |

**Visibility condition:** `m δ²L²·λ ≳ 6`, i.e. **`δL ≳ √(6/λ)`**. Since the
window must contain the zero (`γ ∈ [T,2T]`), `T ≍ γ` is forced and
`L = λ log(γ/2π)`: the only free parameter is `λ`.

**Numerical validation** `[NUM]` (`negindex_masking.py`, `l = 12`, flat taper,
synthetic on-line lattice + one off-line pair, exact `λ_min(Ĝ)`):

| λ | predicted threshold `δL` | observed |
|---|---|---|
| 0.5 | 3.46 | `λ_min > 0` still at `δL = 2.40` ✓ |
| 1.0 | 2.45 | crossover between `δL = 1.20` (`+0.594`) and `2.40` (`−0.268`) ✓ |
| 2.0 | 1.73 | **negative already at `δL = 0.24`** — see below |

**The λ > 1 regime (the substantive finding).** `d ≈ LT/2π` probes versus
`N ≈ lT/2π` zeros in the window: `d/N = λ`. For `λ > 1` the grid *oversamples*,
the on-line Gram is a sum of `N < d` rank-one terms, hence **PSD but singular**,
and any off-line pair whose `y` escapes the on-line span produces a strictly
negative eigenvalue. Numerically at `λ = 2`, `λ_min = −0.0000` at `δ = 0` and
`−0.0047` already at `δ = 0.01` (`δL = 0.24`). **In the oversampled regime the
every-δ test PASSES**: no δ-threshold, no exponent race — the detector becomes
a rank/kernel obstruction, exactly the "forbidden direction" form of `P` the
route brief asks for.

**The price, stated exactly.** `λ > 1` means `X = e^L = (T/2π)^λ > T`: the
prime side involves primes beyond the window height, precisely where
unconditional control is weakest. The difficulty is therefore *exchanged*, at
the explicit rate above, from "detect small δ" to "control a longer Dirichlet
polynomial". This exchange rate is the honest content of R002-A.

---

## 4. Online-double adversary (claim `R002_MULTI_PROBE_SEPARATION`)

The adversary is: distinguish a **tight off-line pair** from an **on-line
double**, given that OBS-001/`lemmaR_tight_two` `[LEAN]` proves the quadruple
`(tr, ‖·‖_F², on-line integer atoms, n₊)` is *simultaneously extremal* on both.

- On-line configurations (any multiplicities, including doubles and
  near-coincident zeros) contribute only `Σ c_j v_jv_jᵀ` with `c_j ≥ 0` and
  `v_j` **real** ⇒ PSD ⇒ `n₋ = 0` `[LEAN]` `onPart_posSemidef`,
  `rePart_posSemidef`, closure of PSD under sums.
- TightMult's extremal mock is `Q = diagonal(Sum.elim 0 (const c))`, `c > 0`
  ⇒ PSD ⇒ `n₋ = 0` `[LEAN]` `TightMult.Q_posSemidef`.
- A genuine off-line pair block is `2m(xxᵀ − yyᵀ)`; with
  `w := y − (⟨x,y⟩/‖x‖²)x ≠ 0` (i.e. `y ∉ ℝx`, Cauchy–Schwarz strict) one gets
  `⟨x,w⟩ = 0`, `⟨y,w⟩ = ‖w‖²`, hence **`wᵀBw = −2m‖w‖⁴ < 0`** `[DERIVED]`.

So `n₋` is a quantity that is `0` for every on-line world *and* for the tight
mock, and `≥ 1` for a visible off-line pair: **a theorem-relevant separation
not reducible to TightMult-visible data.** This is the promotable content, and
it is δ-uniform at block level (no threshold — the strictness is
`y ∉ ℝx`, not a size condition).

Caveat kept explicit: block-level separation is **not** a windowed-visibility
theorem (§3 masking) and **not** an RH route.

Gauntlet fixtures: this is the `G03` (on-line double) vs `G04`/`G05` (tight
off-line pair) discrimination, with `G05`'s fail-closed requirement respected —
the criterion returns "no separation" exactly when `y ∈ ℝx`.

---

## 5. Unconditional theorem inventory (named mechanisms)

| Candidate | Exact arithmetic statement needed | Named mechanism | Grade |
|---|---|---|---|
| A (block) | none — pure linear algebra | Sylvester/PSD closure `[LEAN]` | **PROVABLE NOW** |
| A (windowed, λ ≤ 1) | `∫\|W\|²ν_X ≥ −θ₀`, bandwidth `L ≤ l` | μ-part positivity + MV quadratic form (`MV.mv_hilbert` C = 26) + Chebyshev + `Tail.prop_tail` | partially unconditional; **insufficient** — masking makes the zero-side leg fail for `δ ≪ 1/L` |
| A (windowed, λ > 1) | same with `X > T` | none identified; MV's additive `Σn\|c_n\|²` penalty exceeds the target for `X > T` | **RH-equivalent by Weil's criterion in the ∀(T,λ) limit** |
| B | ternary Λ-correlation with relative precision `1/N` | none | dead |
| C | `lem_ends_nu` `[LEAN]` applies, but no gain | density-generic Frobenius transfer | second tier |
| D | *identity*, not an estimate — needs `EF_lit` for a `C¹`-BV test class | `EF_lit_zetaZeroConfig` `[LEAN]` + mollification | verification incomplete |
| E | subexponential off-diagonal Λ-pair form | none (DR-004 wall) | dead |
| F | — | — | second tier |

**Grade of A's terminal statement.** RH ⇒ `A ⪰ 0` ⇒ `λ_min(G̃) ≥ −θ₀` `[LEAN]`
machinery; conversely, positivity for all `(T, λ>1)` restores Weil's criterion,
hence RH. So A's terminal leg is **RH-equivalent** — but it is a *better-posed*
equivalent than R001's: no δ-threshold, no exponential race, and it is a
positivity statement about an explicitly given quadratic form rather than a
growth rate. Recorded as **OBS-009**.

---

## 6. Ranking

| | A | B | C | D | E | F |
|---|---|---|---|---|---|---|
| zero sensitivity | **high** (every-δ at λ>1) | very low | medium | n/a | high | low |
| unconditional controllability | low (λ>1) / partial (λ≤1) | none | low | n/a (identity) | none | low |
| non-equivalence risk | **high** (proved equivalent) | — | high | **none** | certain | high |
| formalization difficulty | **low at block level** | high | medium | medium-high (C¹ tests) | low | medium |
| CCM bridge compatibility | **high** (same object family) | low | medium | **maximal** | none | low |
| finite→infinite burden | low (finite matrices) | high | medium | **the whole point** | high | medium |
| **overall viability** | **1st (block-level)** | dead | 4th | **2nd (structural)** | dead | 5th |

---

## 7. Promotion decision

```
PROMOTE_ONE_CANDIDATE_TO_FORMALIZATION
```

**Promoted:** R002-A, **at block level only**. The discriminating theorem pair
was formalized in this same iteration (no terminal RH implication, per the
formalization rule) in `Zeta23/ExceptionalZero/ProbeGramNegativity.lean`,
sorry-free, `#print axioms` = `[propext, Classical.choice, Quot.sound]`:

1. **`dotProduct_pairBlock_orthoWitness`** — at the division-free witness
   `orthoWitness x y = ⟨x,x⟩•y − ⟨x,y⟩•x`, the exact pair block
   `c • xxᵀ − c • yyᵀ` has Hermitian form value exactly
   `−c·(gramDet x y)²`, where `gramDet x y = ⟨x,x⟩⟨y,y⟩ − ⟨x,y⟩²`;
   `dotProduct_pairBlock_orthoWitness_neg` gives strict negativity for `c > 0`
   and `gramDet x y ≠ 0`. (Cleaner than the normalized witness planned: no
   division, no `x ≠ 0` hypothesis, and the value is the squared Gram
   determinant — an explicitly computable transversality measure.)
2. **`dotProduct_nonneg_of_onLineCombination`** — every nonnegatively weighted
   sum of *real* rank-one blocks has nonnegative Hermitian form in every
   direction, via `ZeroSide.ZeroBlockData.posSemidef_smul_vecMulVec` `[LEAN]`.
3. **`not_onLineCombination_of_pairBlock`** (the separation corollary) — a
   visible off-line pair block is **not equal to any** such sum; on-line
   doubles and the `TightMult` mock `Q ⪰ 0` are of exactly that shape.

**Not promoted:** the windowed-visibility statement (masking, §3), the
arithmetic leg (§5, RH-equivalent — OBS-009), and every other candidate.
`C_RH` and `R001_PRIME_UPPER` remain `OPEN`. `R002_MULTI_PROBE_SEPARATION` may
be promoted **only** to the block-level statement actually proved, with its
`y ∉ ℝx` hypothesis explicit.

**Next after this iteration** (in priority order): complete the R002-D
archimedean verification — it is the only item in this document whose success
would produce an *identity* rather than a relocated estimate, and it is the
declared R003 bridge and R004-J5 seam.
