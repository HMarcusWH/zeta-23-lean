# Post-#247 remainder/budget ratio scout — results

Status: **EXPERIMENTAL SIGNAL / RH OPEN**

Script: `post247_remainder_budget_ratio_scout.py`
Data: `fixtures/post247_remainder_budget_ratio_v1.json` (schema `POST247_REMAINDER_BUDGET_RATIO_SCOUT_v1`)
Base: `main` at `070c0a08` (PR #247 merged).

This is research evidence only. Lean, CI, and `CLAIM_REGISTRY.json` remain the theorem authority.

## What was measured

PR #246 proved, for every `L > 0`, `K`, and every vector `x`:

```text
canonicalSourceChannelEnergy L K x = -canonicalPrimeRemainderEnergy L K x - canonicalPrimeFreeBudget L K x
```

It also proved that nonnegativity on all boundary-flat carriers at all `(L, K)` is equivalent to RH. The scout writes:

- `A := -E_R`: minus the energy of `R(x) = Σ_{n≤x} Λ(n)/√n − 2√x`.
- `B := B_free`: pole tail plus reduced archimedean channels plus the scalar term.
- `E = A − B`: the canonical energy.

RH ⇔ `B(x) ≤ A(x)` on every boundary-flat carrier.

For each `(L, K)`, restricted to the even and odd boundary-flat carriers, the scout computes:

- the inertia of `A` and `B`;
- the spectrum of `E`;
- the worst-case ratio `max B/A` and its slack `min E/A`.

It does the same for a **planted-zero control**. There, `R(x)` gains the explicit-formula term `−Σ x^{ρ−½}/(ρ−½)` of an extra zero quadruplet `½ ± δ ± iγ`:

- `δ = 0` plants an on-line double pair;
- `δ > 0` plants an off-line pair.

### Method

- **Ball arithmetic.** All channels are Arb enclosures, built on `canonical_source_arb.py`.
  - The archimedean integrals use Arb's validated integrator.
  - `G`, `T`, and the planted term are closed forms.
  - The prime channel is an exact finite sum over a certified cutoff cell.
- **Exact carriers.** Carriers use exact integer bases of the even and odd boundary-flat subspaces (moments 0, 1, 2 vanish), orthonormalized by an Arb Cholesky factor.
- **Certified signs.** Eigenvalues are `arb_mat.eig` enclosures. A sign counts as certified only if its enclosure excludes 0. Precision doubles from 256 bits up to 4096 until every sign is certified.

### Validation

- **Pole channel.** The closed form of `pole_component` equals `G − T` to ≤ 5·10⁻⁷⁵ at every point.
- **Float cross-check.** The Arb canonical energy matches the repository float builder to 5·10⁻¹⁵ relative.
- **Parity blocks.** The cross-parity block vanishes (enclosures ≤ 3·10⁻⁷⁰).
- **Sign convention of the planted term.** Using the first 300 true zeros in the same explicit formula reproduces `R(x)`. The mean error is 0.022; flipping the sign gives 0.30.

## Results

96 real-data points (`L ∈ {½, ¾, 1, 3/2, 2, 5/2, 3, 4, 5, 6, 7, 8}`, `K ∈ {3, 4, 6, 8, 10, 12, 16, 20}`), 108 planted cases, 18 threshold searches. Every sign is certified.

### 1. Both families are positive definite; the energy is positive everywhere

- `A` and `B` are each positive definite on every carrier. Their eigenvalues lie in roughly [0.3, 10].
- `E` is certified positive at all 96 points.

So the ratio `B/A` is well defined everywhere tested, and `B ⪯ A` holds on the whole grid.

### 2. The worst-case ratio is 1 up to a super-exponentially small slack

Minimum slack `min_x E(x)/A(x) = 1 − max_x B(x)/A(x)`, taking the minimum over parities:

| L \ K | 3 | 6 | 12 | 20 |
|---|---|---|---|---|
| ½ (no primes) | 3.4e-2 | 1.8e-2 | 1.2e-2 | 1.0e-2 |
| ¾ | 5.2e-3 | 9.1e-4 | 3.1e-4 | 2.2e-4 |
| 1 | 1.2e-4 | 1.1e-5 | 1.9e-6 | 7.9e-7 |
| 3/2 | 7.4e-10 | 1.7e-12 | 1.2e-14 | 9.2e-15 |
| 2 | 2.9e-10 | 1.6e-16 | 1.4e-23 | 1.9e-28 |
| 3 | 1.1e-13 | 3.1e-21 | 1.3e-33 | 1.2e-46 |
| 4 | 1.6e-16 | 1.9e-24 | 1.4e-40 | 1.0e-57 |
| 6 | 1.4e-17 | 5.3e-29 | 1.9e-49 | 1.1e-72 |
| 8 | 2.8e-20 | 4.5e-32 | 1.3e-55 | 6.8e-83 |

- **Prime-free regime `L < log 2`.** The slack is about 1% and decreases only slowly with `K`. This is the regime of Connes–Consani archimedean positivity.
- **Once several primes enter (`L ≥ 2`).** The slack collapses super-exponentially in `K`.
- **The two families cancel almost exactly.** At `L = 8`, `K = 20`, the prime-remainder energy and the prime-free budget are each about 3, yet they agree to 83 digits on the worst carrier.
- **No uniform gap.** The data show no margin strictly below 1 for the ratio.

### 3. The difference of the two families switches on exactly at the first zeta zero

Take the carrier bandwidth `2πK/L`:

- All 36 points with bandwidth below `γ₁ = 14.1347` have `λ_max(E) ≤ 0.15`. Here `A ≈ B` in *every* direction; at `L = 8`, `K = 12` they agree to 7 digits across the whole carrier.
- All 60 points with bandwidth at or above `γ₁` have `λ_max(E) ≥ 0.90`. The first point past the line (bandwidth 14.36) has `λ_max(E) = 6.4`.

This is what the explicit formula predicts: `E` is the zero-side sum `Σ_ρ |ĝ(ρ)|²`. It stays small until the carrier can resolve the first zero.

### 4. The planted control fires with the predicted structure and extreme sensitivity

**On-line plant (`δ = 0`), 18 cases.**
- The energy increment is rank-one positive semidefinite in each parity block.
- Positivity is never broken.

**Off-line plant (`δ > 0`), 90 cases.**
- The increment has signature (1, 1) in each parity block: one positive and one negative direction, as for a hyperbolic pair.
- Its negative eigenvalue scales as `δ²`.
- 82 of 90 states are certified bad. The 8 misses are all at `γ = 20` with `K = 6`, where the carrier bandwidth (9.4 to 18.8) is below the planted ordinate. At `K = 12` every off-line plant is detected.

**Detection thresholds** (smallest `δ` certified bad, bracketed to 12 digits):

| (L, K) | γ = 5 | γ = 10 | γ = 20 |
|---|---|---|---|
| (2, 6) | 7.2e-6 | 2.6e-5 | 2.8e-2 |
| (2, 12) | 4.4e-9 | 1.3e-8 | 3.2e-6 |
| (3, 6) | 3.6e-8 | 7.8e-7 | 4.7e-2 |
| (3, 12) | 5.0e-14 | 3.3e-13 | 3.2e-9 |
| (4, 6) | 1.6e-9 | 1.1e-6 | 1.9e-1 |
| (4, 12) | 3.4e-17 | 7.1e-16 | 3.7e-8 |

At `(4, 12)`, an extra zero displaced by `3·10⁻¹⁷` from the line at height 5 produces a certified negative canonical energy.

## Interpretation

1. **Dividing the two families returns the zeros.** `B` is the common prime-free structure. By the explicit formula, what remains after dividing it out, `A − B`, is the zero-side sum `Σ_ρ |ĝ(ρ)|²` (DERIVED, not separately formalized here). Finding 3 is the numerical fingerprint of this: the difference switches on at `γ₁`. So the ratio is `1 − (zero-side sum)/A`, and `ratio ≤ 1` is RH.
2. **There is no error budget.** The worst-case ratio tends to 1 super-exponentially, so any proof of `B ⪯ A` has to be exact.
   - An inequality that loses even a factor `1 + 10⁻⁸⁰` fails already at `(8, 20)`.
   - Bounds on `R(x)` of analytic-number-theory type (PNT-strength or zero-density-strength) cannot supply this.
   - What could supply it is a structural identity: an exact Cauchy–Schwarz or positivity statement in which the slack is a sum of squares.
3. **The finite forms are sharp detectors.** They are not "almost RH" statements with room to spare. The real data sit at certified positive energy with near-zero slack, and a planted off-line zero at distance 10⁻¹⁷ breaks positivity.
4. **Only the prime-free regime has a real margin.** `L < log 2` shows about 1% slack. Once primes enter, the margin disappears. This is consistent with the one proved positivity result, which is archimedean.

## Nonclaims

- Arb enclosures on a finite `(L, K)` grid are not Lean theorem authority.
- Positivity at finitely many `(L, K)` is not RH.
- The planted model is a synthetic control, not a statement about ζ.
- No slack, ratio, or threshold here is a theorem about all `(L, K)`.
- **RH remains OPEN.**

## Reproduce

```text
pip install -r research/RHRC/routes/R003_ccm_bridge/requirements.txt
python research/RHRC/routes/R003_ccm_bridge/post247_remainder_budget_ratio_scout.py --out out.json
python research/RHRC/routes/R003_ccm_bridge/post247_remainder_budget_ratio_scout.py --quick   # reduced grid
```

The full run takes about 15 minutes on one core.
