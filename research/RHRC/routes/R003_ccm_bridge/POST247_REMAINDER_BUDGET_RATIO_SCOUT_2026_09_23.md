# Post-#247 remainder/budget ratio scout — repaired interpretation after PR #249

Status: **EXPERIMENTAL SIGNAL / RH OPEN**

Script: `post247_remainder_budget_ratio_scout.py`  
Data: `fixtures/post247_remainder_budget_ratio_v1.json` (schema `POST247_REMAINDER_BUDGET_RATIO_SCOUT_v1`)  
Original scout base: `070c0a08` (PR #247 merged).  
Merged research PR: #249, head `1758ed7fd1fd0bbae6b6929b3793fa8e97288b55`, merge `caec6773664458bde0eac55cf1ad60446c385efd`.

The PR #249 fixture is unchanged by this interpretation repair. This file tightens the claims to exactly what the finite Arb experiment supports.

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

For each `(L, K)`, restricted to the even and odd boundary-flat carriers, the scout computes the inertia of `A` and `B`, the spectrum of `E`, and the worst-case ratio `max B/A` with slack `min E/A`.

It also applies a **synthetic zero-side perturbation control**. The real canonical prime/Euler-product data are left fixed while the remainder channel receives the local explicit-formula contribution of an extra zero quadruplet `½ ± δ ± iγ`.

### Planted-control semantics

| Preserved by the control | Not preserved / not claimed |
|---|---|
| real canonical matrix before perturbation | modified Euler product consistent with the planted zeros |
| exact boundary-flat/parity carriers | modified von Mangoldt sequence generating the planted zeros |
| zero-quartet symmetry | existence of an alternate zeta/L-function |
| local explicit-formula zero contribution | global prime/zero consistency of a genuine explicit formula |

The planted object is a **zero-side perturbation falsifier**, not a globally self-consistent alternate zeta function.

## Method and validation

- All channels are Arb enclosures.
- Exact integer bases of the even and odd boundary-flat carriers are used.
- A sign counts only when its Arb enclosure excludes zero.
- The pole closed form agrees with `G-T` to at most about `5e-75` on the checked points.
- The Arb canonical energy agrees with the independent repository float builder to about `5e-15` relative.
- Cross-parity blocks vanish to about `3e-70`.
- The planted-term sign is checked against the first 300 true zeros; mean error is about `0.022` with the chosen sign versus `0.30` with the sign flipped.

## Results

96 real-data points, 108 planted cases, and 18 sign-change searches were frozen. Every reported real-data sign is certified.

### 1. Positive on the tested real grid

`A` and `B` are positive definite on every tested carrier and `E=A-B` is certified positive at all 96 real points.

Across the fixture:
- `A` eigenvalues are approximately in `[2.20, 10.32]`;
- `B` eigenvalues are approximately in `[0.331, 5.35]`;
- the smallest certified `λ_min(E)` is about `3.49e-82`.

Thus `B ⪯ A` holds on this finite grid.

### 2. Extremely small finite-grid slack; no asymptotic decay law is claimed

Minimum slack `min_x E(x)/A(x) = 1 - max_x B(x)/A(x)`:

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

At the **tested prime-free aperture `L=1/2`**, the slack remains at the percent level through `K=20`. At several larger tested apertures it becomes extraordinarily small as `K` grows. The fixture establishes no exponential, super-exponential, or other asymptotic rate, and it does not establish a uniform statement over all `0<L<log 2`.

### 3. Sharp coarse-grid separation near the first-zero resolution scale, not an exact switch

Using the nominal scale `2πK/L`:

- 36 sampled points below `γ₁≈14.134725` have `λ_max(E)≤0.1522`;
- 60 sampled points at or above `γ₁` have `λ_max(E)≥0.8998`.

The nearest sampled scales are `4π≈12.56637` below and `14.36157` above, leaving a substantial unsampled interval. The fixture therefore does not locate an exact transition at `γ₁`.

Also, `2πK/L` is a **nominal resolution scale**, not a hard Fourier cutoff theorem for the localized compactly supported tests.

### 4. Planted low-rank sign structure

For the 18 on-line cases (`δ=0`), the increment is rank-one PSD in each parity block and none becomes bad.

For the 90 off-line cases:
- the increment has signature `(1,1)` in each parity block;
- 82/90 tested states are certified bad;
- all 8 misses occur at `γ=20, K=6`;
- at `K=12`, every tested off-line plant is detected;
- for small `δ`, the negative eigenvalue shows the expected leading-order `O(δ²)` behavior. The runtime regression compares `δ=10^-3` and `10^-2`; no exact global scaling law is claimed.

### 5. Certified sign-change brackets, not globally minimal deltas

The geometric search returns `delta_certified_not_bad < delta_certified_bad` with relative bracket width below `1e-9` for each frozen search.

| (L, K) | γ = 5 | γ = 10 | γ = 20 |
|---|---|---|---|
| (2, 6) | 7.2e-6 | 2.6e-5 | 2.8e-2 |
| (2, 12) | 4.4e-9 | 1.3e-8 | 3.2e-6 |
| (3, 6) | 3.6e-8 | 7.8e-7 | 4.7e-2 |
| (3, 12) | 5.0e-14 | 3.3e-13 | 3.2e-9 |
| (4, 6) | 1.6e-9 | 1.1e-6 | 1.9e-1 |
| (4, 12) | 3.4e-17 | 7.1e-16 | 3.7e-8 |

These are certified sign-change brackets found by the search. They are **not globally minimal deltas**, because monotonicity of the lowest eigenvalue in `δ` was not proved.

## Interpretation

1. **The #246 split is numerically extremely sharp.** Order-one `A` and `B` can differ by less than `1e-81` on a legal extremal direction. A proof that introduces a fixed multiplicative loss cannot certify the exact sign from that margin alone.
2. **This does not rule out PNT-strength, zero-density, or other analytic-number-theory methods as classes.** It rules out only the inference that a coarse fixed-slack estimate is enough on the observed states.
3. **The planted control is a useful falsifier.** The tested on-line and off-line quartets have qualitatively different low-rank signatures.
4. **The first-zero-scale signal needs a dense follow-up.** A fixed-`K`, dense-`L` sweep around `2πK/L≈γ₁` is the fastest way to test whether the coarse separation localizes near the first zero.
5. **Exact structure remains the strongest lead.** Carrier/interlacing identities, exact threshold updates, or exact positivity/factorization mechanisms are worth testing. None is proved here.

## Nonclaims

- Arb enclosures on a finite `(L,K)` grid are not Lean theorem authority.
- Positivity at finitely many `(L,K)` is not RH.
- The finite-grid slack values establish no asymptotic decay rate in `K`.
- `2πK/L` is a nominal resolution scale here, not a hard Fourier cutoff theorem.
- The sign-change brackets are not globally minimal deltas; monotonicity in `δ` is not proved.
- The planted object is not a globally self-consistent alternate zeta function.
- The experiment does not rule out PNT-strength, zero-density, or other analytic methods.
- No slack, ratio, sign-change bracket, or planted sensitivity here is a theorem about all `(L,K)`.
- **RH remains OPEN.**

## Reproduce

```text
pip install -r research/RHRC/routes/R003_ccm_bridge/requirements.txt
python research/RHRC/routes/R003_ccm_bridge/post247_remainder_budget_ratio_scout.py --out out.json
python research/RHRC/routes/R003_ccm_bridge/post247_remainder_budget_ratio_scout.py --quick
```
