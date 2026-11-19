# Finite-core frame lower attempt: exact family redundancy and the weighted remaining target

11 November 2026. **DERIVED paper deductions. No repository edits, new Lean compilation, CI qualification, source-core identification theorem, or closing arithmetic estimate.** The source baseline remains PR299 `b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`.

The complete small-cutoff measurement family is quantitatively equivalent, up to subexponential factors, to a single full integer-completion measurement. This holds on every physical core, including the newly constructed source-defined core, without an invariance hypothesis. An explicit unconditional frame lower is available, but only at the nonclosing rate `exp(-T)`. The weaker weighted-target frame is stated with its exact physical metric. A conditional visible-zero test uses the **genuine complete source loading**, rather than inserting an unrelated exponential into the core.

## 1. Exact scope inherited from the source-core construction

Retain `T=L/2`, the actual affine reconstruction, its known offset, and the physically orthogonal core from `SOURCE_CORE_FRAME_COMPOSITION.md`. Its revised construction and `SOURCE_CORE_FRAME_REVIEW.md` now verify the exact physical operator identification and the historical near-null theorem's applicability at the paper/source-statement level. Inheriting that reviewed construction gives

\[
v_L\in\mathcal K_L,\qquad
\|Z-v_L\|_{2,[0,T]}\le d_L,\qquad d_L\le e^{-3L/4}
\tag{1}
\]

eventually, with dimension `O(L^3 log L)+1`. Its actual loading and bounded affine offset are retained. This uses the documented nested physical compression and the original near-null theorem's legal-carrier scope, not matching matrix names. It does not turn the historical paper theorem into new compiled authority.

Choose an orthonormal physical basis `f_1,...,f_r` of this same function space. Thus `v_L=sum u_a f_a` has `||v_L||^2=||u||^2`. All filters below act on the **complete output functions before any projection**, not on a guessed invariant coordinate subspace.

The prescribed source-only cutoffs satisfy `2<=y_j<=Y`, where

\[
Y=Y_T=\left\lfloor\frac{T}{8\log(T+2)}\right\rfloor,
\quad w_j\ge0,\quad\sum_jw_j=1.
\]

The current complete-source budget, with outside-core amplification already paid, is

\[
u^*\Gamma_Lu=\sum_jw_j\|N_{y_j}v_L\|_2^2
\le\mathcal B_T^2
:=2\|U\|_2^2e^{4\sqrt Y}+8e^T d_L^2=e^{o(T)}.
\tag{2}
\]

Here `Gamma_L(a,b)=sum_j w_j <N_(y_j)f_a,N_(y_j)f_b>`, and the norm is on the full prefix. No assertion about a canonical ground eigenray or reciprocal input has been added.

If r=0, (1) immediately gives `E_Z(T)<=d_L^2`; no minimum eigenvalue is defined in that case. For the actual source this degeneracy cannot persist at large apertures: the isolated first prime pulse gives

\[
\int_{\log2-S}^{\log2+S}|Z(t)|^2dt
=\frac{(\log2)^2}{2}\|h\|_2^2>0,
\tag{3}
\]

because `log(3/2)>2S` excludes every other integer pulse from that interval. Thus a valid approximation with `d_L->0` has r>=1 eventually. This is only a fixed positive lower, not the missing growth upper.

## 2. Every low-prime factor and its inverse have subexponential cost

On `L2[0,T]` use zero extension before zero and the exact causal shifts

\[
T_pf(t)=p^{-1/2}\mathbf1_{t\ge\log p}f(t-\log p).
\]

They commute, and `||T_p||<=p^(-1/2)<1`. The inverse `(I-T_p)^(-1)` is its complete causal geometric series. On a fixed prefix that series terminates; its norm is at most `(1-p^(-1/2))^(-1)`. No terminal output or early history is removed by this inversion.

For `1<=y<=Y`, with the convention `N_1=N` for the full integer operator, the exact finite-prefix identities are

\[
N_Y=\prod_{y<p\le Y}(I-T_p)N_y,
\qquad
N_y=\prod_{y<p\le Y}(I-T_p)^{-1}N_Y.
\tag{4}
\]

Every prime-power cofactor in the inverse product is retained. There are finitely many prime factors in these products, so no infinite Euler product at a critical-strip point is involved.

Put `c0=(1-1/sqrt(2))^(-1)`. Elementary inequalities give

\[
\prod_{p\le Y}(1+p^{-1/2})\le e^{2\sqrt Y},
\qquad
\prod_{p\le Y}(1-p^{-1/2})^{-1}\le e^{2c_0\sqrt Y}.
\tag{5}
\]

The second follows from `-log(1-x)<=x/(1-x)` and `x<=1/sqrt(2)`; both use `sum_(n<=Y)n^(-1/2)<=2sqrt(Y)`. Therefore, for **every** causal prefix input f,

\[
e^{-2\sqrt Y}\|N_Yf\|_2
\le\|N_yf\|_2
\le e^{2c_0\sqrt Y}\|N_Yf\|_2.
\tag{6}
\]

Comparison directly with the full integer operator is also exact:

\[
e^{-2c_0\sqrt Y}\|Nf\|_2
\le\|N_yf\|_2
\le e^{2\sqrt Y}\|Nf\|_2.
\tag{7}
\]

All constants are independent of the number of selected cutoffs and of their weights. Since `sqrt(Y)=o(T)`, these losses are subexponential on the actual horizon scale, not merely on the aperture scale.

## 3. The entire finite frame is equivalent to one measurement

Let `H_Y` and `H_N` be the physical core Gram matrices formed with `N_Y` and N respectively. Applying (6)--(7) to `f=sum x_a f_a`, then averaging the squared inequalities, proves the Loewner comparisons

\[
\boxed{e^{-4\sqrt Y}H_Y\preceq\Gamma_L
\preceq e^{4c_0\sqrt Y}H_Y,}
\tag{8}
\]

\[
\boxed{e^{-4c_0\sqrt Y}H_N\preceq\Gamma_L
\preceq e^{4\sqrt Y}H_N.}
\tag{9}
\]

The core may depend on L and on the actual source. No filter is assumed to preserve that core: (4)--(7) compare full output norms, which is enough for the matrix statements. There is no intermediate compression that loses filtered output.

It follows that an every-positive-rate lower for this full family is equivalent, at the same cofinal apertures, to such a lower for a single `N_Y` or N measurement. The same statement holds only on the actual loading if that weaker supplier is used. To pass between them, fix the desired exponent first, apply the available inequality with a smaller exponent, and then enlarge the threshold until the explicit `exp(O(sqrt(Y)))` factor is absorbed. The horizon is not reselected independently for different filters.

This is a substantive restriction on the proposed frame strategy. Increasing the number of these low-prime cutoffs does not create an exponential-scale improvement over the one genuine equation `NZ=U`. It may improve finite constants or conditioning, but the entire missing closing-rate lower survives in that single measurement.

For completeness, the true single-measurement core budget is also paid directly:

\[
\|Nv_L\|_2^2
\le2\|U\|_2^2+8e^T d_L^2.
\tag{10}
\]

This uses `NZ=U` and `||N||<=2exp(T/2)` on the complete prefix, so the same outside-core error is charged. The nonunit delays of N include all integers, while N_Y retains only rough integers; (9) precisely quantifies the low-prime distinction.

## 4. A quantitative unconditional lower, at the wrong rate

The exact finite-prefix inverse of N_y is the complete rough Möbius operator

\[
M_yf(t)=\sum_{\substack{d\le e^T\\P^-(d)>y}}
\mu(d)d^{-1/2}\mathbf1_{t\ge\log d}f(t-\log d),
\quad M_yN_y=N_yM_y=I.
\]

The unit is included. Every product cutoff is causal and identical on both sides. The elementary absolute bound gives

\[
\|M_y\|_{2\to2}
\le\sum_{d\le e^T}\frac{|\mu(d)|}{\sqrt d}
\le2e^{T/2}.
\tag{11}
\]

Thus, on all prefix inputs and therefore on any physical core,

\[
\|N_yf\|_2^2\ge\tfrac14e^{-T}\|f\|_2^2,
\qquad
\boxed{\Gamma_L\succeq\tfrac14e^{-T}I_r.}
\tag{12}
\]

This is more than bare finite invertibility. It is an explicit unconditional lower, but combining it with (2) yields only `E_Z(T)<=exp(T+o(T))`. It does not supply `exp(-eta T)` for every eta>0. This is the best lower obtained by the present absolute inverse estimate, not a claim that no stronger arithmetic estimate could exist.

The positivity of the coefficients of N_y does not improve (12) through entrywise ordering: its output norm contains all signed correlations of f and its delays. Likewise positivity of the frame matrix does not control its smallest eigenvalue at the requested rate. The finite dimension alone does not price the inverse in (11).

There is a second exact but unpriced observation: N_Y equals the identity before its first nonunit delay. If `tau=min(T,log p_next(Y))`, then

\[
\|N_Yf\|_{2,[0,T]}^2\ge\|f\|_{2,[0,\tau]}^2.
\tag{13}
\]

On the core, this supplies an early-interval Gram lower. To turn it into a global or weighted lower requires a quantitative observability estimate for that **actual** core. No such estimate follows merely from its rank. Its known affine offset, reconstruction tails, and completion projection cannot be replaced by an arbitrary bandlimited or analytic class to assert an unproved continuation cost.

## 5. The weaker weighted physical frame target

The original response target does not require unweighted energy. Fix the same `0<gamma<1` as in `WEIGHTED_TARGET_TRANSFER.md`, and define the physical weighted core Gram matrix

\[
G_{\gamma,L}(a,b)=\int_0^T e^{-\gamma(T-t)}
\overline{f_a(t)}f_b(t)dt.
\tag{14}
\]

This is not the coordinate Gram matrix from a nonorthonormal native basis. Here the basis is already orthonormal for the unweighted physical norm, and

\[
e^{-\gamma T}I_r\preceq G_{\gamma,L}\preceq I_r,
\quad
u^*G_{\gamma,L}u=W_\gamma(v_L).
\tag{15}
\]

The error satisfies `||Z-v_L||_(gamma,T)<=d_L`; every filter measurement still uses the full prefix. A sufficient actual-loading estimate is

\[
\boxed{u_L^*\Gamma_Lu_L\ge
c_{h,\gamma,\eta}e^{-\eta T}
u_L^*G_{\gamma,L}u_L}
\tag{16}
\]

at common cofinal apertures for every requested eta>0, with constants fixed first. The stronger all-core version is `Gamma_L >= c exp(-eta T)G_(gamma,L)`. Its exact quantity is the least generalized eigenvalue of the pair `(Gamma_L,G_(gamma,L))`, not the Euclidean eigenvalue of one matrix alone.

Under (16), the paid measurements give

\[
W_\gamma(Z)\le
2c_{h,\gamma,\eta}^{-1}\mathcal B_T^2e^{\eta T}+2d_L^2,
\qquad
A_Z(T)^2\le W_\gamma(Z)/(1-\gamma).
\tag{17}
\]

The smaller exponent is chosen first and the source-fixed thresholds are enlarged to absorb the `exp(o(T))` measurement budget. This preserves the original cofinal order of quantifiers.

The family comparisons (8)--(9) remain valid with this denominator. Thus (16), or its all-core form, is equivalent at the every-positive-rate scale to the same relative estimate for H_Y or H_N. All prehistory remains in the measured numerator. A small weighted Gram eigenvalue is not permission to delete early history before filtering.

If `lambda_0` is the unweighted minimum Rayleigh quotient and `lambda_gamma` the weighted one, the only automatic comparison from (15) is

\[
\lambda_0\le\lambda_\gamma\le e^{\gamma T}\lambda_0.
\tag{18}
\]

The unconditional estimate (12) gives `lambda_gamma>=exp(-T)/4`; it does not automatically improve to `exp(-(1-gamma)T)/4`. The weighted target is genuinely weaker, but its required relative lower still needs arithmetic input.

## 6. The genuine source tests the lower, without inserting an arbitrary mode

Assume only for this compatibility test that an actual visible off-line zero with displacement delta>0 exists. The inherited multiplicity-correct centered-jet theorem gives, for the unchanged **complete** Z,

\[
A_Z(T)\ge c_\rho e^{\delta T}
\]

at every sufficiently late real horizon. Weighted Cauchy therefore implies

\[
W_\gamma(Z)\ge(1-\gamma)c_\rho^2e^{2\delta T}.
\]

Using the already-paid physical error in (1), the actual loading has

\[
u_L^*G_{\gamma,L}u_L\ge c'_{\rho,\gamma}e^{2\delta T}
\]

eventually, whereas its measurement numerator still obeys (2). Consequently

\[
\boxed{\frac{u_L^*\Gamma_Lu_L}{u_L^*G_{\gamma,L}u_L}
\le C_{\rho,\gamma}e^{-2\delta T+o(T)}.}
\tag{19}
\]

The all-core least generalized eigenvalue is at most this actual-loading quotient. This test uses the genuine source with its complete complement and existing zero lower; it does not assert that a pure exponential belongs to the source core, select a dominant zero, or promote a hypothetical zero into an observed fact.

It follows that the source-defined finite core has not automatically removed the admissible obstruction: if the hypothetical zero existed, the actual source loading itself would exhibit the exponentially small relative frame value. Proving (16) independently would exclude it, but the rank estimate, tiny outside-core error and stable low-prime factors do not prove that lower.

This is not an equivalence between RH and the all-core bound. The latter is stronger and may be obstructed by nongenuine core combinations. The actual-loading inequality is the appropriately narrower arithmetic target.

## 7. Result and remaining single-measurement inequality

The useful new information is the exact uniform reduction

\[
\text{normalized full rough family}
\quad\asymp_{\exp(o(T))}\quad
\text{one full integer-completion measurement},
\]

valid on the actual source core and for the weighted target. Every low-prime inverse factor is harmless at this exponent scale. The remaining inverse over the unresolved arithmetic frequencies is not priced by that fact.

After the legitimate affine reconstruction and source-core approximation, one can therefore focus on the precise actual-loading supplier

\[
\boxed{\|Nv_L\|_{2,[0,T]}^2\ge
c_{h,\gamma,\eta}e^{-\eta T}
\int_0^T e^{-\gamma(T-t)}|v_L(t)|^2dt}
\tag{20}
\]

for every requested eta>0 at common cofinal apertures. The numerator is already bounded by the complete actual integer drive and the paid core error. Its missing lower relative to the weighted source norm is not established here.

**Outcome:** exact family redundancy, an unconditional but nonclosing quantitative lower, a correctly weaker weighted frame target, and a genuine-source conditional obstruction test. No independent all-positive-rate lower was proved. **Step 4 and RH remain OPEN.**

### Provenance and scope

- `SOURCE_CORE_FRAME_COMPOSITION.md` and `SOURCE_CORE_FRAME_REVIEW.md`: explicit affine reconstruction, verified paper-level physical operator identification, source-only core and full outside-core amplification. The reviewed composition has SHA-256 `0a784aa0204dd66c5cf3dacc5b7fd406dc10214e7c7057f6283420161ddbe406`.
- `FILTER_FAMILY_ATTEMPT.md`: genuine complete filtered-output bounds and actual-source simultaneous compensation.
- `../step4-signed-response-round2-2026-11-10/OUTPUT_RECOVERY.md`: paid output recovery, physical metric and the retained literal pole direction.
- `../step4-complete-residual-round4-2026-11-10/WEIGHTED_TARGET_TRANSFER.md` and `PAIRING_WEIGHTED_REVIEW.md`: unchanged A_Z consumer, weighted energy, all-power transfer and cofinal quantifiers.
- `../step4-complete-residual-round4-2026-11-10/COMPLETE_RESIDUAL_RECURRENCE.md`: complete rough Möbius inverse and finite causal product conventions.

All comparisons proved here are finite-prefix operator algebra and explicit norm estimates. The carrier identification has been checked in the cited source-core review; these comparisons do not upgrade the inherited paper near-null proof to fresh formal authority.
