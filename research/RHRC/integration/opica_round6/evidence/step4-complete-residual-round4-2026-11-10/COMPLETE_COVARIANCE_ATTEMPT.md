# Complete clipped covariance: exact coprime reduction and centered prime-pair discrepancy

11 November 2026. **DERIVED paper investigation. No new Lean compilation, CI qualification, independent every-positive-rate upper, or Step 4 closure.** The inspected mathematical baseline remains PR299 `b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`, tree `d0a6b1ad78523c23834eb01f57f4910a22e30d3b`. No repository files were edited in this pass.

The substantive new result is an actual-source asymptotic for both signs of the **complete clipped covariance**. Each sign has the same strictly positive main term of order `exp(T)`. It is not a selected prime block and does not discard the terminal collar. A fixed two-variable kernel removes the deterministic continuum exactly and specifies the remaining arithmetic discrepancy, including the accuracy required for closure.

## 1. Unchanged source and complete field

Keep the fixed real even source

\[
h=((D^2-1/4)q)*((D^2-1/4)q),\qquad
\operatorname{supp}h\subset[-S,S],\quad S=1/2048.
\]

It is nonzero and smooth, and its two half-pole moments vanish. In particular

\[
\int e^{-v/2}h(v)\,dv=\int e^{v/2}h(v)\,dv=0.                 \tag{1}
\]

All prime powers remain in

\[
Z(t)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}h(t-\log n).
\]

There is no pulse before `log(2)-S>0`. The actual equation `a*Z=W` and fixed `||W||_2=C_W` remain available; no global `L2` hypothesis on Z or inverse bound is imposed.

Define

\[
k_T(u,v)=\int_0^T h(t-u)h(t-v)\,dt,\qquad
N_T=\lfloor e^{T+S}\rfloor.
\]

Exactly,

\[
E_Z(T)=\int_0^T|Z(t)|^2dt=D_T+O_T,                         \tag{2}
\]

\[
D_T=\sum_{n\le N_T}\frac{\Lambda(n)^2}{n}k_T(\log n,\log n),
\quad
O_T=\sum_{\substack{m,n\le N_T\\m\ne n}}
\frac{\Lambda(m)\Lambda(n)}{\sqrt{mn}}k_T(\log m,\log n).
\]

The off-diagonal is ordered, so no additional factor two is suppressed. An elementary Chebyshev bound `psi(x)<=A x` gives, with source-fixed constants,

\[
0\le D_T\le\|h\|_2^2\sum_{n\le N_T}\frac{\Lambda(n)^2}{n}
\le C_h(1+T)^2.                                           \tag{3}
\]

Indeed `Lambda(n)^2<=log(N_T)Lambda(n)` and partial summation gives `sum Lambda(n)/n<=C(1+log N_T)`. The weaker earlier cubic bound also suffices.

## 2. The gcd grouping terminates exactly at coprime prime powers

If `Lambda(m)Lambda(n)!=0`, `m!=n`, and `gcd(m,n)>1`, the two integers are powers of the same prime: `m=p^j,n=p^k`, `j!=k`. Therefore

\[
|\log m-\log n|\ge\log2>2S,
\]

and their packets have no overlap, even before clipping. Hence

\[
\boxed{O_T=\sum_{\substack{m\ne n\le N_T\\(m,n)=1}}
\frac{\Lambda(m)\Lambda(n)}{\sqrt{mn}}k_T(\log m,\log n).}  \tag{4}
\]

This is an exact arithmetic simplification. It does not create a sparse interaction graph: distinct ordinary primes in a fixed multiplicative neighborhood are already coprime, and their number grows with the scale.

For completeness, higher prime powers can be compared with the ordinary-prime field without dropping their cross terms. Put `Z=P+Q`, where P uses only primes and Q uses every power of exponent at least two. Chebyshev's estimate gives

\[
|Q(t)|\le \|h\|_\infty e^{-(t-S)/2}
\sum_{2\le j\le(t+S)/\log2}\vartheta(e^{(t+S)/j})
\le C_h\bigl(1+(1+t)e^{-t/6}\bigr)\le C'_h.              \tag{5}
\]

An empty exponent range contributes zero; bounded initial times are included in the constant. For each fixed `epsilon>0`,

\[
E_Z(T)\le(1+\epsilon)E_P(T)+(1+\epsilon^{-1})(C'_h)^2T,    \tag{6}
\]

and the converse inequality holds with Z and P exchanged. This pays the correction by a norm inequality, with its mixed term retained. It does not assert that the mixed covariance is independently polynomial. The argument below continues to use the **full Mangoldt measure**, so no prime-power compatibility substitution is needed.

## 3. A fixed clipped kernel for every observation scale

Set `X=exp(T)` and introduce the positive rescaled Mangoldt measure

\[
\nu_X=\frac1X\sum_{n\ge2}\Lambda(n)\delta_{n/X}.
\]

Define once and for all

\[
K_-(u,v)=\int_{-\infty}^{0}h(t-u)h(t-v)\,dt,
\qquad
F_h(r,s)=\frac{K_-(\log r,\log s)}{\sqrt{rs}},\quad r,s>0. \tag{7}
\]

This retains the upper observation boundary. On actual prime-power atoms it is exactly the original prefix kernel:

\[
K_-(\log(m/X),\log(n/X))=k_T(\log m,\log n).              \tag{8}
\]

To check the lower boundary, substitute `t=w-T`. The extra range `w<0` has no prime packet because `log n-S>0`. Thus the extension of the integral to minus infinity changes **no actual summand**. This is not replacement by the whole-line autocorrelation.

Consequently,

\[
\boxed{\frac{E_Z(\log X)}X=\iint F_h(r,s)\,d\nu_X(r)d\nu_X(s).} \tag{9}
\]

The fixed kernel is continuous for `r,s>0`, zero unless

\[
0<r,s\le e^S,\qquad e^{-2S}\le r/s\le e^{2S},
\]

and satisfies

\[
|F_h(r,s)|\le\frac{\|h\|_2^2}{\sqrt{rs}}
\mathbf1_{e^{-2S}\le r/s\le e^{2S}}.                     \tag{10}
\]

The behavior at `r=s=0` must be paid, not ignored. Since
`nu_X((0,u])=psi(Xu)/X<=A u`, (10) gives uniformly in X

\[
\iint_{r\le\varepsilon}|F_h|\,d\nu_Xd\nu_X
\le A^2e^{3S}\|h\|_2^2\varepsilon.                       \tag{11}
\]

Indeed, for fixed r the inner integral is at most
`e^S||h||_2^2 nu_X((0,e^(2S)r])/r`. The same argument applies with either or both measures replaced by Lebesgue measure, or with total variation bounded by `nu_X+dr`. For the union `r<=epsilon or s<=epsilon`, double the displayed constant. Thus every integral used below is absolutely meaningful.

## 4. Complete deterministic continuum subtraction

For every fixed r, the entire continuum row vanishes:

\[
\begin{aligned}
\int_0^\infty F_h(r,s)ds
&=r^{-1/2}\int_{-\infty}^0h(t-\log r)
\left[\int_0^\infty s^{-1/2}h(t-\log s)ds\right]dt\\
&=r^{-1/2}\int_{-\infty}^0h(t-\log r)e^{t/2}dt
\int e^{-v/2}h(v)dv=0.
\end{aligned}                                                     \tag{12}
\]

The columns vanish as well. The continuum runs over `(0,infinity)`: restricting it to integers at least one or primes at least two would create an unpaid lower-boundary correction. The kernel itself restricts the upper range, and (11) pays the lower end.

Define the exact centered measure

\[
\Delta_X=\nu_X-dr,\qquad
\Delta_X((0,r])=\frac{\psi(Xr)-Xr}{X}.
\]

Expanding the product measure and using (12), with all mixed terms included, gives

\[
\boxed{\mathfrak C_h(X):=\iint F_h\,d\Delta_Xd\Delta_X
=\frac{E_Z(\log X)}X\ge0.}                               \tag{13}
\]

This is the precise prime-pair discrepancy after **complete** continuum removal. It uses the actual signed discrepancy, not a conjectural Hardy--Littlewood pair-density model, a prime-ideal specialization, or independent random prime coefficients. The arithmetic pairs are the exact pairs in (4), together with the paid diagonal.

An equivalent nonsingular finite-prefix formula uses `E_psi(x)=psi(x)-x`,

\[
Z(t)=\int_0^\infty x^{-1/2}h(t-\log x)\,dE_\psi(x).       \tag{14}
\]

Its continuum is zero by (1), and all boundary terms vanish because the test function has compact support inside `(0,infinity)`. Integration by parts yields

\[
Z(t)=e^{-t/2}\int_{-S}^S e^{v/2}E_\psi(e^{t-v})
\left[h'(v)+\tfrac12h(v)\right]dv.                       \tag{15}
\]

Equations (13)--(15) are identities, not new arithmetic uppers. Their value is that the specific remaining aggregate and its normalization are now fixed, and every deterministic main term is removed before an inequality is attempted.

## 5. Both signs of the complete covariance have the same exponential main term

For a real number x write `x_+=max(x,0)` and `x_-=max(-x,0)`. Keep the ordered pair sums

\[
\mathcal P_T=\sum_{m\ne n}
\frac{\Lambda(m)\Lambda(n)}{\sqrt{mn}}
[k_T(\log m,\log n)]_+,
\quad
\mathcal N_T=\sum_{m\ne n}
\frac{\Lambda(m)\Lambda(n)}{\sqrt{mn}}
[k_T(\log m,\log n)]_-.
\]

Thus `O_T=P_T-N_T`. Every contributing off-diagonal pair is coprime by (4).

The ordinary prime number theorem, `psi(x)=x+o(x)`, implies vague convergence `nu_X -> dr` on compact subintervals of `(0,infinity)`. This standard input was checked at [DLMF 25.16.3](https://dlmf.nist.gov/25.16.E3). Products of these positive locally finite measures converge on each compact rectangle bounded away from zero. Apply this to the continuous functions `(F_h)_+` and `(F_h)_-`, then remove the small-r cutoff using the uniform bound (11). The diagonal is nonnegative and contributes only `D_T/X -> 0` by (3). Therefore

\[
\frac{\mathcal P_T}{e^T}\longrightarrow
\iint(F_h)_+\,drds,
\qquad
\frac{\mathcal N_T}{e^T}\longrightarrow
\iint(F_h)_-\,drds.                                     \tag{16}
\]

The row cancellation (12) makes the two integrals equal. Both are strictly positive. To verify this without a numerical plot, let `k=h*h`. Then `k(0)=||h||_2^2>0`, but

\[
\int e^{u/2}k(u)du=\left(\int e^{u/2}h(u)du\right)^2=0.
\]

Continuity forces k to be negative on some open interval. If `log r` and `log s` both lie sufficiently far below zero, the packets are completely before the terminal cut and `K_-(log r,log s)=k(log r-log s)`. Such open regions realize both signs of F. Hence the actual source determines a finite strictly positive constant

\[
c_h^{\rm pair}:=\iint(F_h)_+drds
=\iint(F_h)_-drds=\tfrac12\iint|F_h|drds>0.
\]

We have proved the paper result

\[
\boxed{\mathcal P_T=c_h^{\rm pair}e^T+o_h(e^T),\qquad
\mathcal N_T=c_h^{\rm pair}e^T+o_h(e^T).}                 \tag{17}
\]

This is a statement about the **complete clipped sum of actual prime powers**, including its real cutoff. It is stronger in scope than a lower bound for one selected component. It does not say that `O_T` has exponential size: the equal main terms cancel. Ordinary PNT proves only `E_Z(T)=o_h(e^T)`, consistently with (13).

In particular, a positive-part upper `P_T<=C_eta exp(eta T)` with `eta<1`, or an absolute off-diagonal upper at that rate, is false for the actual source at all sufficiently large horizons. This falsifies those unsigned proof strategies without replacing the genuine coefficients by a toy model.

Define the complete centered sign remainders

\[
R_h^+(T)=\mathcal P_T-c_h^{\rm pair}e^T,
\qquad R_h^-(T)=\mathcal N_T-c_h^{\rm pair}e^T.
\]

Then the exact remaining signed residual is

\[
\boxed{O_T=R_h^+(T)-R_h^-(T).}                            \tag{18}
\]

No separate smallness of either remainder is needed or established. PNT alone says each is `o(e^T)`; the needed accuracy is much finer.

## 6. The concrete Cauchy attempt and the rate it actually supplies

One direct finite Cauchy estimate, with all original coefficients, is

\[
|Z(t)|^2\le
\left(\sum_{e^{t-S}\le n\le e^{t+S}}\frac{\Lambda(n)}n\right)
\left(\sum_{e^{t-S}\le n\le e^{t+S}}\Lambda(n)|h(t-\log n)|^2\right)
\le C_h e^t.                                             \tag{19}
\]

Chebyshev and partial summation justify the two factors. This proves `E_Z(T)<=C_h exp(T)`, not every-positive-rate control. Exact coprimality does not improve this estimate, and (17) shows why replacing the signed pair sum by its positive or absolute part cannot repair it.

A centered Cauchy attempt uses `g=h'+h/2` and
`epsilon(y)=sup_{x>=y}|psi(x)-x|/x`. For sufficiently large t, (15) gives

\[
|Z(t)|\le B_h e^{t/2}\epsilon(e^{t-S}),\qquad
B_h=\int_{-S}^S e^{-v/2}|g(v)|dv.                        \tag{20}
\]

For any fixed A and `T>=A`,

\[
E_Z(T)\le E_Z(A)+B_h^2(e^T-e^A)\epsilon(e^{A-S})^2.      \tag{21}
\]

Thus PNT supplies `E_Z(T)=o(e^T)`. Substituting a classical quantitative PNT error into this formula still leaves a positive exponential rate in T; it does not provide arbitrarily small rates. This pass does not claim a stronger external prime-pair or large-sieve theorem than was actually supplied. A sieve upper for a nonnegative majorant would face the genuine order-`exp(T)` mass in (17).

The weighted signed average in (15) could be much smaller than the supremum in (20). Controlling precisely that cancellation, or its pair version (13), is the unproved step. Replacing it by a uniform RH-scale bound for `E_psi` would merely assume an RH-equivalent estimate, not derive the desired cancellation.

## 7. Exact remaining target, with common-horizon quantifiers

An independently proved closing covariance upper would be

\[
\forall\eta>0\ \exists C_{h,\eta}<\infty\ \forall R>0\
\exists T\ge R:\quad
R_h^+(T)-R_h^-(T)\le C_{h,\eta}e^{\eta T}.                \tag{22}
\]

The source and constant precede the horizon choice. The two remainders, all prime powers, and all terms of the covariance are evaluated at that same T. Adding the polynomial diagonal and shrinking the requested exponent if necessary makes (22) equivalent to the energy upper with every positive exponent. In the fixed-kernel discrepancy normalization, the same target is

\[
\boxed{\forall\eta>0\ \exists C_{h,\eta}\ \forall R>1\
\exists X\ge R:\quad
\mathfrak C_h(X)\le C_{h,\eta}X^{-1+\eta}.}              \tag{23}
\]

Only a cofinal sequence is requested. No argument here upgrades it to an eventual pointwise estimate, a running envelope, or a bound for separately chosen local windows.

The target is quantitatively specific: the two sign masses have the known scale `X`, and their complete difference must be controlled at scale `X^eta` after the paid diagonal. PNT identifies their common continuum coefficient but supplies neither this precision nor a mechanism that forces it.

At such a horizon, weighted Cauchy gives

\[
A_Z(T)^2=
\left(\int_0^T e^{-(T-t)/2}|Z(t)|dt\right)^2
\le(1-e^{-T})E_Z(T)\le E_Z(T).                           \tag{24}
\]

The existing visible-zero centered-moment lower is eventual at every sufficiently late horizon. For a displacement `delta>0`, choose the energy exponent strictly below `2delta`, then choose the cofinal horizon beyond its lower-bound threshold. The contradiction would follow. This is a valid consumer of (22)/(23); no proof of those estimates has been obtained.

## 8. Completion and native constraints are retained, not silently promoted

On `[0,T]`, the complete identity `a*Z=W` gives a bounded quadratic with the different clipped kernel

\[
k^a_T(u,v)=\int_0^T(a*h)(t-u)(a*h)(t-v)dt,
\]

\[
\sum_{m,n\le N_T}\frac{\Lambda(m)\Lambda(n)}{\sqrt{mn}}
k^a_T(\log m,\log n)=\|W\|_{2,[0,T]}^2\le C_W^2.         \tag{25}
\]

The finite cutoff is valid because `a*h` starts at `-S`. Equation (25) contains all cross terms and earlier history. It is not an upper for (2): the required comparison between these two quadratic kernels on the actual Mangoldt field remains unproved. No general stable inverse, positivity of the canonical Weil form, or disappearance of terminal output is assumed.

At aperture `L=2T`, the established physical native-output adapter connects this same field to the exact even moment slice, with subexponential adapter loss and paid source approximation. In a nonorthonormal native basis B, the column quantity remains

\[
(Ax)^*G^{-1}(Ax),\qquad G=B^*B,\quad A=B^*H_LB,
\]

not the Euclidean square `||Ax||^2`. Conversely the full physical output is the fixed arch part plus the reflected field, so an every-positive-rate upper for E_Z supplies the corresponding column upper. The new pair discrepancy does not change that source connection or furnish its missing amplitude estimate.

## 9. What this attempt established and did not establish

**DERIVED:** all nonzero prime-power off-diagonal overlaps are coprime; proper-power corrections have an explicitly payable norm cost; the full clipped field is an exact fixed-kernel centered Mangoldt-pair discrepancy; its two complete sign masses share the same strictly positive order-`exp(T)` asymptotic; unsigned covariance bounds at smaller exponential rate are false for the actual source.

**OPEN:** the much finer signed difference (22), equivalently (23), with constants fixed before a common cofinal horizon. The actual completion and native column constraints remain intact but do not yet prove this upper.

This pass therefore supplies a quantitative arithmetic obstruction and an exact centered target, not a closure. In particular, the correct next attack must retain the difference of the two large sign masses, rather than prove smallness of either one separately or replace the clipped kernel by a whole-line autocorrelation.

### Local provenance and comparison

- `../step4-signed-amplitude-round3-2026-11-10/CANONICAL_TRANSLATION_ATTEMPT.md`: actual translated source, clipped covariance, and exponential terminal-collar audit.
- `../step4-study-2026-11-09/PASS16_PRIMITIVE_AND_SIGNED_PRIME_ENERGY_REVIEW.md`: primitive-channel and prime-insertion sign failures.
- `../step4-study-2026-11-09/PASS18_CENTERED_JETS_AND_COMPLETE_COVARIANCE_REVIEW.md`: complete covariance consumer and prohibition on component-to-total inference.
- `../step4-signed-response-round2-2026-11-10/OUTPUT_RECOVERY.md` and `NATIVE_SIGNED_TARGET.md`: full native adapter, source normalization, inverse-Gram metric, and cofinal closing interface.
- [DLMF 25.16.3](https://dlmf.nist.gov/25.16.E3): the ordinary prime number theorem used for (16)--(17). No zero exclusion stronger than that input is asserted.
