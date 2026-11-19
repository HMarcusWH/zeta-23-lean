# Averaging and composing the complete rough-filter family

11 November 2026. **DERIVED paper investigation, pending independent review. No new Lean compilation, CI qualification, repository edits, signed closing upper, or Step 4 closure.** Source baseline: PR299 `b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`.

This pass tests the whole bounded filter family rather than one characteristic zero. It obtains three concrete actual-source facts: a positive Gram-family bound, an explicit growing term in every twice-completed output, and simultaneous exponential compensation of one genuine prime block across all small cutoffs. It also determines exactly what a finite average or telescoped difference measures. None supplies the missing coercive estimate for the complete source.

## 1. Fixed source, full-prefix operators and two independently bounded families

Use the unmodified causal fields

\[
Z(t)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}h(t-\log n),\qquad
U=N*Z,\qquad
N=\sum_{n\ge1}n^{-1/2}S_{\log n}.
\]

The first pulse begins at t0=log(2)-S>0. Every finite-prefix operator below uses zero extension before zero; no late-window restart is made. For y>=2,

\[
N_y:=N_{>y}=M_{\le y}N,
\quad M_{\le y}=\prod_{p\le y}(I-T_p),
\quad T_pf(t)=p^{-1/2}f(t-\log p),
\quad F_y=N_yZ=M_{\le y}U.
\tag{1}
\]

All prime-power cofactors in N_y are retained. The existing source argument proves, for every y,T,

\[
\int_0^T|Z(t)F_y(t)|dt\le C_Z I_U2^{\pi(y)},
\quad I_U=\int_0^\infty e^{s/2}|U(s)|ds<\infty.
\tag{2}
\]

There is also a positive bound that is stronger than (2) in its y-dependence. Young's inequality for the finite causal filter gives

\[
\boxed{
\|F_y\|_{L^2(0,\infty)}
\le\|U\|_2\prod_{p\le y}(1+p^{-1/2})
\le\|U\|_2e^{2\sqrt y}.}
\tag{3}
\]

Only the elementary bound sum_{n<=y}n^{-1/2}<=2 sqrt(y) is needed. Every earlier source age and every output time is retained in (3); restriction to a prefix is therefore legitimate.

Fix Y=Y_T=floor(T/(8 log(T+2))). Uniformly over all cutoffs 2<=y<=Y, both (2) and (3) are subexponential in T. For any nonnegative weights w_j with sum w_j=1 and cutoffs y_j<=Y,

\[
\left|\sum_jw_j\langle Z,N_{y_j}Z\rangle_{[0,T]}\right|
\le C_ZI_U2^{\pi(Y)},
\qquad
\sum_jw_j\|N_{y_j}Z\|_{2,[0,T]}^2
\le\|U\|_2^2e^{4\sqrt Y}.
\tag{4}
\]

Thus the positive Gram family really is bounded on the genuine source. Its positivity is not in question; its coercivity back to ||Z|| is.

## 2. Exact coefficient geometry of averaging and cutoff differences

On the prefix, write N_y=I+B_y with the full causal delay kernel. A normalized weighted average is

\[
\overline N=\sum_jw_jN_{y_j}
=I+\sum_{d\ge2}\frac{a(d)}{\sqrt d}S_{\log d},
\quad a(d)=\sum_jw_j\mathbf1_{P^-(d)>y_j}.
\tag{5}
\]

For positive weights, 0<=a(d)<=1. Crucially,

\[
P^-(d)>Y\ \Longrightarrow\ a(d)=1.
\tag{6}
\]

All rough integers beyond the largest selected cutoff retain their full coefficient. This includes every ordinary prime p>Y in the causal range. Positive averaging does not cancel that common tail.

The actual finite-time symmetric operator is

\[
\overline A=I+\tfrac12(\overline B+\overline B^*),\quad
\overline B^*g(s)=\sum_{d\ge2}\frac{a(d)}{\sqrt d}
\mathbf1_{s+\log d\le T}g(s+\log d).
\]

Its bounded quadratic is exactly

\[
\langle Z,\overline A Z\rangle
=E_Z(T)+\sum_{d\ge2}\frac{a(d)}{\sqrt d}
\int_{\log d}^T Z(t)Z(t-\log d)dt.
\tag{7}
\]

The coefficients are positive, but the correlations are signed. Neither (4) nor (6) supplies a lower bound for the complete cross term in (7).

More generally, allow signed weights and let W=sum w_j. Both the identity coefficient and every coefficient with P^-(d)>Y equal W. Therefore a telescoped difference with W=0 removes the energy coefficient and the whole common rough tail simultaneously. A combination with W=1 retains both. As long as a prime p>Y remains in the causal range, no such linear combination equals the identity operator: its p-delay coefficient is necessarily p^{-1/2}. This is a finite-prefix coefficient statement, not an appeal to analytic continuation.

At a single prime insertion,

\[
N_p=(I-T_p)N_{p^-},\qquad
\mathfrak Q_p(T)-\mathfrak Q_{p^-}(T)
=-\langle Z,T_pF_{p^-}\rangle_{[0,T]},
\quad\mathfrak Q_y(T)=\langle Z,N_yZ\rangle_{[0,T]}.
\tag{8}
\]

The right side is a mixed pairing, not a negative square. Pairing the outputs with themselves instead gives

\[
\|F_p\|_{2,[0,T]}^2-\|F_{p^-}\|_{2,[0,T]}^2
=p^{-1}\|F_{p^-}\|_{2,[0,T-\log p]}^2
\quad-2\operatorname{Re}\langle F_{p^-},T_pF_{p^-}\rangle_{[0,T]}.
\tag{9}
\]

The truncated norm is zero if T<log(p). Both terms and every prehistory value are present; no monotonicity follows by discarding the mixed term.

## 3. The genuine filtered coefficients are monotone, but their quadratic is not ordered by that fact

The coefficient of h(t-log n)/sqrt(n) in F_y is exactly

\[
b_y(n)=\sum_{d\mid(n,\mathcal P_y)}\mu(d)\log(n/d).
\]

Finite inclusion-exclusion evaluates it without a residual:

\[
b_y(n)=
\begin{cases}
\log n,&n\text{ has no prime divisor at most }y,\\
\log p,&p\text{ is its unique prime divisor at most }y,\\
0,&n\text{ has at least two distinct prime divisors at most }y.
\end{cases}
\tag{10}
\]

All multiplicities are retained. Thus b_y(n)>=0 and is nonincreasing in y for every fixed n. This is a real arithmetic ordering furnished by the full divisor identity.

It does not order F_y pointwise because h changes sign. It also does not order its energy: the clipped source Gram matrix has both positive and negative off-diagonal entries. The independently reviewed complete covariance asymptotic proves that both sign masses of the genuine source have order exp(T). Hence entrywise coefficient monotonicity does not justify dropping the cross term in (9), or a small negative-part estimate in (7). A further source-specific signed inequality is still required.

## 4. An actual-source obstruction to composing the cheap forward outputs

The following calculation concerns the genuine source, not an arbitrary unstable test mode. Define

\[
M_0=\int_0^\infty e^{-s/2}U(s)ds=Q(1/2)^2>0.
\tag{11}
\]

Here Q is the bilateral transform of the unchanged nonnegative probability source q. Equation (11) was derived in `DIVISOR_RESEARCH.md`, section 5: the source factor H(z)=(z^2-1/4)^2Q(z)^2 cancels the double pole of -zeta'(z+1/2) at z=1/2, leaving the positive value Q(1/2)^2. This is the negative-weight moment, distinct from the previously vanishing positive-weight moment.

Put g(r)=r^{-1/2}U(-log r) for r>0, extended by zero at r=0 and beyond its positive support. It is compactly supported in [0,exp(-t0)]. It has finite variation. To check the endpoint at zero, fixed fourth-order Euler--Maclaurin applied to h and h' gives U(s),U'(s)=O_h((1+s)exp(-7s/2)); differentiating h retains its two half-pole moment zeros. Consequently g and g' vanish at zero, and ||g'||_1 is finite. Only fixed derivative order is used here.

For x=exp(t), the exact Riemann sum is

\[
(N*U)(t)=x^{-1/2}\sum_{n\ge1}g(n/x).
\]

The bounded-variation Riemann estimate, obtained by integrating g(n/x)-g(r) on each mesh interval, gives

\[
\boxed{(N*U)(t)=M_0e^{t/2}+R(t),\qquad
|R(t)|\le C_he^{-t/2}\quad(t\in\mathbb R).}
\tag{12}
\]

For t>=0 this uses ||g'||_1. For t<0 the actual causal output is zero; the same statement follows by enlarging C_h to at least M_0, since M_0 exp(t/2)<=M_0 exp(-t/2). Thus no early-time exception is hidden in (12).

All convolution products commute on finite causal histories, so

\[
N_yN_zZ=M_{\le y}M_{\le z}(N*U).
\]

Apply both finite filters to (12). Let

\[
c_y=\prod_{p\le y}(1-p^{-1}).
\]

Repeated small-prime factors are included in the double filter. The leading exponential gets the exact factors c_yc_z, while each remainder shift again cancels its coefficient magnitude. Therefore, for every y,z and every real t,

\[
\boxed{
(N_yN_zZ)(t)=M_0c_yc_ze^{t/2}
\quad+O_h\!\left(2^{\pi(y)+\pi(z)}e^{-t/2}\right).}
\tag{13}
\]

This preserves the entire prefix and all negative-age cancellations. For 2<=y,z<=Y_T, the elementary product comparison gives c_y,c_z>=1/Y_T. Uniformly for t in [T/2,T], the error-to-main ratio is at most a fixed multiple of Y_T^2 exp(-T/2) 2^{2Y_T}, which tends to zero. Thus, for all sufficiently large T,

\[
\boxed{
\|N_yN_zZ\|_{2,[0,T]}^2
\ge c_h\frac{e^T}{Y_T^4}
\quad(2\le y,z\le Y_T).}
\tag{14}
\]

So composing two forward completion operators does **not** inherit the subexponential norm bound (3). The same obstruction survives a normalized positive average of such double compositions: their leading coefficients are all at least M_0/Y_T^2 and have the same sign. This is an actual full-source falsifier of that proposed inheritance, not a counterexample substituted for the primes.

Nor is their pairing with Z already paid. On the complete prefix, (13) gives

\[
\langle Z,N_yN_zZ\rangle_{[0,T]}
=M_0c_yc_z\int_0^T e^{t/2}Z(t)dt
\quad+O_h\!\left(T2^{\pi(y)+\pi(z)}\right).
\tag{15}
\]

The error uses the actual elementary bound |Z(t)|<=C_Z exp(t/2). The first term is an unpaid signed arithmetic boundary moment. Explicitly, with Psi(v)=integral_{-infinity}^v exp(w/2)h(w)dw,

\[
\int_0^T e^{t/2}Z(t)dt
=\sum_{n\ge2}\Lambda(n)\Psi(T-\log n).
\tag{16}
\]

Psi is compactly supported by the half-pole moment, and its lower endpoint contributes zero because log(2)>S. Thus (16) contains all prime powers in the terminal collar, with no assumption that their signed sum is small. Formula (15) isolates the precise new quantity that a composed-pairing tactic would need to estimate.

## 5. Simultaneous compensation across the whole family really occurs in the genuine source

There is a direct test of the claim that a large coherent component cannot be compensated consistently at many cutoffs. Let omega=S and w=omega+2S=3S<log(2), and use the actual ordinary-prime block

\[
V_L(t)=\sum_{e^L<p\le e^{L+\omega}}
\frac{\log p}{\sqrt p}h(t-\log p),\qquad
T_L=L+\omega+S.
\tag{17}
\]

All its pulses are retained completely. Its support has width w and ends at T_L. For every y>=2, each nonunit rough delay is at least log(3)>w. Hence on the **entire** prefix [0,T_L],

\[
\boxed{N_yV_L=V_L.}
\tag{18}
\]

Ordinary PNT and finite-interval Stieltjes integration yield

\[
e^{-L/2}V_L(L+v)\longrightarrow
b_\omega(v)=\int_0^\omega e^{r/2}h(v-r)dr
\]

uniformly and in L2 on the fixed support. This is the same ordinary-PNT block limit used earlier; no zero density or RH-scale error is assumed. The profile b_omega is nonzero: its Fourier transform is the nonzero transform of h times (exp((1/2-i xi)omega)-1)/(1/2-i xi), and this latter factor has no zero for real xi. Therefore

\[
\|V_L\|_2^2=\kappa_\omega e^L+o_h(e^L),\qquad
\kappa_\omega=\|b_\omega\|_2^2>0.
\tag{19}
\]

Restore the entire arithmetic complement R_L=Z-V_L, including every other prime, every remaining prime power, and every earlier history. From (1) and (18), exactly on the same prefix,

\[
N_yR_L=-V_L+F_y.
\tag{20}
\]

The uniform family bound (3) now proves, uniformly for 2<=y<=Y_{T_L},

\[
\boxed{
\langle V_L,N_yR_L\rangle
=-\|V_L\|_2^2
\quad+O_h(e^{L/2+2\sqrt{Y_{T_L}}}),}
\tag{21}
\]

and

\[
\|N_yR_L\|_2^2
=\|V_L\|_2^2
\quad+O_h(e^{L/2+2\sqrt{Y_{T_L}}}+e^{4\sqrt{Y_{T_L}}}).
\tag{22}
\]

Thus the complete genuine complement supplies essentially the same negative order-exp(L) mixed term at every such cutoff, while the final filtered field has subexponential energy. Cutoff differences cancel the shared leading block contribution. Positive averages preserve it together with its full compensating complement.

This is not a claim that R_L itself is close to -V_L: N_yR_L includes delayed prehistory. Nor does it infer a large energy for Z. It demonstrates quantitatively that simultaneous compensation across all these connected outputs is already realized by the actual complete arithmetic coupling. Merely counting these compatible observations cannot rule it out.

The same conclusion for the signed pairing family follows directly by polarization: Q_y(V_L)=||V_L||^2 and |Q_y(Z)|<=C_h exp(o(T_L)), so the full complementary quadratic plus its mixed term equals -||V_L||^2+O_h(exp(o(T_L))). Neither complementary term is individually dropped or assigned a sign.

## 6. Native constraints and the exact point where the proposed closure still stops

All of the preceding statements concern the same complete Z that occurs in the physical canonical source column. The bounded arch part, actual inverse-Gram metric and quartic input correction remain those of the reviewed source adapter. The block decomposition is an arithmetic calculation only: neither V_L nor R_L is asserted to be a canonical ground eigenray, reciprocal input or independently admissible native state.

For a positive average of the original pairings, the first missing line remains a closing-rate lower bound on the complete cross term in (7). For a positive average of the completed energies in (4), it is a source-specific coercive estimate from that Gram family back to E_Z(T), retaining the full native output complement. The actual even/odd rank-one displacement controls its stated two source-row functionals; it does not identify either missing inequality with a known signed quantity.

The calculation (21) is particularly relevant to this distinction: large signed compensating contributions are compatible with all the source-preserving filters, not forbidden by their joint consistency. A proof must distinguish the complete field's remaining norm from those already forced compensations.

Every finite Euler cutoff also retains the common zeta-zero factor and its multiplicities, but this is not the sole reason given for failure here. The finite symmetric operator coefficients, the exact cutoff-difference identities, the positive Gram bound, the actual growing double-completion term and the actual simultaneous block compensation have all been evaluated separately.

**Outcome:** new valid information is (3), (13)--(16) and (21)--(22), together with the exact averaging/telescoping restrictions. No closing signed covariance lower or source-specific coercivity was proved. Step 4 and RH remain OPEN.

### Source and qualification links

- `../step4-complete-residual-round4-2026-11-10/ROUGH_ECHO_NATIVE_PAIRING.md`: complete pairing bound, prehistory, native rows and full complement.
- `../step4-complete-residual-round4-2026-11-10/COMPLETE_RESIDUAL_RECURRENCE.md`: exact rough-integer recurrence and finite Euler cutoffs.
- `../step4-complete-residual-round4-2026-11-10/COMPLETE_COVARIANCE_ATTEMPT.md`: full clipped positive/negative covariance masses.
- `../step4-weighted-response-2026-11-10/DIVISOR_RESEARCH.md`, sections 2 and 5: fixed-order drive decay and the nonvanishing negative-weight integer moment.
- [DLMF 25.16.3](https://dlmf.nist.gov/25.16.E3): ordinary PNT used for the actual-prime block limit. All other estimates in this note are finite algebra or source-fixed analytic estimates explained above.
