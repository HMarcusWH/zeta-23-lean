# Positive arithmetic precursor and the exact terminal energy cancellation

11 November 2026. **DERIVED paper investigation, pending independent review. No repository edit, new Lean compilation, CI qualification, closing arithmetic upper, or Step 4 closure.** The unchanged source baseline is [PR299](https://github.com/HMarcusWH/zeta-23-lean/pull/299), commit `b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`.

This pass moves before the signed source filter and uses the actual positive Mangoldt measure. It obtains an exact harmonic renewal equation, the complete finite-prefix Green identity, a sharp damping threshold for the proposed positive energy, and an independently bounded divisor pairing. For the genuine arithmetic field, the apparently positive bulk and its terminal boundary each have order exp(T) and cancel at leading order. The bounded divisor pairing retains an unpaid signed prime boundary derivative. These are actual-source deductions, not a claim that a freely chosen unstable mode is the source.

## 1. Positive precursor, complete divisor coupling, and normalization

Put a=1/2 and retain the fixed nonnegative probability source q. Write

\[
k=q*q\ge0,\qquad \operatorname{supp}k\subset[-S,S],\qquad S=1/2048,
\]
\[
L=D^2-a^2,\qquad h=L^2k,
\qquad K(z)=\int e^{-zv}k(v)\,dv=Q_0(z)^2.
\tag{1}
\]

Define the two unfiltered fields using every prime power and every integer:

\[
B(t)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}k(t-\log n)\ge0,
\qquad
V(t)=\sum_{n\ge2}\frac{\log n}{\sqrt n}k(t-\log n)\ge0.
\tag{2}
\]

They and all their derivatives vanish before t0=log(2)-S>0. The sums are locally finite, including after any fixed number of derivatives. There is no initial-value impulse at zero. The literal divisor identity 1*Lambda=log gives

\[
NB=V,\qquad
(Nf)(t)=\sum_{n\ge1}n^{-1/2}f(t-\log n),
\]
\[
Z=L^2B,\qquad U=L^2V=NZ.
\tag{3}
\]

All fields are extended by zero to negative ages. Equation (3) is a finite-history identity at every time; it needs no convergent infinite Fourier transform of B or Z.

Normalize the growing continuum before filtering:

\[
F(t)=e^{-t/2}B(t)\ge0,\qquad G(t)=e^{-t/2}V(t),
\qquad P=D^2+D.
\]

The source satisfies the exact positive harmonic renewal equation and differential identities

\[
\boxed{\sum_{n\ge1}\frac1nF(t-\log n)=G(t),}
\qquad
Z(t)=e^{t/2}P^2F(t),\quad U(t)=e^{t/2}P^2G(t).
\tag{4}
\]

The missing target is therefore a quantitative control of derivatives of the *complete* positive solution F after the constant continuum has been annihilated. Positivity of F alone does not give a sign to P^2F.

## 2. What the genuine source already gives quantitatively

Set

\[
\kappa_0=K(1/2)>0,\qquad \kappa_1=K'(1/2).
\]

Fixed fourth-order Euler--Maclaurin, applied to the smooth compact profiles

\[
f_{j,0}(y)=y^{-1/2}k^{(j)}(-\log y),\qquad
f_{j,1}(y)=(\log y)f_{j,0}(y),
\]

gives, for every fixed j needed below and t>=0,

\[
V^{(j)}(t)=\frac{d^j}{dt^j}\left[e^{t/2}(\kappa_0t+\kappa_1)\right]+R_j(t),
\qquad |R_j(t)|\le E_j(1+t)e^{-7t/2}.
\tag{5}
\]

Each E_j is a fixed source constant. One may take the sum of the L1 norms of the fourth derivatives of f_{j,0}, f_{j,1}, divided by 720. Every endpoint term is zero. The two profile integrals are

\[
\int f_{j,0}=a^j\kappa_0,\qquad
\int f_{j,1}=j a^{j-1}\kappa_0+a^j\kappa_1,
\]

with the first term of the second expression zero when j=0. This checks the signs and normalization in (5). In particular

\[
G(t)=\kappa_0t+\kappa_1+O_k((1+t)e^{-4t}).
\tag{6}
\]

No variable derivative order is needed in this note. The stronger Gevrey decay established in preceding rounds is compatible with (5) but is not required here.

Chebyshev's elementary estimate psi(x)<=A x yields, for every fixed j,

\[
|B^{(j)}(t)|\le C_j e^{t/2},\qquad
C_j=Ae^{3S/2}\|k^{(j)}\|_\infty.
\tag{7}
\]

Ordinary PNT gives the stronger qualitative statement

\[
e^{-t/2}B^{(j)}(t)\longrightarrow a^j\kappa_0.
\tag{8}
\]

Indeed, with x=exp(t), the left side is x^{-1} sum Lambda(n) f_{j,0}(n/x); PNT and finite Stieltjes integration against this fixed compact profile give its limit integral. Thus

\[
F(t)\longrightarrow\kappa_0,\qquad F^{(j)}(t)\longrightarrow0\quad(j\ge1\text{ fixed}).
\tag{9}
\]

These are statements about the actual prime-power field. Ordinary PNT, or mere convergence in (9), does not supply a rate of order exp(-(1/2-epsilon)t) for the filtered derivatives. The relevant PNT and conditional RH estimate for psi are recorded in [DLMF 25.16](https://dlmf.nist.gov/25.16).

## 3. The complete finite-prefix energy identity

For sigma>=0 put

\[
f_\sigma(t)=e^{-\sigma t}B(t),\qquad
I_\sigma(T)=\int_0^T e^{-2\sigma t}B(t)Z(t)\,dt.
\]

Conjugating the exact differential operator gives

\[
e^{-\sigma t}Z=
\left[(D+\sigma)^2-a^2\right]^2f_\sigma.
\]

Integration by parts on the finite interval, with every endpoint retained, gives

\[
\boxed{
I_\sigma(T)=\int_0^T\left[(f_\sigma'')^2
+(2a^2-6\sigma^2)(f_\sigma')^2
+(\sigma^2-a^2)^2f_\sigma^2\right]dt
+\mathcal B_\sigma(T)-\mathcal B_\sigma(0),}
\tag{10}
\]

where

\[
\begin{aligned}
\mathcal B_\sigma={}&ff'''-f'f''
+4\sigma ff''-2\sigma(f')^2\\
&+(6\sigma^2-2a^2)ff'
+2\sigma(\sigma^2-a^2)f^2,
\qquad f=f_\sigma.
\end{aligned}
\tag{11}
\]

The lower endpoint is zero for the actual field. The upper endpoint has no assumed sign.

At sigma=0 the bulk in (10) is positive:

\[
\int_0^T BZ
=\int_0^T\left[(B'')^2+\tfrac12(B')^2+\tfrac1{16}B^2\right]dt
+\left[BB'''-B'B''-\tfrac12BB'\right]_0^T.
\tag{12}
\]

An equivalent ground-adapted square is

\[
\int_0^T BZ=\int_0^T(LB)^2dt
+\left[B(LB)'-B'LB\right]_0^T
=\int_0^T(LB)^2dt+\left[BB'''-B'B''\right]_0^T.
\tag{13}
\]

Equations (12) and (13) are identical: expanding the square in (13) moves exactly -2a^2 BB' into the boundary. Neither allows the terminal contribution to be removed. Moreover the proposed left side is BZ, not the independently bounded completed pair Z(N_yZ).

## 4. The positive bulk actually has an exponential terminal cancellation

Apply (8) to (12). The positive integrand there is asymptotic to

\[
4a^4\kappa_0^2e^{2at}=\tfrac14\kappa_0^2e^t.
\]

Consequently the exact genuine-source asymptotics are

\[
\boxed{
\int_0^T\left[(B'')^2+\tfrac12(B')^2+\tfrac1{16}B^2\right]dt
\sim\tfrac14\kappa_0^2e^T,}
\]
\[
\boxed{
BB'''-B'B''-\tfrac12BB'
=-\tfrac14\kappa_0^2e^T+o(e^T)\quad(t=T).}
\tag{14}
\]

The two leading terms BB''' and B'B'' cancel; the remaining leading boundary is -BB'/2. This is an actual arithmetic compensation, derived from PNT and the unchanged source, not a pure exponential substituted for the primes. It shows that the dominant positivity visible before filtering is exactly the continuum contribution that the source annihilates. Retaining that positive term while deleting its terminal compensation would produce a false energy estimate.

The correctly retained identity yields only integral BZ=o(exp(T)) from these inputs. It gives no closing bound for integral Z^2 or its weighted counterpart.

## 5. Damping cannot simultaneously supply the proposed positivity and integrability

The real whole-line multiplier associated with the bulk in (10) is

\[
m_\sigma(\xi)=\xi^4+(2a^2-6\sigma^2)\xi^2+(\sigma^2-a^2)^2.
\tag{15}
\]

For sigma>=0, this polynomial is nonnegative for every real xi **if and only if**

\[
0\le\sigma\le a/\sqrt2=1/(2\sqrt2).
\tag{16}
\]

To verify the exact threshold, set u=xi^2>=0. If the linear coefficient is negative, the quadratic minimum is nonnegative precisely when 2a^2-6sigma^2 >= -2|sigma^2-a^2|. For sigma<=a this reduces to sigma^2<=a^2/2; for sigma>=a it fails. If the linear coefficient is nonnegative the criterion is already satisfied.

By (8), however, the actual f_sigma is globally square-integrable only when sigma>a=1/2. At sigma=a it approaches the nonzero constant kappa0; below a it grows exponentially. For sigma>a, (7) makes its fixed derivatives square-integrable and the endpoint terms at infinity vanish, but (15) is then indefinite. There is no overlap between the two regimes.

At the natural continuum normalization sigma=1/2, the exact formula reads

\[
I_{1/2}(T)=\int_0^T\left[(F'')^2-(F')^2\right]dt
+\left[FF'''-F'F''+2FF''-(F')^2+FF'\right]_0^T.
\tag{17}
\]

Its bulk multiplier is xi^4-xi^2. Subtracting the continuum does not turn it into a positive quadratic.

This establishes the failure of this automatic damping-and-square argument. It does **not** establish that an arbitrary negative multiplier test function belongs to the genuine source core, or that no other arithmetic positivity argument can work.

## 6. Use the independently controlled divisor output instead

There is a stronger source-specific pairing that really is bounded. The actual integer drive satisfies the fixed-order bound

\[
|U(t)|\le B_h(1+t)e^{-7t/2}.
\]

Together with (7), this gives

\[
\boxed{\int_0^\infty |B(t)U(t)|dt\le\tfrac49 C_0B_h<\infty.}
\tag{18}
\]

Now apply the Green identity to the exact equation U=L^2V, instead of replacing U by Z:

\[
\int_0^T BU
=\int_0^T (LB)(LV)dt
+\left[B(LV)'-B'LV\right]_0^T,
\qquad LV=N(LB).
\tag{19}
\]

Equation (5), for j=0,1,2,3, implies

\[
LV=\kappa_0e^{t/2}+r(t),\qquad
(LV)'=\tfrac12\kappa_0e^{t/2}+r_1(t),
\]
\[
|r(t)|\le(E_2+a^2E_0)(1+t)e^{-7t/2},\quad
|r_1(t)|\le(E_3+a^2E_1)(1+t)e^{-7t/2}.
\tag{20}
\]

Since B=e^(t/2)F, the complete upper boundary is

\[
B(LV)'-B'LV=-\kappa_0e^t F'(t)+\epsilon(t),
\]
\[
|\epsilon(t)|\le C_*(1+t)e^{-3t},\quad
C_*=C_0(E_3+a^2E_1)+C_1(E_2+a^2E_0).
\tag{21}
\]

Thus the bounded output pairing yields the exact quantitative deduction

\[
\boxed{
\int_0^T (LB)(N(LB))dt
=\kappa_0e^T F'(T)+R(T),}
\]
\[
|R(T)|\le\tfrac49C_0B_h+C_*(1+T)e^{-3T}.
\tag{22}
\]

This retains all prime powers, all earlier ages, the complete integer divisor response, and both endpoints. It exposes an unpaid prime boundary derivative; it does not bound the square of LB.

The obstruction is visible already in the literal source. On the isolated first-prime pulse, LB=(log 2)/sqrt(2) times Lk(t-log 2). The nonzero compact profile Lk changes sign: its integral is -a^2, while its weighted integral against exp(-av) is zero. Positive coefficients of N do not by themselves establish nonnegativity of the full correlation in (22); no negative value of that actual correlation is asserted here. The leading LV is positive, but that does not determine the sign of LB.

Keeping only elementary source bounds pays the right side of (22) by O(exp(T)); PNT pays it by o(exp(T)). Neither is an all-positive-exponent upper. The derivative in (22) must not be declared independently small merely because the paired output in (18) is small.

## 7. What positivity and log-convexity do and do not supply

Global log-convexity does not follow from the positive Mangoldt coefficients. Before the n=3 pulse begins, B is a single nonzero smooth compact k pulse and then returns to zero. A nonzero continuous log-convex function cannot have this compact positive component with zero endpoints. Thus a global log-convex precursor premise is already false for the genuine early-time field. This observation makes no unproved assertion about possible eventual curvature properties.

There is an exact positive variance identity available from (4). On positive values of F write ell=F'/F, and define F ell^2=0 at zeros. Smooth nonnegativity gives F'=0 at such zeros; all sums at a fixed time are finite. For G(t)>0,

\[
\sum_{n\ge1}\frac1n\frac{F'(t-\log n)^2}{F(t-\log n)}
-\frac{G'(t)^2}{G(t)}
=\sum_{n\ge1}\frac1n F(t-\log n)
\left[\ell(t-\log n)-\frac{G'(t)}{G(t)}\right]^2\ge0.
\tag{23}
\]

At a zero of F the indicated summand uses the zero convention just stated. This is Jensen/Cauchy--Schwarz for the actual finite divisor weights. From (6), its controlled part G'^2/G is asymptotic to kappa0/t. The inequality is a **lower** bound on a derivative dispersion, not the required upper. Reversing it or postulating nonnegative logarithmic curvature would add a new unsupported arithmetic premise.

## 8. Exact remaining rate and consequence for the actual loading

For the unchanged fixed 0<gamma<1,

\[
W_\gamma(T)=\int_0^T e^{-\gamma(T-t)}|Z(t)|^2dt
=e^T\int_0^T e^{-(1+\gamma)(T-t)}|P^2F(t)|^2dt.
\tag{24}
\]

Thus a closing upper would require, with constants fixed before each selected horizon,

\[
\forall\eta>0\ \exists C_\eta<\infty\ \forall R\ \exists T\ge R:
\quad
\int_0^T e^{-(1+\gamma)(T-t)}|P^2F(t)|^2dt
\le C_\eta e^{-(1-\eta)T}.
\tag{25}
\]

The estimates actually obtained above give O(exp(T)) for W_gamma, and ordinary PNT improves this to o(exp(T)). Indeed P^2F tends to zero and is uniformly bounded; exponential averaging in (24) preserves this convergence. No positive exponential saving is inferred from little-o alone. If a separately available prime-error estimate psi(x)-x=O(x^theta log(x)^b) is inserted, the earlier complete weighted discrepancy calculation gives exponent 2theta-1, with the same fixed source and all boundaries. This positive-precursor calculation has not improved that exponent.

The reviewed source-core reconstruction transports a genuine W_gamma upper to the corresponding actual-loading estimate. It does not license imposing (16), eventual log-convexity, a terminal derivative bound, or positivity of (22) on the reconstructed arithmetic vector. No arbitrary core vector has been substituted for that vector in this investigation.

## 9. Comparison with preceding attempts and the remaining arithmetic task

The [full divisor analysis](../step4-weighted-response-2026-11-10/DIVISOR_RESEARCH.md) already proved actual exponential growth of absolute Mobius inversion. This pass does not repeat that triangle-inequality route. The [round-5 filter-family analysis](../step4-signed-correlation-round5-2026-11-11/FILTER_FAMILY_ATTEMPT.md) established nonnegative filtered coefficients and bounded positive output Gram forms; those coefficients remain intact here. The [complete covariance calculation](../step4-signed-correlation-round5-2026-11-11/ROUGH_CORRELATION_ARITHMETIC.md) retained the signed full prime discrepancy. The [weighted discrepancy audit](../step4-signed-correlation-round5-2026-11-11/WEIGHTED_DISCREPANCY_ATTEMPT.md) identified the exact terminal square. Equation (22) identifies a related terminal derivative when attempting to move the energy before the source filter.

The new usable information is precise: the complete positive precursor has a linear normalized integer echo, but its leading positive energy is continuum energy and is canceled by the exact physical boundary. Switching to the independently bounded output retains a signed prime derivative at that boundary. Damping the positive precursor enough to justify an infinite energy integral makes this proposed quadratic indefinite.

The remaining task is an independent quantitative restriction on P^2F, or on the actual-loading direction, at the rate in (25). None of the derived identities above supplies that restriction. Step 4 remains **OPEN**.
