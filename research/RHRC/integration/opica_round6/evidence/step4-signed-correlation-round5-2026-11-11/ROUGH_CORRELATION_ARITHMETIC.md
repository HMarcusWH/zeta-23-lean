# Exact arithmetic of the complete rough correlation

11 November 2026. **DERIVED paper results, pending independent review. No closing lower bound, new Lean compilation or CI authority.** Mathematical baseline: PR299 b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7. No repository files are changed.

This follows the newly bounded complete rough-echo pairing. It combines the rough coefficient with the actual Mangoldt coefficient before estimating anything. The result is an explicit nonnegative sifted coefficient, a vanishing echo-diagonal bound, and an actual-source asymptotic for both signs of the complete regrouped correlation. Those signs each have scale exp(T) T/log(T); their difference is the unpaid quantity. Nonnegative arithmetic coefficients therefore do not establish a lower bound for this signed packet covariance.

## 1. Exact grouping of every rough divisor and prime power

Use the unchanged real source h, support [-S,S], S=1/2048, and all prime powers in

\[
Z(t)=\sum_{m\ge2}\frac{\Lambda(m)}{\sqrt m}h(t-\log m).
\]

Let y>=2 be frozen at the horizon and write P^-(d)>y for a y-rough integer. The term d=1 is included only where explicitly stated. Define

\[
B_y(k)=\sum_{\substack{d\mid k\\P^-(d)>y}}\Lambda(k/d),
\qquad A_y(k)=B_y(k)-\Lambda(k)
=\sum_{\substack{d\mid k,\ d\ge2\\P^-(d)>y}}\Lambda(k/d).
\tag{1}
\]

Thus A_y is nonnegative and A_y(1)=0. Grouping k=dn in the entire triple sum gives exactly

\[
\boxed{\mathcal C_{y,T}
=\sum_{m,k\ge2}
\frac{\Lambda(m)A_y(k)}{\sqrt{mk}}k_T(\log m,\log k),}
\qquad
k_T(u,v)=\int_0^T h(t-u)h(t-v)\,dt.
\tag{2}
\]

Every sum in (2) is finite by the original pulse support. There is no coprimality restriction and no squarefree restriction on d; every prime-power multiplicity and every earlier history remain.

Write k=a b, where all prime factors of a are <=y and b is y-rough. The Mangoldt support gives the complete classification:

\[
\boxed{
A_y(k)=
\begin{cases}
\log k-\Lambda(k),&a=1,\\
\log p,&a=p^j,\ p\le y,\ j\ge1,\ b>1,\\
0,&a=p^j,\ b=1,\text{ or }a\text{ has at least two distinct primes}.
\end{cases}}
\tag{3}
\]

Indeed, if a=1, the ordinary divisor identity sum_{n|k} Lambda(n)=log k applies. If a=p^j, the only prime-power quotient k/d permitted by roughness of d is p^j itself, so d=b and B_y(k)=log p. If a has two distinct small prime factors, no quotient is a prime power. In particular 0<=A_y(k)<=log k.

This is the actual source coefficient, not an arbitrary positive sequence. It contains rough composites, all repeated rough-prime powers, and integers with one distinct small prime and an arbitrary rough cofactor.

## 2. The complete echo diagonal is small and explicitly paid

If m=k contributes on the diagonal of (2), then m must be a prime power p^j. Formula (3) gives A_y(p^j)=0 for p<=y, and A_y(p^j)=(j-1)log p for p>y. Hence the exact diagonal is

\[
\mathcal D_{y,T}
=\sum_{\substack{p>y\\j\ge2}}
\frac{(j-1)(\log p)^2}{p^j}
k_T(j\log p,j\log p)\ge0.
\]

Retaining all j and using k_T(u,u)<=||h||_2^2 gives

\[
\boxed{0\le\mathcal D_{y,T}
\le\|h\|_2^2\sum_{p>y}\frac{(\log p)^2}{(p-1)^2}
\le C_h\frac{1+\log y}{y}.}
\tag{4}
\]

The geometric identity is sum_{j>=2}(j-1)p^{-j}=(p-1)^{-2}. For the last bound use the elementary Chebyshev estimate theta(u)<=C u and partial summation of sum_{p>y}(log p)^2/p^2. This controls the full echo diagonal uniformly in T, and tends to zero at the prescribed y_T.

For unequal prime-power arguments with the same base prime, the packets are disjoint because their logarithmic spacing is at least log 2>2S. Formula (3), however, also contains non-prime-power k sharing a prime with m. Those contributions have not been removed or declared disjoint.

The remaining sign is entirely the sign of k_T on actual off-diagonal arithmetic pairs. Positivity of Lambda(m)A_y(k) is not positivity of this cross-covariance.

## 3. An independent exact count of the sifted coefficients

Let

\[
\mathcal P_y=\prod_{p\le y}p,\qquad
v_y=\prod_{p\le y}(1-1/p),\qquad
w_y=\sum_{p\le y}\frac{\log p}{p-1}.
\]

The finite divisor identity from the complete rough recurrence gives

\[
B_y=\mu_{\le y}*\log,
\qquad
\mu_{\le y}(d)=
\begin{cases}\mu(d),&d\mid\mathcal P_y,\\0,&\text{otherwise}.\end{cases}
\]

Consequently, for x>=mathcal P_y, the finite sum and elementary log-factorial estimate yield

\[
\begin{aligned}
\sum_{k\le x}B_y(k)
&=\sum_{d\mid\mathcal P_y}\mu(d)
\sum_{n\le x/d}\log n\\
&=x\sum_{d\mid\mathcal P_y}\frac{\mu(d)}d
\bigl(\log x-\log d-1\bigr)
+O\bigl(2^{\pi(y)}\log(2x)\bigr)\\
&=v_y x\bigl(\log x+w_y-1\bigr)
+O\bigl(2^{\pi(y)}\log(2x)\bigr).
\end{aligned}
\tag{5}
\]

The implied constant is absolute and independent of x and y. Every x/d>=1 in this stated range. The exact finite identities used are sum mu(d)/d=v_y and sum mu(d)log(d)/d=-v_y w_y.

Subtracting the actual Chebyshev prime-power function, rather than replacing it by a guessed density, gives

\[
\boxed{\sum_{k\le x}A_y(k)
=v_y x(\log x+w_y-1)-\psi(x)
+O\bigl(2^{\pi(y)}\log(2x)\bigr),\quad x\ge\mathcal P_y.}
\tag{6}
\]

All errors in (6) are independently bounded; the prime term is still exactly psi(x). This is a genuine arithmetic simplification of the full coefficient, not a truncation to a selected sector.

## 4. Complete positive and negative masses at the moving rough cutoff

Now fix the same cutoff as the preceding work:

\[
T\longrightarrow\infty,\quad X=e^T,\quad
y=y_T=\left\lfloor\frac{T}{8\log(T+2)}\right\rfloor,\quad
b_T=T v_{y_T}.
\tag{7}
\]

One has mathcal P_y<=exp(T/8), 2^{pi(y)}=exp(o(T)), and w_y=O(log y)=o(T). Write gamma_E for Euler's constant, distinct from any weighted-energy parameter. Ordinary Mertens' product theorem gives

\[
b_T\sim e^{-\gamma_E}\frac{T}{\log y_T}
\sim e^{-\gamma_E}\frac{T}{\log T}\longrightarrow\infty.
\tag{8}
\]

Only divergence of b_T, not the sharp asymptotic, is needed below. It also follows from an elementary Chebyshev bound: pi(u)<=C u/log u implies v_y>=c(log y)^{-C'}.

Define positive measures

\[
\nu_X=\frac1X\sum_{m\ge2}\Lambda(m)\delta_{m/X},
\qquad
\alpha_T=\frac1{Xb_T}\sum_{k\ge2}A_{y_T}(k)\delta_{k/X}.
\tag{9}
\]

For every fixed r>0, (6) and ordinary PNT imply

\[
\nu_X((0,r])\longrightarrow r,\qquad
\alpha_T((0,r])\longrightarrow r.
\tag{10}
\]

For the second limit the leading multiplier is
r[1+(log r+w_y-1)/T], the exact psi term costs O(r/b_T), and the finite-filter error is exp(-T+o(T))/v_y. No uniform prime-error exponent approaching 1/2 is assumed.

Retain the exact clipped kernel from the complete covariance calculation:

\[
F_h(r,s)=\frac1{\sqrt{rs}}\int_{-\infty}^{0}
h(v-\log r)h(v-\log s)\,dv.
\tag{11}
\]

The extra lower range is exactly zero on actual arithmetic atoms, since every pulse starts after log2-S>0. Thus the complete positive and negative masses in (2), defined according to the sign of k_T, satisfy

\[
\frac{\mathcal C_{y_T,T}^{+}}{Xb_T}
=\iint(F_h)_+\,d\nu_Xd\alpha_T,\qquad
\frac{\mathcal C_{y_T,T}^{-}}{Xb_T}
=\iint(F_h)_-\,d\nu_Xd\alpha_T.
\tag{12}
\]

Here mathcal C=mathcal C^+-mathcal C^-, with both masses nonnegative. These are the signs of the complete regrouped correlation, not separate signs of its arithmetic coefficients.

### The small-index collar is retained

The kernel vanishes unless r,s<=e^S and e^{-2S}<=r/s<=e^{2S}, and |F_h(r,s)|<=||h||_2^2/sqrt(rs). On compact subsets away from zero, (10) proves convergence of the integrals of each kernel sign.

It remains to justify that arbitrarily small indices have no unaccounted contribution. Split m<=epsilon X into m<=X^{1/2} and the remainder.

For m<=X^{1/2}, all interacting k lie between e^{-2S}m and e^{2S}m. The crude actual bound A_y(k)<=log k and Chebyshev's bound imply that the unnormalized absolute pair sum is at most

\[
C_h\sum_{m\le X^{1/2}}\Lambda(m)(1+\log m)
\le C_h X^{1/2}(1+T).
\tag{13}
\]

Dividing by Xb_T sends this to zero. This includes the initial compact source history.

For X^{1/2}<m<=epsilon X, (5) gives uniformly

\[
\sum_{k\le e^{2S}m}A_y(k)
\le\sum_{k\le e^{2S}m}B_y(k)
\le C b_T m.
\tag{14}
\]

Indeed the argument exceeds the full primorial, log(e^{2S}m)<=T+2S, and the finite-filter error exp(o(T))T is negligible against b_T m. Using comparable k in the denominator of (2), this portion has absolute mass at most

\[
C_h b_T\sum_{m\le\epsilon X}\Lambda(m)
\le C_h b_T\epsilon X.
\tag{15}
\]

The union where either m or k is <=epsilon X is contained in m<=e^{2S}epsilon X, by kernel support. Thus (13)-(15) give a normalized collar bound C_h epsilon+o(1). This pays the entire lower collar; the upper clipping was already retained in (11).

### The two exact limiting masses

Every continuum row of F_h vanishes because

\[
\int_0^\infty s^{-1/2}h(v-\log s)\,ds
=e^{v/2}\int e^{-u/2}h(u)\,du=0.
\tag{16}
\]

The half-pole moment is the unchanged source moment. The continuum integrals are absolutely convergent by the same comparable-scale collar estimate. Moreover F_h is positive on a neighborhood of an interior diagonal point where a nonzero source pulse lies before the observation boundary. Therefore

\[
c_h:=\iint(F_h)_+\,dr\,ds
=\iint(F_h)_-\,dr\,ds>0.
\]

Combining (10)-(16) proves

\[
\boxed{
\mathcal C_{y_T,T}^{+}=c_h Xb_T+o(Xb_T),\qquad
\mathcal C_{y_T,T}^{-}=c_h Xb_T+o(Xb_T).}
\tag{17}
\]

Equivalently, each complete sign has the actual-source scale

\[
c_h e^{-\gamma_E}\frac{e^T T}{\log T}(1+o(1)).
\tag{18}
\]

Removing the independently paid diagonal (4) does not change either asymptotic. Nothing in this result asserts that the difference has this size: its leading terms cancel.

## 5. Exact centered arithmetic: the residual contains the negative prime discrepancy

There is a sharper diagnostic than comparing the two large sign masses. The unchanged source also has its first weighted moment zero:

\[
\int u e^{-u/2}h(u)\,du=0.
\tag{19}
\]

Consequently each full continuum row of F_h annihilates both 1 and log s:

\[
\int_0^\infty F_h(r,s)\log s\,ds=0.
\tag{20}
\]

To verify (20), the inner substitution from (16) gives
e^{v/2} integral e^{-u/2}(v-u)h(u)du=0. The logarithmic collar is absolutely integrable; its continuum mass below epsilon is O_h(epsilon(1+|log epsilon|)).

Define, without replacing any arithmetic coefficient,

\[
\nu_{B,T}=\frac1X\sum_{k\ge2}B_y(k)\delta_{k/X},\quad
\Delta_X=\nu_X-dr,\quad
\mathcal E_{y,T}=\nu_{B,T}
-v_y(T+\log r+w_y)\,dr.
\tag{21}
\]

The measure mathcal E is defined on the whole positive line. Formula (5) supplies its independent summatory estimate where x>=mathcal P_y; the earlier range remains in this exact definition. It has not been filled with the large-x formula.

Since A_y=B_y-Lambda, the complete unnormalized rescaled A measure is exactly

\[
\frac1X\sum_{k\ge2}A_y(k)\delta_{k/X}
=[v_y(T+\log r+w_y)-1]\,dr
+\mathcal E_{y,T}-\Delta_X.
\tag{22}
\]

Using both row moments and the ordinary column moment therefore gives the exact signed identity

\[
\boxed{
\frac{\mathcal C_{y,T}}X
=-\iint F_h\,d\Delta_Xd\Delta_X
+\iint F_h\,d\Delta_Xd\mathcal E_{y,T}.}
\tag{23}
\]

Every continuum and mixed term is accounted for. In particular the independent finite-sieve error is not the entire A discrepancy: the negative of the genuine prime discrepancy is also present with coefficient exactly minus one.

The second pairing in (23) is independently paid by the complete rough-source estimate:

\[
\left|X\iint F_h\,d\Delta_Xd\mathcal E_{y,T}\right|
=\left|\int_0^T Z(t)F_y(t)\,dt\right|
\le C_Z I_U\,2^{\pi(y)}.
\tag{24}
\]

This follows by substituting nu_B into the fixed kernel: its exact field is F_y=N_{>y}*Z. The 1 and log continuum profiles vanish by (16),(20), including all clipping and early histories. Thus (23) precisely locates the unsupported line in an attempt to use the independently countable sieve coefficient: the complete prime self-discrepancy remains, with negative sign, after the sieve error has been paid.

## 6. The estimate obtained and the estimate still missing

The regrouping proves the complete signed statement

\[
\mathcal C_{y_T,T}=o\!\left(e^T T/\log T\right).
\tag{25}
\]

It does not prove the required lower

\[
\mathcal C_{y_T,T}\ge-C_\eta e^{\eta T}
\quad\text{at common arbitrarily late horizons for every }\eta>0.
\tag{26}
\]

Indeed, the already paid rough-echo pairing says exactly

\[
\mathcal C_{y_T,T}=-E_Z(T)
+O_h\!\left(2^{\pi(y_T)}\right).
\tag{27}
\]

Equation (17) describes the much larger two sign masses that produce this difference. Equation (27) is retained as an identity with a paid error; it is not used to assume an upper for E_Z.

The ordinary PNT estimate for Z may yield a stronger nonclosing absolute upper than (25). The new information here is the exact coefficient classification, the paid echo diagonal, the asymptotic size of both complete arithmetic signs, and the precise negative prime-discrepancy term left by the independent sieve count. We do not promote (25) as an improvement over every previous rate.

In particular:

- Positive rough and Mangoldt coefficients do not make their packet cross-covariance nonnegative.
- The positive echo diagonal is too small to control the full signed off-diagonal.
- The exact sieve count (6) controls a macroscopic first moment, not the very fine complete signed correlation required in (26).
- The rough cutoff changes the individual sign masses by the factor b_T~T/log T. It does not make their difference independently cheap.

This calculation therefore identifies the actual remaining cancellation after complete arithmetic regrouping. A valid closing improvement has to estimate that signed difference at the requested rates, rather than bound either sign or use the macroscopic density.

## 7. Qualification and references

- [ActualSourceHyperbola.lean at b3afa611](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/OPICARound4/ActualSourceHyperbola.lean): unchanged fields and source.
- COMPLETE_RESIDUAL_RECURRENCE.md: exact rough identity and frozen cutoff.
- ROUGH_ECHO_NATIVE_PAIRING.md: independently paid complete pairing and the closing lower-bound interface.
- COMPLETE_COVARIANCE_ATTEMPT.md and COVARIANCE_REVIEW.md: exact clipped kernel, full continuum moment cancellation and prior covariance qualification. The different moving arithmetic measure alpha_T is established independently in this note.
- [Diamond and Pintz, Oscillation of Mertens' product formula, JTNB 21 (2009), 523-533](https://www.numdam.org/item/JTNB_2009__21_3_523_0/): primary research source explicitly stating the unconditional Mertens product limit used only for the sharp form (8).
- [Fiori, Kadiri and Swidinsky, arXiv:2206.12557v2](https://arxiv.org/abs/2206.12557v2): previously inspected primary unconditional PNT source. The qualitative ordinary PNT and Chebyshev bounds suffice here.

All constants are independent of the observation horizon once h is fixed. No off-line zero was assumed to exist, no selected sector was substituted for the complete source, and no numerical experiment was used as an asymptotic proof. **Step 4 remains OPEN.**
