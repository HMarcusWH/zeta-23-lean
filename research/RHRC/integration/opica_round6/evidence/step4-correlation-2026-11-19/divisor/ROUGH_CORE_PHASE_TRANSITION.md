# Exact divisor covariance, a sharp sieve threshold, and a genuine signed cancellation

**Paper deduction, 19 November 2026. Step 4 OPEN.** The positive energy obtained by grouping actual Möbius divisors according to their factors above \(y\) has a sharp growth transition at \(y=t^2\) on the power scale. For some native terminal windows with \(y\sim(n/8)^8\), the complete contribution between different groups is negative of exponential size at least \(\exp((3/4-o(1))n)\). The proof below uses the actual one-copy source, including all prime powers and the exact integer drive. The smaller residual after cancellation remains open.

## Positive grouping of the genuine divisor equation

Put \(s=1/4096\), \(j=(D^2-1/4)^2q_s\), and
\[
 U(t)=\sum_{k\ge2}\frac{\log k}{\sqrt k}j(t-\log k),\qquad
 P(t)=\sum_{k\ge2}\frac{\Lambda(k)}{\sqrt k}j(t-\log k).
\]
The divisor formula gives \(P=\sum_a\mu(a)a^{-1/2}U(\cdot-\log a)\). Each sum is finite on any bounded horizon. The drive \(U\) begins at \(\log2-s>0\), is nonzero on its isolated first pulse and decays faster than any exponential as \(t\to\infty\). These last bounds follow from Poisson summation on the zero-mass smooth sampling profiles of the integer drive. Thus its bilateral Laplace transform \(\widehat U\) is entire and is not identically zero. [Exact drive and prime source](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeSourceFamily.lean) · Earlier source and Poisson derivation

For \(y\ge2\), set \(P_y=\prod_{p\le y}p\). Every squarefree \(a\) decomposes uniquely as \(r d\), where \((r,P_y)=1\) and \(d\mid P_y\). Define
\[
 V_y(t)=\sum_{d\mid P_y}\frac{\mu(d)}{\sqrt d}U(t-\log d),\quad
 c_r(t)={\bf1}_{(r,P_y)=1}\frac{\mu(r)}{\sqrt r}V_y(t-\log r),\quad
 E_y(t)=\sum_r c_r(t)^2.
\]
Then \(P(t)=\sum_r c_r(t)\). The complete energy is \(P(t)^2=E_y(t)+\sum_{r\ne r'}c_r(t)c_{r'}(t)\), with ordered off-diagonal pairs. All signs within a group are summed before the square.

Uniformly in real \(v\), \(\sum_{r\ge1}r^{-1}|U(v-\log r)|^2\ll_j1\). To see this, divide the arguments \(v-\log r\ge0\) into unit intervals. On each, the harmonic mass of a multiplicative interval of ratio \(e\), truncated below at the integer 1, is at most two. The squared suprema of \(U\) on these intervals are summable. Minkowski on the \(r\)-sequence gives
\[
 \sqrt{E_y(t)}\ll_j\prod_{p\le y}(1+p^{-1/2})
 \le\exp(O(\sqrt y/\log y)).
 \tag{1}
\]
For \(y=n^2\), the full same-group energy at every native node is independently at most \(\exp(O(n/\log n))\). The threshold below shows what happens when this grouping is enlarged.

## Sharp weighted asymptotic for the full filter

Fix \(0<\sigma<1/2\), write \(h=1/2-\sigma>0\), \(u=1/2+\sigma\), \(L_y=y^h/(h\log y)\), \(T_y=y^h/h\). Plancherel gives
\[
 I_\sigma(y):=\int_0^\infty e^{-2\sigma t}|V_y(t)|^2dt
 =\frac1{2\pi}\int_{\mathbb R}|\widehat U(\sigma+i\tau)|^2
       \prod_{p\le y}|1-p^{-u-i\tau}|^2d\tau .
\]
Also
\[
 \int_0^\infty e^{-2\sigma t}E_y(t)dt
 =I_\sigma(y)\prod_{p>y}(1+p^{-1-2\sigma}).
\]
The extra factor tends to one. The following sharp estimate holds for each fixed real \(a\), allowing \(a=0\),
\[
 \log I_{\sigma+a/\log y}(y)=(2e^{-a}+o(1))L_y. \tag{2}
\]

Here are the estimates needed for the matching lower bound. Put \(u_y=u+a/\log y\). PNT and partial summation give \(\sum_{p\le y}p^{-u_y}\sim e^{-a}L_y\). One way to see the moving-exponent factor is to first remove \(p<y^{1-\delta}\), which contributes \(o(L_y)\) for any fixed \(\delta>0\), and then send \(\delta\) to zero. Uniformly near \(\sigma\), \(\sum_p p^{-2u_y}=O_\sigma(1)\). The absolute Euler product gives the upper in (2), with the \(L^2\) norm of the weighted \(U\) bounded uniformly. For a lower integrate on \(|\tau-\pi/\log y|\le(\log y)^{-2}\). On its top prime range, \(-\cos(\tau\log p)\) is uniformly at least \(1-O(\delta^2)-o(1)\); the excluded primes have negligible weight. The real logarithm of the modulus is \(-\sum_{p\le y}p^{-u_y}\cos(\tau\log p)+O_\sigma(1)\). If \(\widehat U\) has a zero of order \(m\) at \(\sigma\) (use \(m=0\) if nonzero), it is bounded below by a positive constant times \((\log y)^{-m}\) throughout this interval, by analytic factorization at \(\sigma\). Its width and this polynomial cost have logarithm \(o(L_y)\). Taking \(\delta\) to zero proves (2). The alignment frequency tends to zero and is distinct from zero. [Plancherel](https://dlmf.nist.gov/1.14) · [Prime number theorem](https://dlmf.nist.gov/27.2)

The positive measures \(I_\sigma(y)^{-1} e^{-2\sigma t}|V_y(t)|^2dt\) concentrate on \(t/T_y\to1\). For \(t\le(1-\epsilon)T_y\), multiply by \(e^{-2at/\log y}\) and use (2) with small fixed \(a>0\). The log probability is at most \(2L_y[a(1-\epsilon)+e^{-a}-1+o(1)]\), a strictly negative multiple of \(L_y\). For \(t\ge(1+\epsilon)T_y\) use (2) with \(-a\), giving \(2L_y[-a(1+\epsilon)+e^a-1+o(1)]\). These estimates hold for every fixed \(\epsilon>0\).

## Sharp growth transition in physical time

For every \(A>0\),
\[
 \limsup_{t\to\infty}\frac1{2t}
   \log\left(1+\sup_{2\le y\le t^A} E_y(t)\right)
 =\max(0,\tfrac12-1/A). \tag{3}
\]
For \(A\le2\), (1) gives the upper and nonnegativity gives the lower. For \(A>2\), take any \(\sigma'\) between \(1/2-1/A\) and \(1/2\). Since \(e^{-\sigma't}U(t)\) is bounded, the absolute filter gives
\[
 E_y(t)\le C_{\sigma'} e^{2\sigma' t}
 \zeta(1+2\sigma')\,\prod_{p\le y}(1+p^{-1/2-\sigma'})^2 .
\]
The logarithm of the product is \(o(t)\) uniformly for \(y\le t^A\). Now decrease \(\sigma'\) to \(1/2-1/A\). For the lower choose \(\sigma=1/2-1/A\) in (2). The concentration just proved gives some \(t\sim T_y=A y^{1/A}\) for which \(|V_y(t)|^2\ge e^{2\sigma t+(2-o(1))L_y}\). Indeed one can let a fixed relative window shrink along a diagonal subsequence and divide its weighted mass by its length \(O(T_y)\); \(\log T_y=o(L_y)\). The index \(y\le t^A\) there and the \(r=1\) term of \(E_y\) suffices. Formula (3) takes a supremum over cutoffs. It does not assert the same lower for every prescribed \(y=t^A\).

The same sharp limsup holds for the native positive terminal quadrature after replacing \(E_y(t)\) by \(\mathcal E_{y,n}=\sum_i w_iE_y(t_i)\) and \(t\) by the integer \(n\). The upper is immediate from the preceding pointwise estimate with \(y\le n^A\), \(t_i\le n\), and total weight \(2\log n\). For the lower, the concentration proof on the disjoint unit intervals gives some integer \(n\sim T_y\) with \(\int_{n-1}^n |V_y(t)|^2dt\ge \exp(2\sigma n+(2-o(1))L_y)\). The full terminal interval contains that unit. To apply the *same* quadrature, expose the exact coefficients
\[
 V_y(t)=\sum_k b_y(k)k^{-1/2}j(t-\log k),\qquad
 b_y(k)=\sum_{d\mid(k,P_y)}\mu(d)\log(k/d).
\]
If \(k\) has no prime factor \(\le y\), this equals \(\log k\). If it has exactly one distinct such factor, it equals \(\log p\) for that prime. For two or more, both the constant sum and the sums attached to each small prime vanish. Thus \(0\le b_y(k)\le\log k\) for all \(k,y\), including prime powers. At \(t\asymp n\) this costs only an extra \(O_j(1+n)\) in the derivative estimate from the original fixed \(j\). The exact original Gauss mesh therefore integrates \(V_y^2\) on the terminal interval with error \(O_j((1+n)^2\log(n)e^{-2n})\) uniformly in \(y\), by the same Taylor estimate and positive weights. At every node \(E_y\ge V_y^2\). Native source, original mesh and error proof

## Exact cost at the boundary \(y=n^2\)

On the subexponential scale the native supremum has the sharper asymptotic upper envelope
\[
 \limsup_{n\to\infty}\frac{\log n}{n}
 \log\!\left(1+\sup_{2\le y\le n^2}\mathcal E_{y,n}\right)=1+\log2. \tag{4}
\]
The continuous-time version holds with \(E_y(t)\) as well.

To prove this, allow a *moving* tilt \(\sigma_y=a/\log y\) with \(a\) fixed. The proof of (2) now gives
\[
 \log I_{a/\log y}(y)=(4e^{-a}+o(1))\sqrt y/\log y.
\]
The quadratic terms in the Euler logarithm are bounded by \(O_a(\sum_{m\le y}1/m)=O_a(\log y)=o(\sqrt y/\log y)\). The \(U\) norm stays bounded on a neighborhood of zero and the earlier analytic-factorization lower handles its possible zero at zero. Tilt by another fixed \(\pm b/\log y\) as in the concentration argument. The new time center is \(T_{y,a}=2e^{-a}\sqrt y\). A weighted unit interval therefore yields some integer \(n\sim T_{y,a}\) with
\[
 \log\int_{n-1}^n |V_y(t)|^2dt
 \ge 2(a/\log y)n+(4e^{-a}-o(1))\sqrt y/\log y
 =(1+a-o(1))\,n/\log n.
\]
Quadrature transfers this lower as above. Take \(0<a<\log2\), so \(y<n^2\) at these horizons, then increase \(a\) to \(\log2\).

For the upper, at integer horizon \(n\) choose \(\sigma'=a/(2\log n)\) with \(a=\log2\), and apply the pointwise absolute Rankin bound to every \(t_i\le n,\ y\le n^2\). The constants for the drive are bounded uniformly for \(0\le\sigma'\le1\) and \(\zeta(1+2\sigma')=O_a(\log n)\). The positive Euler product over \(p\le n^2\) contributes \((2e^{-a}+o(1))n/\log n\) to the energy logarithm by PNT. The time tilt contributes \(a n/\log n\), and total quadrature weight costs \(o(n/\log n)\). Since \(a+2e^{-a}=1+\log2\), this gives (4). In particular a polynomial upper uniform over all paid cutoffs \(y\le n^2\) would fail on this genuine arithmetic system.

## Signed cancellation obtained and remaining estimate

The merged native theorem gives \(\log(1+Q_n)/(2n)\to d\), with \(Q_n=\sum_iw_iP(t_i)^2\) and \(d\) the supremum of rightward zero displacements, using the positive quadrature transfer. The inspected external theorem gives \(d\le b=0.3733458561067185768\ldots<3/8\). Choose \(A=8\), \(\sigma=3/8\). At the horizons established above the *complete ordered distinct-group covariance* satisfies
\[
 \mathcal R_{y,n}:=\sum_i w_i\sum_{r\ne r'}c_r(t_i)c_{r'}(t_i)
 =-\mathcal E_{y,n}+Q_n,\qquad
 \mathcal R_{y,n}\le-\exp((3/4-o(1))n),\qquad y\sim(n/8)^8 .
\]
In fact the ratio \(\mathcal R_{y,n}/\mathcal E_{y,n}\to-1\), with relative error at most \(\exp(-(3/4-2b-o(1))n)\). This calculation establishes an actual large negative signed aggregate for the unaltered arithmetic beyond the block decomposition. Its cancellation precision uses the known external ceiling. Reusing it alone does not improve that ceiling. [Native terminal theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeWindowRate.lean#L1154) · [External comparison](https://github.com/GTimG/QuasiRiemannTracker/blob/42cf5415cfaa4205caaa25ab11160724606cdc33/submissions/2026-11-13-continuum-exact-contact/src/Candidate/Main.lean)

The economy of \(y=n^2\) has a formulation through a thin set of arithmetic pairs. Take \(q=2^{\lfloor\sqrt n\rfloor}\). All nonzero rough cores are odd. Cauchy across the \(\phi(q)\) invertible residues gives
\[
 Q_n\le\phi(q)\left[\mathcal E_{n^2,n}
 +\sum_i w_i\sum_{\substack{r\ne r'\\r\equiv r'\pmod q}}c_r(t_i)c_{r'}(t_i)\right].
\]
Here both \(\phi(q)\) and the complete first term have subexponential size, independently. A one-sided subexponential bound on the signed sum restricted to this single progression of differences, at a cofinal sequence for each requested exponent, suffices to close Step 4. Conversely if \(d>0\), then simultaneously for all \(n^2\)-smooth \(q\le e^{(2d-\epsilon)n}\) (so all relevant cores are units), the restricted cross sum is at least \(\exp(2dn-\log\phi(q)-o(n))\). The threshold can depend on \(\epsilon>0\). A centered progression variance eliminates the principal term algebraically and supplies no upper for it. The signed estimate on the congruent distinct cores, or an equally strong independent input, remains OPEN.

## Positive rough-phase test

Twist only the rough primes at \(y=n^2\) by independent unit-circle phases \(z_p\), extending multiplicatively. Put \(F_i(z)=\sum_r c_r(t_i)z(r)\). The point with every \(z_p=1\) is the genuine source. Haar integration gives \(\sum_iw_i\mathbb E|F_i|^2=\mathcal E_{n^2,n}\). Every active \(r\) has at most \(D\le(n+s)/\log(n^2)\) prime factors. For positive integer \(k\),
\[
 \mathbb E\left(\sum_i w_i |F_i|^2\right)^k
 \le k^{kD}\mathcal E_{n^2,n}^k .
\]
Indeed orthogonality of monomials groups ordered \(k\)-tuples by the product of their entries. Each fibre has at most \(k^{kD}\) tuples by assigning the at most \(kD\) prime occurrences to \(k\) slots. Apply Cauchy within fibres and then Minkowski in \(L^k\) across the positive observation weights. Consequently for \(0<\nu<4\lambda\) and \(k=\lfloor n^{4\lambda-\nu}\rfloor\), the probability of energy at least \(e^{2\lambda n}\) is at most \(\exp(-c_\nu n^{1+4\lambda-\nu})\) for sufficiently large \(n\). The same finite moments hold on Dirichlet characters of any prime modulus exceeding \(e^{k(n+s)}\), by ordinary character orthogonality and unique factorization. The principal character is just one point in this much larger family. Rarity alone gives no bound on the value at that distinguished point. This distinction preserves the entire coupling at the unpaid step.

**Status.** Paper deductions and a finite arithmetic replay. No new Lean or production CI result is claimed by this note.
