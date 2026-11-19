# One signed prime sum per order for Step 4

**19 November 2026. Paper result.** Starting from the complete one-copy OPICA prime-power field, the vertical norm in the [fixed-line derivative test](../../step4-correlation-2026-11-19/shift/FIXED_LINE_JETS.md) can be replaced by the absolute value of **one explicit complex number per order**. It uses only Taylor coefficients of absolutely convergent Euler series near the real point \(s=3/2\). At every sufficiently large order, a rightward zero would force exponential growth of this number, even if several poles tie for the largest unmodulated contribution. A uniform arithmetic upper on an unbounded subsequence remains **OPEN**.

## The arithmetic quantity

Let \(P(t)=\sum_m\Lambda(m)m^{-1/2}j(t-\log m)\) with the actual compact one-copy \(j\), and \(J(z)=\int e^{-zv}j(v)dv\). Write \(F(z)=-J(z)(\zeta'/\zeta)(1/2+z)\), the Laplace transform of \(P\) in \(\Re z>1/2\). Let \(L_n(x)=\sum_{k=0}^n\binom nk(-x)^k/k!\), \(\tau_n=(n+1)^{-1/3}\), \(z_n=1+i\tau_n\). Define the following equivalent numbers:
\[
 b_n=\sqrt2\int_0^\infty e^{-z_n t}L_n(2t)P(t)dt
 =\sqrt2\sum_{k=0}^n2^k\binom nk\frac{F^{(k)}(z_n)}{k!}. \tag{1}
\]
Integration gives the middle form directly from the Laguerre polynomial. For each fixed \(n\) the field expansion gives the single absolutely convergent signed prime-power sum
\[
 b_n=\sqrt2\sum_{m\ge2}\frac{\Lambda(m)}{m^{3/2+i\tau_n}}
       \int_{-s}^s j(v)e^{-z_n v}L_n(2\log m+2v)dv,\qquad s=1/4096 . \tag{2}
\]
There is no moving prime cutoff, squared response, time window, or integral over a vertical frequency line to estimate in (2). For fixed \(\tau\) these are the Taylor coefficients at \(w=0\) of \(\sqrt2 F(i\tau+(1+w)/(1-w))/(1-w)\). The generating identity follows from \(\sum_{n\ge0} L_n(x)w^n=(1-w)^{-1}e^{-xw/(1-w)}\) initially in a sufficiently small disk. Equation (1) samples a separately prescribed \(\tau_n\) at each order. The source and the polynomial family are the existing OPICA ingredients. This is related to the classical conformal viewpoint on Li coefficients but uses a different coefficient sequence, the original local source and a vanishing modulation. [Native source](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeSourceFamily.lean) · [OPICA Laguerre calculus](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/MultiplicityTail.lean) · [Bombieri and Lagarias](https://websites.umich.edu/~lagarias/doc/bombieri.pdf)

## What one hypothetical zero forces at every late order

Write \(p=\rho-1/2=\delta+i\gamma\). With multiplicities consolidated let \(a_p=-m_\rho J(p)\). The native explicit formula and fixed-source estimates give
\[
 P(t)=\sum_p a_p e^{pt}+B(t)\quad(t\ge0),\qquad \sum_p|a_p|<\infty,\quad B\in L^2(0,\infty).
\]
On \([0,1]\) this *defines* the correction using the true initial field. Beyond 1 the remaining term is the exponentially decaying trivial-zero series. The bounds in the fixed-sieve certificate give \(\|B\|_2<10^{32}\): the critical absolute weights sum to less than \(10^{31}\), the off-line weights sum to less than \(e^{-53890}\), and the initial field costs less than \(10^{31}\). On \([0,1]\) multiply the weights by at most \(e^{1/2}<2\). On \(t\ge1\), compact support bounds the trivial-zero series by \(2\|j\|_1 e^{-2(t-1)}\). Every rightward zero has \(a_p\ne0\) by the nonvanishing of the one-copy sinc product off its imaginary Laplace axis. [Native explicit formula](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeExplicitFormula.lean) · [Source and finite-height bounds](../../step4-correlation-2026-11-19/FIXED_SIEVE_SIGN.md)

The functions \(\ell_n(t)=\sqrt2 e^{-t}L_n(2t)\) are orthonormal on \([0,\infty)\). The contribution of \(B\) to (1) is at most \(\|B\|_2\) and in fact tends to zero: ordinary Bessel orthogonality applies to \(B\), and \(\|(e^{-i\tau_n t}-1)B\|_2\to0\). Integration of each mode gives the exact expression
\[
 b_n=\sqrt2\sum_p\frac{a_p}{1-p+i\tau_n}r_p(\tau_n)^n+o(1),\qquad
 r_p(\tau)=\frac{-1-p+i\tau}{1-p+i\tau},\quad
 |r_p(\tau)|^2=1+\frac{4\delta}{(1-\delta)^2+(\gamma-\tau)^2}. \tag{3}
\]
For each order the absolutely summable mode weights are integrated against a polynomial times \(e^{-(1-d)t}\). If there is no rightward zero, every multiplier has modulus at most one, so \(|b_n|<10^{33}\) for every \(n\).

If any rightward zero exists, \(R=\max_p|r_p(0)|>1\) is **attained**. As \(|\gamma|\to\infty\), the moduli tend uniformly to 1 for \(|\tau|\le1\), since \(|\delta|\le1/2\). Thus a finite set of poles attains \(R\), and the others have a fixed gap below \(R\) for sufficiently small \(|\tau|\). To disentangle all ties in the finite set, minimize the following score there:
\[
 h_p(\tau)=\frac{(1-\delta)^2+\gamma^2}{\delta}
     -\frac{2\gamma}{\delta}\tau+\frac1\delta\tau^2.
\]
Distinct poles have different polynomials: equal quadratic and linear coefficients force equal displacement and ordinate. For every sufficiently small positive \(\tau\), the lexicographically least coefficient triple picks one unique \(p_*\). Every originally tied competitor has \(h_p(\tau)-h_{p_*}(\tau)\ge c\tau^2\), with fixed \(c>0\) if competitors exist. Since \(h\mapsto\tfrac12\log(1+4/h)\) has strictly negative derivative on the finite neighborhood of their positive score, its relative modulus costs at least \(e^{-c' n\tau_n^2}\). This tends to zero. The infinite nonmaximal tail has a fixed ratio below one and summable residues. The surviving residue has a nonzero limiting prefactor. Consequently
\[
 b_n=\frac{\sqrt2 a_{p_*}}{1-p_*+i\tau_n}\,r_{p_*}(\tau_n)^n(1+o(1)),\qquad
 \lim_{n\to\infty}|b_n|^{1/n}=R>1 . \tag{4}
\]
This holds without a simple-zero assumption, a nearest-pole uniqueness assumption at zero modulation, or attainment of the unweighted displacement supremum. The quadratic tie-breaking argument uses \(n\tau_n^2\to\infty\). At fixed zero modulation conjugates can cancel at some orders. The choice of modulation precedes the unknown zero configuration.

For actual zeta an even smaller modulation would work. If two distinct tied right poles also shared the linear score coefficient, they would have \(\gamma_1/\delta_1=\gamma_2/\delta_2=c\) and \(\delta_1\delta_2=1/(1+c^2)\) by equality of the constant coefficients. Thus \(\gamma_1\gamma_2+\delta_1\delta_2=1\), impossible for same-sign ordinates of magnitude greater than one. The actual verified height is far larger. Hence all genuine ties split already to first order. One may replace the specified rule throughout the asymptotic criteria by \(\tau_n=\log(n+2)/(n+1)\), since \(n\tau_n\to\infty\) and \(n|\tau_{n+1}-\tau_n|\to0\). The finite samples below use the original cube-root rule.

Combining the cases, the following is a sufficient and necessary arithmetic target:
\[
 \boxed{\ d=0\iff |b_n|\le 10^{33}\ \text{for arbitrarily large integers }n.\ } \tag{5}
\]
More weakly, \(\liminf \log(1+|b_n|)/n=0\) is equivalent. These statements relate the source directly to the fixed-sieve sign and native-window energy without a new premise at the transfer stage. No separate estimate of (2) at unbounded orders has been established.

## An all-order evaluation of every higher-prime-power contribution

The aggregate of all powers \(p^\nu\), \(\nu\ge2\), in (2) admits an independent asymptotic. Write their time field as \(H\). Every even exponent is counted exactly by \(\sum_{m\ge2}\Lambda(m)m^{-1}j(t-2\log m)\), because \((p^k)^2=p^{2k}\) and \(\Lambda(p^k)=\log p\). Remaining odd exponents are at least three. Counting their possible bases and exponents on \(p^\nu\asymp e^t\) bounds their field by \(O_j((1+t)^2 e^{-t/6})\). For the even part use Stieltjes integration with \(\psi(x)=x+E(x)\). The continuum integral is exactly \(\tfrac12\int j=J(0)/2=1/32\) at sufficiently late times. The error is
\[
 \int E(x)x^{-2}\big[j(t-2\log x)+2j'(t-2\log x)\big]dx,
\]
with zero endpoint terms. The published unconditional bound \(|E(x)|\ll x(\log x)^2 e^{-c\sqrt{\log x}}\) and compact support make this \(O_j((1+t)^2e^{-c'\sqrt t})\). Therefore \(H-1/32\in L^2(0,\infty)\), retaining the finite initial interval. Applying the same Bessel argument as above and integrating the constant gives the actual all-order compensation
\[
 b_n(H)=\frac{\sqrt2}{32(1+i\tau_n)}
      \left(\frac{-1+i\tau_n}{1+i\tau_n}\right)^n+o(1). \tag{6}
\]
Thus the unknown in (5) can be tested directly on the first-prime sum with this explicitly restored bounded term. In particular a cofinal subexponential upper for the first-prime scalar suffices. The ordinary prime number theorem controls the twice-log-scaled channel here; the remaining first-prime channel has no corresponding factor of two. [Johnston and Yang, unconditional prime-number-theorem error](https://arxiv.org/abs/2204.01980)

## Two first-prime ranges are independently paid at every large order

Set \(u=\log m\) and \(f(t)=e^{-i\tau t}j(t-u)\) with \(|\tau|\le1\). The Laguerre equation gives \(\mathcal L\ell_n=(2n+1)\ell_n\) for \(\mathcal L f=-(tf')'+tf\). Repeated integration by parts is legitimate because the whole support of \(f\) is contained in \((0,\infty)\). Thus
\[
 \left|\int\ell_n(t)f(t)dt\right|
 \le(2n+1)^{-k}\|\mathcal L^kf\|_2
 \le 2^{120}\sqrt{2s}\left[\frac{2^{65}(1+u)k^4}{n}\right]^k\quad(n,k\ge1). \tag{8}
\]
Here are details of the derivative budget. Differentiating \(r\) of the native uniform boxes and bounding the next density gives \(\|q^{(r)}\|_\infty\le s^{-r-1}(r!)^2(r+1)^2(r+2)/2\le 2^{20(r+1)}(r!)^2\). In \(j=q^{(4)}-q''/2+q/16\), use \((r+4)^8\le2^{8(r+2)}\) to obtain \(\|j^{(r)}\|_\infty\le2^{120+28r}(r!)^2\). Modulation increases \(2^{28r}\) to at most \(2^{29r}\). For \(r\le2k\), divide derivatives by \(B^r\), \(B=2^{31}k^2\), obtaining a seminorm at most \(2^{120}\). Applying \(\mathcal L\) once costs at most \(4(1+u)B^2\) and two available derivatives, since
\[
 D^r\mathcal L f=-t f^{(r+2)}-(r+1)f^{(r+1)}+tf^{(r)}+r f^{(r-1)}.
\]
The final term is zero at \(r=0\). Iteration keeps the support and proves (8). The source box widths are exactly \(s/(m(m+1))\), \(m\ge1\). [Pinned native widths](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/CCM/UniversalSincDetector.lean#L35)

Choose \(k=\lfloor[n/(2^{69}(1+u))]^{1/4}\rfloor\) when the floor argument is at least two. Otherwise use \(\|f\|_2\). This proves a uniform one-pulse estimate
\[
 \left|\int \ell_n f\right|\le 2^{122}\exp\{-2^{-19}[n/(1+u)]^{1/4}\}.
\]
Consequently with the explicitly fixed \(a=2^{-20}\), the sum of the absolute values of all source-pulse contributions with \(\log m\le a n^{1/5}\), with the genuine \(\Lambda(m)/\sqrt m\) weights, is \(O_j(e^{-2^{-17}n^{1/5}})\) as \(n\to\infty\). Indeed \(\sum_{m\le e^U}(\log m)/\sqrt m\ll(1+U)e^{U/2}\), and \(1+U\le2a n^{1/5}\) for large \(n\). The negative exponent coefficient \(2^{-19}(2a)^{-1/4}\) exceeds \(a/2+2^{-17}\). Oscillation was used inside each actual pulse before summing the absolute weights; replacing \(j\) or the Laguerre polynomial by its absolute value inside the integral would lose this saving.

At the opposite end, Cauchy's estimate at \(|w|=1/8\) in the generating function gives \(|\ell_n(t)|\le (8\sqrt2/7)8^ne^{-7t/9}\), because \(\Re((1+w)/(1-w))\ge7/9\). For \(\log m\ge8(n+1)\), summing the pulse bounds with \(t\ge\log m-s\) costs
\[
 O_j\left(8^n\sum_{m\ge e^{8(n+1)}}(\log m)m^{-23/18}\right)
 =O_j\big((1+n)e^{-(20/9-\log8)n}\big), \tag{9}
\]
and \(20/9>\log8\). In (8) and (9) all constants are independent of the primes and the order. Let \(M_n\) be the finite first-prime part of (2) with \(2^{-20}n^{1/5}<\log p<8(n+1)\). Equations (6), (8) and (9) give the **unconditional, all-order arithmetic** reduction
\[
 b_n=M_n+\frac{\sqrt2}{32(1+i\tau_n)}
      \left(\frac{-1+i\tau_n}{1+i\tau_n}\right)^n+o(1). \tag{10}
\]
In particular it suffices to bound the modulus of this single intermediate first-prime sum by \(10^{33}-1\) at arbitrarily high orders. If a subexponential rather than fixed upper is sought, the lower endpoint can be raised further to \(n/\log(n+2)\): Cauchy at \(|w|=n/(n+1)\) gives \(|\ell_n(t)|\le\sqrt2 e(n+1)\) for all \(t\ge0\). The aggregate between the two lower cutoffs then costs \(\exp(o(n))\) by the same elementary weight count. Thus the cofinal subexponential test needs only primes in \(n/\log(n+2)<\log p<8(n+1)\). All omitted contributions have an independent bound stated above. No cofinal estimate on that remaining signed range has been proved.

## A neighboring-order test and zero reconstruction

Equation (4) also fixes the **complex ratio**, not only the size. If \(d>0\), \(n|\tau_{n+1}-\tau_n|\to0\). On a neighborhood of zero modulation the multiplier of the selected pole has a nonzero analytic logarithm. Thus \([r_{p_*}(\tau_{n+1})/r_{p_*}(\tau_n)]^n\to1\); its prefactor ratio also tends to one. Consequently
\[
 \lim_{n\to\infty}\frac{b_{n+1}}{b_n}
 =\lim_{n\to\infty}\frac{M_{n+1}}{M_n}
 =r_*=-\frac{1+p_*}{1-p_*},\qquad
 p_*=\frac{r_*+1}{r_*-1} . \tag{11}
\]
The bounded difference in (10) costs an exponentially vanishing relative error here. The selected zero \(1/2+p_*\) maximizes the unmodulated Cayley score with the specified tie rules; it need not maximize horizontal displacement itself. The residue factor in (4), with \(J(p_*)\ne0\), also determines its multiplicity. This is conditional reconstruction from asymptotic arithmetic data and identifies no new actual zero.

Define \(S_n=M_n\), or use \(S_n=b_n\). The forward ratio has modulus \(>1\) if \(d>0\), whereas \(S_n\) is bounded if \(d=0\), by (10). Therefore an equivalent target requiring *only two neighboring orders* is
\[
 \boxed{\quad d=0\iff
   \frac{1+|S_{n+1}|}{n+1}\le\frac{1+|S_n|}{n}
   \quad\text{at arbitrarily large integers }n\ge1 .\quad} \tag{12}
\]
For the bounded case the positive normalized sequence tends to zero and must have arbitrarily late nonincreases. In the positive-displacement case the successive ratio of the normalized values tends to \(|r_*|>1\). This test avoids fixing an upper on the absolute size of the arithmetic sum. With \(M_n\) it consists solely of two finite, source-specific prime sums on the prescribed bands, with all other contributions accounted for. Proving that these nonincreases recur for genuine primes remains open. A demonstration that finite local evidence and positive Euler factors cannot enforce the recurrence appears in the [Euler-tail falsification](EULER_TAIL_FALSIFICATION.md).

For the full \(S_n=b_n\), 160-bit interval Taylor calculations at orders 0 through 18 certify strict decreases at \(n=4,5,6,7,8,15,16,17\). The calculation uses the complete zeta logarithmic derivative, the exact variance of the compact even seed, and a uniform remainder bounded from its support. These are eight actual finite instances of the comparison in (12). They establish no cofinal occurrence. [Calculations and intervals](CAYLEY_CHECK.json) · [Reproduction script](check_cayley.py)

## Finite verified range and sensitivity at high ordinate

At all orders \(0\le n\le 648\cdot10^{27}\), **\(|b_n|<10^{33}\)**, conditional only on the published finite verification and external zero-free ceiling used in the fixed-sieve checkpoint. Explicitly, the critical terms cost at most \(\sqrt2\,10^{31}\) at every order and the time correction costs \(10^{32}\). All off-line weights together cost less than \(e^{-53890}\), have \(|\gamma|>H_0=3\cdot10^{12}\), and have \(\delta<0.374\). For \(0\le\tau_n\le1\), their possible logarithmic gain is at most \(2(0.374)n/(H_0-1)^2<53857\) at the upper endpoint. Also \(|1-p+i\tau_n|\ge1/2\). This yields the displayed uniform finite upper without evaluating each single coefficient. The very large order reflects the \(\gamma^{-2}\) sensitivity of this transform near its real center and uses exactly the same finite-height input as before. [Finite-height and source-weight bounds](../../step4-correlation-2026-11-19/FIXED_SIEVE_SIGN.md) · [Exact scalar checks](CAYLEY_CHECK.json)

Even at unbounded orders, every zero at \(|\gamma|>(128n)^{2/5}\) collectively pays at most a fixed tiny contribution when restricted to the unverified range. In fact if a contrary observation \(|b_n|\ge10^{33}\) ever occurs, one specific rightward zero must satisfy
\[
 |\gamma|>3\cdot10^{12},\qquad
 n\delta> (|\gamma|-1)^2\sqrt{|\gamma|}/256,
 \qquad |\gamma|<(128n)^{2/5}. \tag{7}
\]
If every unverified rightward zero missed the middle inequality, then \(n\log|r_p|\le\sqrt{|\gamma|}/128\). In the bin \(m=\lfloor\sqrt{|\gamma|}\rfloor\), the native unamplified absolute weights cost at most \(3000(m+2)^{15}e^{-m/32}\), with both signs and all multiplicities. The amplified tail is consequently bounded by \(3\cdot3000\sum_{m\ge1732050}(m+2)^{15}e^{-(3m-1)/128}<1\). Together with the initial and critical terms this contradicts the observation. Using \(\delta<0.374\) and \(|\gamma|>3\cdot10^{12}\) gives the last inequality. This simultaneously localizes displacement and height on the same zero. No contrary observation was obtained.

## What the alternative approaches establish

* **Fixed-radius Cauchy estimates.** On a circle lying in \(\Re z>1/2\) all ordinary Euler derivatives are legitimate. The disk in the Cayley variable reaching the whole right half-plane contains precisely the nonremovable rightward poles under test. A bound obtained by assuming analyticity throughout it assumes the needed exclusion. The actual source kills the pole at \(z=1/2\) and keeps the residues at the unknown rightward zeros.
* **Turán and zero density.** A power-sum argument detects an existing pole. Equation (4) strengthens the detection by choosing the modulation before looking for a zero. A density upper allows a single rightward zero at arbitrarily high ordinate, whose weight in (3) is tiny but whose fixed multiplier eventually exceeds one exponentially. Ingham-type explicit bounds and the recent improvements in short strips estimate counts, not the exclusion needed for the cofinal arithmetic upper. [Chourasiya and Simonič](https://arxiv.org/abs/2507.15184) · [Ye, short-strip theorem and its parameter range](https://arxiv.org/abs/2610.15989)
* **Positivity and log-convexity.** The unnormalized moments of \(P^2\) are log-convex by Cauchy–Schwarz. Convexity bounds interior values from above when endpoints are supplied; it gives no upper on later values from an initial segment. The modulated \(b_n\) themselves are complex signed quantities. Dropping the source sign also destroys its double cancellation at the Euler pole: replacing \(j\) by \(|j|\) gives a nonzero residue at \(z=1/2\), whose multiplier in (3) tends to 3. The other poles have smaller limiting modulus by the zero-free ceiling; equivalently the isolated pole dominates in a sufficiently small closed Cayley disk. Thus taking absolute values at the level of the source cannot yield the cofinal bound.

**Outstanding arithmetic.** Prove, directly from the signed first-prime sum in (2), a cofinal subexponential upper with the prescribed single polynomial and frequency at each order, or find an independent closing inequality. The finite bound, the known higher-power term and the reduction to a unique dominant hypothetical mode do not prove that final estimate.
