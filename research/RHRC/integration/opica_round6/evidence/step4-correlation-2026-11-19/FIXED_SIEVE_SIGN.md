# One fixed arithmetic sign test for Step 4

**19 November 2026. Paper theorem with a finite interval certificate.** Set the prime cutoff permanently to \(Y=10{,}000{,}000\). Use the complete one-copy OPICA field. On the terminal window \([n-2\log n,n]\), sum all signed interactions between Möbius divisors that have *different* squarefree parts above \(Y\). Call that number \(R_Y(n)\), using the continuous integral below. Then
\[
 \boxed{\quad d=0\quad\Longleftrightarrow\quad
           R_Y(n)\le 0\ \text{for arbitrarily large integers }n .\quad}       \tag{1}
\]
Here \(d\) is the supremum of the rightward displacements of the actual nontrivial zeta zeros. The sign test fixes the cutoff and uses zero as its comparison value. Published finite zero verification and interval calculations give the sign on 50,001 consecutive native windows. Adding the external zero-free half-plane extends this to 94,001. The [all-horizon diagonal estimate](ALL_HORIZON_DIAGONAL.md) makes the starting horizon explicit for the universal conditional statement. The independent proof of arbitrarily late recurrence remains OPEN.

## Definition and the two possible late behaviors

Write \(j=(D^2-1/4)^2q_s,\ s=1/4096\), \(S_m f(t)=m^{-1/2}f(t-\log m)\), \(U(t)=\sum_{k\ge2}(\log k)k^{-1/2}j(t-\log k)\), and \(P(t)=\sum_{k\ge2}\Lambda(k)k^{-1/2}j(t-\log k)\). Let
\[
 \Pi_Y=\prod_{p\le Y}p,\quad V_Y=\sum_{a\mid\Pi_Y}\mu(a)S_a U,\quad
 c_r={\bf1}_{(r,\Pi_Y)=1}\mu(r)S_r V_Y.
\]
Non-squarefree \(r\) vanish. The genuine identity \(\Lambda=\mu*\log\) gives \(P=\sum_r c_r\). Set
\[
 E_Y(t)=\sum_r c_r(t)^2,\qquad
 R_Y(n)=\int_{n-2\log n}^n \sum_{r\ne r'}c_r(t)c_{r'}(t)\,dt.
\]
All pairs are ordered and summed with signs. Every sum at a finite horizon is finite. The grouping is over the actual divisors of the same drive. It includes every higher prime power. [Native source and histories](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeSourceFamily.lean) · [Divisor estimates](COPRIME_DIVISOR_ENERGY.md)

For each *fixed* \(Y\),
\[
 E_Y(t)\longrightarrow L_Y
 =\left(\prod_{p\le Y}(1-1/p)\prod_{p>Y}(1-1/p^2)\right)
    \int_0^\infty |V_Y(u)|^2du .                                           \tag{2}
\]
Indeed the counting function of squarefree integers coprime to \(\Pi_Y\) is \(c_Y x+o(x)\) for the displayed density \(c_Y\). This follows by inclusion–exclusion on the finitely many small primes and truncating the square divisors, whose density tail is at most \(\sum_{k>K}k^{-2}\). On compact ranges of \(u=t-\log r\) partial summation then makes \(r^{-1}\)-weighted sampling converge to \(c_Y\,du\). On the remaining half-line \(V_Y\) decays faster than any exponential since the small-prime operator is fixed and finite. Each unit log interval has harmonic mass at most two. These facts justify the infinite tail in (2). In particular \(L_Y\) is a finite, source-fixed number whether or not RH holds.

If \(d>0\), the merged native theorem gives \(\int_{n-2\log n}^n |P|^2=\exp((2d+o(1))n)\). By (2) the corresponding integral of \(E_Y\) is \((2L_Y+o(1))\log n\). Hence \(R_Y(n)\) is positive at every sufficiently late integer. [Native terminal-window theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeWindowRate.lean#L1154)

If \(d=0\), the native explicit formula at \(t\ge1\) gives \(|P(t)|<10^{31}\), as verified below. In fact the uniform absolute convergence of the critical-line exponential sum implies the sharper mean
\[
 \frac1{2\log n}\int_{n-2\log n}^n P(t)^2dt
 \longrightarrow \sum_{\gamma\ {\rm distinct}}m_\gamma^2|J(i\gamma)|^2,
 \qquad J(z)=\int e^{-zv}j(v)dv .
\]
Integrate finite exponential sums first, combining equal ordinates. Each off-diagonal frequency difference has interval average tending to zero independent of the starting time. The uniform absolute tail and the decaying trivial-zero contribution justify the limit. Our certificate gives \(L_Y>10^{73}\), comfortably above the \(10^{62}\) upper for that mean. Consequently \(R_Y(n)/(2\log n)\) approaches a strictly negative number in this case. These two alternatives prove (1). The same cofinal equivalence holds for the fixed positive terminal quadrature in the preceding checkpoint: its full field has the same exponential rate, the conditional pointwise upper applies at every node, and the smallest node tends to infinity in (2). The bounded finite-horizon result below uses continuous integration.

## Certifying the size comparison for the specified cutoff

Plancherel at real frequency gives the integral of \(|V_Y|^2\) as
\[
 I_Y=\frac1{2\pi}\int_{\mathbb R}|J(i\tau)\zeta'(1/2+i\tau)|^2
       \prod_{p\le Y}|1-p^{-1/2-i\tau}|^2\,d\tau .
\]
The transform of \(U\) is \(-J(z)\zeta'(1/2+z)\), initially in the region of absolute arithmetic convergence and then by continuation. The double source zero removes the pole; the fast tail of \(U\) justifies Plancherel on the displayed line. On the single interval \(0.199\le\tau\le0.200\), the routine using Arb interval arithmetic encloses \(|\zeta'(1/2+i\tau)|\) above one. Evenness, unit mass and \(\cos(\tau v)\ge1-\tau^2s^2/2\) give \(|J(i\tau)|>1/32\).

For \(p<3000\), the squared log-factor is bounded below by \(-2/(\sqrt p-1)\). Between 3000 and \(10^6\) the cosine of \(\tau\log p\) is nonpositive. For \(10^6\le p\le10^7\) the angle lies between \(5\pi/6\) and \(7\pi/6\), and the squared log-factor exceeds \(3/(2\sqrt p)\) using \(\log(1+x)\ge x/(1+x)\). The sieve counts 586,081 primes in that last range. Summing the losses and gains with rational lower bounds proves that the logarithm of the squared Euler product exceeds 200 throughout the interval. The squarefree density is at least \(1/(Y+1)\), by inserting all integers in the two elementary products and telescoping. Thus
\[
 I_Y>\frac{e^{200}}{2\pi\,1000\,32^2}>10^{80},\qquad L_Y>10^{73}.
\]

For the critical-line response use \((1/4+\gamma^2)|J(i\gamma)|\le\|j''\|_1+\|j\|_1/4\). The Hadamard formula at zero and one, with the functional equation, gives
\[
 \sum_\rho\Re\left(\frac1{\rho}+\frac1{1-\rho}\right)
      =2+\gamma_{\!E}-\log(4\pi)<1.
\]
Each term is positive, and on the line equals \(1/(1/4+\gamma^2)\), with multiplicity retained. The sum of the absolute critical contributions therefore costs at most \(\|j''\|_1+\|j\|_1/4\) even in the presence of other zeros. At \(t\ge1\) the trivial-zero series costs at most \(\|j\|_1\) by the source support. To bound the norms, differentiating the first \(m\) uniform boxes in \(q_s\) and bounding the next box gives
\(\|q_s^{(m)}\|_1\le s^{-m}m!(m+1)!(m+1)(m+2)\).
The certificate checks \(\|j''\|_1+2\|j\|_1+1<10^{31}\). [Native explicit formula and trivial series](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeExplicitFormula.lean) · [Completed zeta function](https://dlmf.nist.gov/25.4) · [Executable certificate](check_fixed_sieve.py) · [Numerical receipt](FIXED_SIEVE_CONSTANTS.json)

## Every actual continuous terminal window from 50,000 through 100,000

For every integer \(50000\le n\le100000\), **\(R_Y(n)<-10^{74}\)** with exactly the fixed \(Y\) in (1). This covers a bounded range of horizons.

First, every nontrivial zero of ordinate at most \(H_0=3\cdot10^{12}\) in absolute value is on the critical line by Platt and Trudgian. For the full contribution above this height write \(g=|\Im\rho|\), \(p=\rho-1/2\). The one-copy source bound in the previous checkpoint gives
\[
 |J(p)|\le e^5(g+2)^4(1+\sqrt{sg})^3 e^{-\sqrt g/32}.
\]
This uses a single sinc product, hence the denominator 32 in the exponent. The previous zero count \(N((m+1)^2)\le10(m+2)^4\) and both signs of the ordinate give the total absolute weight above \(H_0\) at most \(3000\sum_{m\ge1732050}(m+2)^{15}e^{-m/32}< e^{-53890}\). The geometric ratio and prefactors are checked in the new scalar certificate. For \(t\le100000\), even the elementary strip bound \(\Re p\le1/2\) keeps this tail below one. Count the critical terms once and use the tail only for remaining off-line terms. For \(0\le t\le1\) a direct count of the initial atoms and \(\|j\|_\infty<10^{24}\) suffices. This proves the actual \(|P(t)|<10^{31}\) over the stated finite range. [Verified zero height](https://arxiv.org/abs/2004.09765) · Sinc estimate and earlier explicit zero-count references

Second, essentially all the lower bound for \(I_Y\) above is captured before \(t=42000\). The elementary second-order Euler summation estimate on \(F(z)=z^{-1/2}j(-\log z)\) and \(\log(z)F(z)\) gives \(|U(t)|\le10^{40}(1+t)e^{-3t/2}\) for \(t\ge0\). Both integrals vanish by the source moments. For example \(\max_{0\le m\le2}\|j^{(m)}\|_\infty<10^{34}\) by the box bounds. On \([e^{-s},e^s]\subset[1/2,2]\) the product and chain rules bound the sum of the two second-derivative \(L^1\) norms by \(10^{39}\). The weighted drive norm consequently satisfies \(\int e^{t/5}|U(t)|^2dt<10^{82}\). Translating it through the finite Euler operator gives
\[
 \int_{42000}^\infty |V_Y(t)|^2dt
 \le e^{-8400}10^{82}\prod_{p\le Y}(1+p^{-2/5})^2<1 .
\]
The sieve certificate groups the primes in intervals \([2^{5k},2^{5(k+1)})\) and proves \(\sum_{p\le Y}p^{-2/5}<4000\). This proves \(\int_0^{42000}V_Y^2>10^{80}-1\).

For \(n\ge50000\) and \(0\le u\le42000\), put \(X=e^{n-u}\). Every prime \(X/10<p\le X\) exceeds \(Y\), is squarefree, and satisfies \(u+\log p\in[n-\log10,n]\), inside the native window. The explicit bounds \(x/\log x<\pi(x)<1.25506\,x/\log x\) in the applicable range imply that the harmonic sum of these primes exceeds \(0.8/\log X\ge0.8/n\), since \(\log X\ge8000\). Use just these nonnegative square terms of \(E_Y\), changing variables \(u=t-\log p\) separately for each prime and applying Tonelli:
\[
 \int_{n-2\log n}^n E_Y(t)dt
 \ \ge\ \int_0^{42000} V_Y(u)^2
       \sum_{e^{n-u}/10<p\le e^{n-u}}\frac1p\,du
 \ >\ \frac{0.8}{n}(10^{80}-1).
\]
For \(50000\le n\le100000\) the full \(P^2\) integral is below \(24\cdot10^{62}\) by the finite zero-height calculation. Their difference is less than \(-10^{74}\). This establishes the sign on the actual complete field analytically throughout those windows. There was no pointwise enumeration of their prime atoms. [Rosser–Schoenfeld, inequalities (3.5)–(3.6)](https://doi.org/10.1215/ijm/1255631807)

The independently verified external ceiling \(b<0.374\) extends the upper endpoint to **144,000**, or **94,001 consecutive windows** starting at 50,000. The high-ordinate bound becomes \(\exp(-53890+0.374\cdot144000)=e^{-34}<1\). Also \(2\log 144000<24\), and the same lower bound with \(n=144000\) still exceeds \(10^{74}+24\cdot10^{62}\). This extension uses the imported ceiling in addition to finite zero verification. [Pinned external theorem](https://github.com/GTimG/QuasiRiemannTracker/blob/42cf5415cfaa4205caaa25ab11160724606cdc33/submissions/2026-11-13-continuum-exact-contact/src/Candidate/Main.lean)

**The remaining arithmetic.** The fixed test asks whether this concrete total of signed interactions is nonpositive again at unbounded horizons. The complete field contains the principal arithmetic contribution. Centering a progression variance would change the test. The finite occurrence uses an external bounded zero-height theorem. A proof that the fixed sign recurs independently at unbounded horizons remains missing.
