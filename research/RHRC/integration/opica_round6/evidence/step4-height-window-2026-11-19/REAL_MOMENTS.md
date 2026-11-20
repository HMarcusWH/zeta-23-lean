# Real gamma moments of the complete prime-power source

**DERIVED on paper, 19 November 2026. Step 4 and RH remain OPEN.** There is a two-sided geometric bound at each fixed real center \(1/2<\lambda<(3\cdot10^{12})^2+1/4\), valid for every moment order \(n\ge1\). The estimate concerns the actual weighted prime powers. A one-sided estimate at an unbounded sequence of fixed centers would suffice for RH. A common bound across moving centers fails even for the genuine primes.

## An exact arithmetic test

Let \(w=1/2+\lambda\), and let \(\Lambda\) be the von Mangoldt function. Define
\[
 G_n(\lambda)=\frac{\lambda^{n+1}}{n!}
 \sum_{m\ge2}\frac{\Lambda(m)(\log m)^n}{m^w}
 -\left(\frac{\lambda}{\lambda-1/2}\right)^{n+1}.
\]
This is the complete centered measure \(\nu\) integrated against the positive gamma density \(\lambda^{n+1}t^n e^{-\lambda t}/n!\). The density has mean \((n+1)/\lambda\) and standard deviation \(\sqrt{n+1}/\lambda\). The second term is the exact integral against the continuum \(e^{t/2}dt\).

For \(\Re s>1/2\), the Euler product gives \(D(s)=-\zeta'/\zeta(1/2+s)-1/(s-1/2)\). Differentiation in the absolutely convergent region gives \(G_n=\lambda^{n+1}(-1)^nD^{(n)}(\lambda)/n!\). For \(n\ge1\), completing the zeta function gives
\[
 G_n(\lambda)=
 -\sum_\rho\left(\frac{\lambda}{w-\rho}\right)^{n+1}
 -\sum_{k\ge1}\left(\frac{\lambda}{w+2k}\right)^{n+1}.
 \tag{1}
\]
Both sums converge absolutely, and the first counts each nontrivial zero with its multiplicity. Indeed \(D=1/w-\tfrac12\log\pi+\tfrac12\psi(w/2)-\xi'/\xi(w)\) at \(s=\lambda\). The differentiated Hadamard product gives the first sum. The polygamma series supplies the second, since its \(k=0\) term cancels the derivative of \(1/w\). Equation (1) is an inverse-power sum of Turán type. The classical Li coefficients use a different power sum with a different normalization. [Completed zeta function](https://dlmf.nist.gov/25.4) · [Trigamma series](https://dlmf.nist.gov/5.15#E1) · [Bombieri and Lagarias](https://websites.umich.edu/~lagarias/doc/bombieri.pdf)

## Explicit bound from the verified height

Write \(H=3\cdot10^{12}\). Put
\[
 q_\lambda=\max\left\{\frac{\lambda}{w+2},
  \frac{\lambda}{\sqrt{\lambda^2+1/4}},
  \frac{\lambda}{\sqrt{(\lambda-1/2)^2+H^2}}\right\},\qquad
 C_\lambda=\lambda^2\left\{
 \frac{w^{-1}+(w-1)^{-1}+\tfrac12\log(1+w)}{w-1}+\frac1{2w}\right\}.
\]
For every \(1/2<\lambda<H^2+1/4\), \(q_\lambda<1\), and
\[
 \boxed{|G_n(\lambda)|\le C_\lambda q_\lambda^{n-1}\qquad(n\ge1).}
\]
The published interval verification puts every zero below \(H\) on the critical line. On that line there is no zero at ordinate \(|t|\le1/2\). For a short elementary check, let \(\eta(s)=(1-2^{1-s})\zeta(s)\). Pairing consecutive terms gives \(\eta(s)/s=\int_1^\infty {\bf1}_{\cup_{j\ge1}[2j-1,2j)}(x)x^{-s-1}dx\). At \(s=1/2+it\), \(|t|\le1/2\), the real part is at least \(2(1-1/\sqrt2)\cos((\log2)/2)-2e^{-\pi/2}>0\), by retaining \([1,2]\) and charging the entire tail \(x\ge e^\pi\). For zeros above \(H\), the strip \(0<\Re\rho<1\) supplies the third denominator in \(q_\lambda\). [Platt and Trudgian, verified height](https://arxiv.org/abs/2004.09765) · [Zero strip and symmetry](https://dlmf.nist.gov/25.10)

To obtain the prefactor, pair the symmetric Hadamard factors. On the real line \(w>1\), \(\xi'/\xi(w)=\sum_\rho\Re(1/(w-\rho))\). The constant term in the real logarithmic derivative vanishes by \(\xi'(1/2)=0\) and symmetry about \(1/2\). Hence \(\sum_\rho|w-\rho|^{-2}\le(\xi'/\xi)(w)/(w-1)\). In its completed logarithmic derivative use \(\zeta'/\zeta(w)\le0\) and \(\psi(w/2)\le\log(w/2)\), the latter by Jensen applied to the logarithm of a gamma variable. Also \(\sum_{k\ge1}(w+2k)^{-2}\le 1/(2w)\) by integral comparison. These give \(C_\lambda\) after removing \(q_\lambda^{n-1}\) from the absolutely convergent sums. For example, \(|G_n(1)|\le7(2/\sqrt5)^{n-1}\). The height is external input to this implication. The present calculation verifies no additional zeros.

## What an upper at unbounded fixed centers would buy

The Taylor generating function is \(\sum_{n\ge0}G_n(\lambda)z^n=\lambda D(\lambda(1-z))\) near zero. A rightward zero \(\rho=1/2+p\), \(\delta=\Re p>0\), produces an interior pole precisely when
\[
 |1-p/\lambda|<1\quad\Longleftrightarrow\quad\lambda>|p|^2/(2\delta).
\]
There are no real singularities on \(0\le z<1\), including at the canceled zeta pole. If an interior pole exists, the coefficients \(G_n\) attain both signs at geometrically growing magnitudes along subsequences. Indeed, if \(r<1\) is the Taylor radius and \(1<a<1/r\), an eventual upper \(G_n\le C a^n\) would make the coefficients of \(C/(1-az)-\lambda D(\lambda(1-z))\) eventually nonnegative. Its radius \(r\) would force a positive-real singularity at \(r\) by Pringsheim's theorem. The same reasoning applies to \(-G_n\). Under RH, (1) instead gives geometric decay for every fixed \(\lambda\) by the critical-line ordinate gap. Consequently an eventual upper as simple as \(G_n(\lambda)\le1\) at each member of any unbounded sequence of fixed centers would suffice. Each order threshold may depend on its center. Establishing it beyond the available finite verification remains open.

**Why the order of quantifiers matters.** For a prime \(\ell\to\infty\), take \(\lambda=\ell^3\) and \(n=\lfloor\lambda\log\ell\rfloor\). At \(t=\log\ell\), Stirling's formula gives gamma density \((1+o(1))\sqrt{\lambda/(2\pi\log\ell)}\). This single prime contributes \((1+o(1))\ell\sqrt{\log\ell/(2\pi)}\). Every other atom has nonnegative weight, and the entire subtracted continuum is \((1+o(1))\sqrt\ell\). Thus \(G_n(\ell^3)\gg\ell\sqrt{\log\ell}\) at a physical horizon \(n/\lambda\sim\log\ell\). Uniform subexponential growth in that physical horizon across all centers is false. A subgeometric-in-\(n\) bound evaluated only on a sequence with \(\lambda\to\infty\) can also miss each fixed zero, whose individual growth per order then tends to one.

## The complete K5 primitive has eventually negative gamma averages at each verified center

Keep the K5 primitive \(I(T)\) of the complete signed source, including its continuum subtraction and all prime powers. Define its own gamma mean by
\[
 J_n^I(\lambda)=\frac{\lambda^{n+1}}{n!}\int_0^\infty T^n e^{-\lambda T}I(T)\,dT .
\]
The integral converges for \(\lambda>1/2\) by the elementary exponential envelope on the original source and the polynomial carrier weights. For each fixed \(1/2<\lambda<H^2+1/4\),
\[
 \boxed{\displaystyle
 J_n^I(\lambda)=\frac{k_{17}(0)D(0)}{18\lambda^{18}}\,n^{18}
                  +O_\lambda(n^{17}),\qquad k_{17}(0)D(0)<0 .}
 \tag{2}
\]
In particular, the gamma mean of the signed primitive is negative at every sufficiently large order at that center. The threshold and remainder constant depend on \(\lambda\). Definition of the K5 primitive and its Euler transform

**Continuation on the disk.** Let \(\mathcal I(s)=\int_0^\infty e^{-sT}I(T)\,dT\) in its initial half-plane. The aperture report gives \(\mathcal I=\mathcal B/s\) and the three carrier functions \(k_m\), \(m=13,15,17\). Each extends to an entire function, since for the trigonometric polynomials \(g,h\) involved its elementary building block is \((1-u)\int_0^1g((1-u)y)h((1-u)y+u)\,dy\). For real \(s>1/2\), substitute \(v=s/u\) into the report's equation (1). This gives
\[
 \mathcal I(s)=\sum_m(-1)^{m+1}s^{-m-2}
       \int_s^\infty v^m k_m(s/v)D^{(m+1)}(v)\,dv . \tag{3}
\]
The verified distance estimates above give an \(\varepsilon_\lambda>0\) such that the disk \(|v-\lambda|<\lambda+\varepsilon_\lambda\) contains no pole of \(D\). The center \(v=0\) of the kernel ratio is regular for \(D\). Slit the enlarged disk along its nonpositive real axis to account for \(s/v\) at \(v=0\). On this simply connected slit domain the path from \(s\) to the real basepoint \(\lambda\) can be deformed freely. Append the real ray from \(\lambda\) to infinity. The integrand is holomorphic in \(v\) on the slit domain, and the real tail is \(O(v^{-2})\) uniformly for \(s\) in compact sets there. A fixed path to a nearby basepoint followed by a short variable endpoint segment also shows holomorphic dependence on \(s\). This gives one analytic branch on a neighborhood of the entire closed disk \(|s-\lambda|\le\lambda\) except at \(s=0\). Rays drawn from poles outside that disk in the original \(u\)-representation introduce no interior singularities in (3).

**Behavior near zero, uniformly in angle.** As \(s\to0\) inside the disk, \(\Re s\ge0\). Use the horizontal path \(v=s+x\), \(x\ge0\). For small \(|s|\) it agrees by contour deformation with the branch just constructed. Indeed, a strip of fixed small imaginary height around the positive real axis is free of \(D\)-poles by the verified zero height, the small-ordinate check, and cancellation at \(1/2\). The vertical connector at large real part has vanishing integral. On this path \(|s/v|\le1\) and \(k_m(s/v)=k_m(0)+O(|s/v|)\). The error inside the integral is \(O(|s|)\) because \(\int_0^\infty |v|^{m-1}|D^{(m+1)}(v)|dx\) is bounded uniformly. Its bounded part uses regularity of \(D\) near the positive axis and its tail uses \(D^{(m+1)}(v)=O(|v|^{-m-2})\). In the constant term one may move the lower endpoint to zero at cost \(O(|s|^{m+1})\). Integrating by parts gives
\[
 \int_0^\infty v^m D^{(m+1)}(v)dv=(-1)^{m+1}m!D(0).
\]
The endpoint at infinity vanishes at each stage since \(D^{(j)}(v)=O(v^{-j-1})\) there. Hence (3) gives \(\mathcal I(s)=17!k_{17}(0)D(0)s^{-19}+O(|s|^{-18})\) uniformly on the stated approach.

**Coefficient and sign.** The generating function with this normalization is \(\lambda\mathcal I(\lambda(1-z))\). The leading term has coefficient \(\lambda^{-18}17! k_{17}(0)D(0)\binom{n+18}{18}\). After subtraction the remainder is bounded on the unit disk by \(C_\lambda|1-z|^{-18}\), using compactness away from \(z=1\). In Cauchy's coefficient integral on \(r=1-1/n\), \(r^{-n}=O(1)\) and \(\int_{-\pi}^\pi|1-re^{i\theta}|^{-18}d\theta=O(n^{17})\). This proves (2). For the fixed carrier, \(k_{17}(0)=\int_0^1 f(y)^2dy/16>0\). The functional equation gives \(\xi'(1/2)=0\). The rational terms \(1/s+1/(s-1)\) cancel at \(s=1/2\), and the quarter-argument digamma value gives
\[
 D(0)=2-\frac{\zeta'}{\zeta}(1/2)
 =2-\frac{\log\pi+\gamma_E+\pi/2+3\log2}{2}<0 .
\]
This calculation supplies a signed result for the actual K5 primitive at the stated centers. It does not supply the required pointwise upper for \(I(T)\), an unbounded family of verified centers, or a bound for a native OPICA generated packet. All estimates have paper scope. [Completed functional equation](https://dlmf.nist.gov/25.4) · [Quarter-argument digamma value](https://dlmf.nist.gov/5.4#E19)
