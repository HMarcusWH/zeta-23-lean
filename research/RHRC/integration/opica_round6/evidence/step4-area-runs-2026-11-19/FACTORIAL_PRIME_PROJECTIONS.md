# What factorial identities measure at a stopped primorial

**DERIVED on paper.** Let \(z=\vartheta(p)\) lie in the gap \((p,p^+)\) after an ordinary prime \(p\). Write \(d(y)=\operatorname{dist}(y,2\mathbb Z)\). Along every sequence of such stops tending to infinity,

\[
 \sum_{q\le z,\ q\ {\rm prime}} q\log q\,d(z/q)
 =(1-\log2)z^2+\tfrac43(1-\sqrt2)\zeta(1/2)z^{3/2}+o(z^{3/2}).       \tag{1}
\]

The secondary coefficient is strictly positive. This gives the size and sign of the discrepancy for an oscillating weight applied to the **entire old prime prefix**. The corresponding factorial-weighted ramp agrees exactly with the ordinary ramp on the upper half \([z/2,z]\). All integer factorial dilations admit the same calculation. A signed density below exhibits a common null direction of all these measurements, including the endpoint mass condition.

## Exact finite accounting

Fix an integer \(m\ge2\). Define \(w_m(j)=1-m\mathbf1_{m\mid j}\) for positive integers \(j\), \(B(y)=\{y\}(1-\{y\})\), and

\[
 d_m(y)=m^2 B(y/m)-B(y),\qquad
 J_m(y)=\sum_{j\ge1}w_m(j)(y-j)_+.
\]

The finite identity \(\sum_{j\ge1}(y-j)_+=(y^2-y+B(y))/2\) for \(y\ge0\) yields

\[
 2J_m(y)=(m-1)y-d_m(y).                                                \tag{2}
\]

The function \(d_m\) is periodic of period \(m\) and linear between consecutive integers. At integer \(j\) its value is \(r(m-r)\), where \(r=j\bmod m\). Thus \(0\le d_m\le m^2/4\). In particular \(d_2=d\), and \(w_2\) counts each odd index once with sign plus and each even index once with sign minus. For \(y=2l+s\), \(0\le s<2\), the odd-even sums give \(J_2=l\) for \(0\le s\le1\) and \(J_2=l+s-1\) for \(1\le s<2\). Values at integers agree because the endpoint ramp vanishes. More generally \(J_m(0)=0\), and the slope on \((j,j+1)\) is \(j\bmod m\). Hence \(J_m\ge0\).

Write \(G(x)=\sum_{n\le x}(x-n)\log n\) for real \(x\ge0\). Use \(\sum_{d\mid n}\Lambda(d)=\log n\) with **every prime power**. Exact finite regrouping gives

\[
 G(x)-m^2G(x/m)=\sum_{n\le x}\Lambda(n)nJ_m(x/n).                     \tag{3}
\]

Indeed the left side weights an ordered factorization \(n=jr\) by \(w_m(j)(x-jr)_+\Lambda(r)\). Each \(r=q^a\) occurs once with weight \(\log q\) for every positive exponent \(a\) and every eligible \(j\). Integrating \(\log\lfloor t\rfloor ! = t\log t-t+O(\log(2+t))\) gives

\[
 G(x)=\tfrac12x^2\log x-\tfrac34 x^2+O(x\log(2+x)),\qquad
 G(x)-m^2G(x/m)=\tfrac12x^2\log m+O_m(x\log(2+x)).                   \tag{4}
\]

## The signed bias of the actual ordinary-prime measure

Define \(Q_m(x)=\sum_{q\le x}q\log q\,J_m(x/q)\) over ordinary primes. In (3) the proper-power contribution is nonnegative. Its leading term comes from squares. Put

\[
 c_m=\int_0^1[(m-1)-v^2 d_m(v^{-2})]\,dv .                            \tag{5}
\]

The integrand extends continuously to \(v=0\) and equals \(2v^2J_m(v^{-2})\) for \(v>0\), so \(c_m>0\). Writing \(v=q/\sqrt x\), ordinary PNT and Riemann approximation of this continuous profile give

\[
 2\sum_{q^2\le x}q^2\log q\,J_m(x/q^2)=c_m x^{3/2}+o_m(x^{3/2}).
\]

Here the finite measures \(x^{-1/2}\sum_{q\le\sqrt x}\log q\,\delta_{q/\sqrt x}\) converge weakly to Lebesgue measure on \([0,1]\), since their masses on each fixed interval converge by PNT. All exponents \(a\ge3\) together cost \(O_m(x^{4/3}\log x)\) by (2), the Chebyshev bound \(\vartheta(u)\ll u\), and \(a\le\log_2 x\). From (3) and (4), for **all real** \(x\to\infty\),

\[
 Q_m(x)=\tfrac12 x^2\log m-\tfrac12 c_m x^{3/2}+o_m(x^{3/2}).         \tag{6}
\]

Its Lebesgue continuum ramp is exactly \(\int_0^x uJ_m(x/u)\,du=x^2\log m/2\), as also follows from (8) below at \(s=1\). For \(m=2\) and \(x/2\le u\le x\), \(uJ_2(x/u)=x-u\), the full original ramp. Equation (6) gives an unconditional signed downward discrepancy of order \(x^{3/2}\) on the resulting whole-prefix test. The untested part of the original ramp is supported on \(0<u<x/2\).

At a true stop, \(\sum_{q\le z}\log q=z\). Inserting this in (2) and (6) gives the equivalent first-moment measurement

\[
 \sum_{q\le z}q\log q\,d_m(z/q)=(m-1-\log m)z^2+c_m z^{3/2}+o_m(z^{3/2}). \tag{7}
\]

For general \(x\), replace \((m-1)z^2\) in its leading terms by \((m-1)x\vartheta(x)\). Thus the only stop-specific inference is made with the actual arithmetic endpoint. All asymptotics here hold for each fixed \(m\).

## A simultaneous null direction and the missing first moment

For \(\Re s>1\), integrating each finite ramp and summing absolutely gives

\[
 \int_0^1 u^s J_m(1/u)\,du
 =\frac{(1-m^{1-s})\zeta(s)}{s(s+1)} .                                \tag{8}
\]

Indeed the \(j\)-th ramp integral is \(j^{-s}/[s(s+1)]\). The integral defines a holomorphic function for \(\Re s>0\) since \(J_m(y)\ll_m y\). The pole at \(s=1\) on the right is removable, so (8) holds throughout that half-plane. From (2),

\[
 \int_0^1u^sd_m(1/u)\,du=\frac{m-1}{s}-\frac{2(1-m^{1-s})\zeta(s)}{s(s+1)}. \tag{9}
\]

Change variable \(u=v^2\) in (5) and set \(s=1/2\) in (9). This gives \(c_m=\tfrac43(1-\sqrt m)\zeta(1/2)\), proving the constant in (1).

For any actual nonreal zeta zero \(\rho=\beta+i\gamma\) with \(0<\beta<1\), the real signed density \(g(u)=\operatorname{Re}(i\rho u^{\rho-1})\) is integrable on \((0,1)\). Direct integration and (9) give

\[
 \int_0^1g=0,\qquad
 \int_0^1 u d_m(1/u)g(u)\,du=0\quad(m=2,3,\ldots),\qquad
 \int_0^1 u g(u)\,du=-\frac{\gamma}{|1+\rho|^2}\ne0 .                \tag{10}
\]

For example any known critical-line zero already proves this unconditional obstruction to uniform linear approximation of the first-moment weight \(u\) by the constant endpoint weight and the complete family \(u d_m(1/u)\). Integration against \(g\) is continuous in the uniform norm. The density is a diagnostic for the measurement family. Equations (6) and (7) themselves concern the actual prime input.

The ordinary target at the stop is \(A(z)=z^2/2-\sum_{q\le z}q\log q+2\), which uses the **unweighted** first moment. At \(m=2\), the missing prime contribution is exactly \(\sum q\log q[1-d(z/q)]\) in (7). The projection does not bound its signed discrepancy against continuum. Step 4 and RH remain OPEN. The divisor identity, Stirling's formula and PNT are classical. The packaging here is a paper deduction for the specific stopped graph, with no claim of literature novelty.

[Stopped prime graph](STOPPED_PRIME_GRAPH.md) · [Squarefree cost](SQUAREFREE_COST.md) · [NIST, prime number theorem](https://dlmf.nist.gov/25.16) · [NIST, Stirling expansion](https://dlmf.nist.gov/5.11)
