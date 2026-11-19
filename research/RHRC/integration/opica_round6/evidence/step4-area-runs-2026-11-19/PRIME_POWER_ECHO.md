# What the square and cube contributions force in the ordinary-prime area

**DERIVED on paper.** Let \(\vartheta(x)=\sum_{p\le x}\log p\) and \(A(x)=\int_2^x(\vartheta(y)-y)\,dy\). For every fixed \(c<3/4\), every sufficiently large \(X\) admits an \(x\) with
\[
 X/(C\log X)^{3/2}\le x\le X(C\log X)^{3/2},\qquad
 A(x)<-\tfrac23x^{3/2}-c\,x^{4/3}.                                   \tag{1}
\]
This is an unconditional statement for the genuine weights. It reaches below the exact leading square bias. It gives no uniform sign between the witnesses. In particular, rounding the witness to a fourth power at the finer \(x^{4/3}\) depth requires more accuracy than the available rounding argument. The earlier negative-margin result on fourth powers is separate.

## The arithmetic incidence calculation

Write \(\psi(y)=\sum_{n\le y}\Lambda(n)\), including all prime powers. Ordinary-prime support is selected by the exact divisor relation
\[
 \vartheta(y)=\sum_{k\le\log_2 y}\mu(k)\psi(y^{1/k}).
\]
At the event \(p^a\), its coefficient in the sum is \(\log p\sum_{k\mid a}\mu(k)\). Thus every ordinary prime contributes its actual log weight and every higher-power event has net coefficient zero. Integration leaves exactly the factor \((x-p^a)_+\) on the same edges. No independence or random sign model enters the calculation.

Put \(t=\log x\) and \(F(t)=e^{-3t/2}A(e^t)\) for \(t\ge\log2\), zero earlier. For each fixed \(k\), the integrated error for \(\psi(y^{1/k})\) is
\[
 \int_2^x [\psi(y^{1/k})-y^{1/k}]\,dy
   =-\sum_\rho\frac{x^{1+\rho/k}}{\rho(1+\rho/k)}+O_k(x\log(2x)).
                                                                    \tag{2}
\]
To obtain (2) from a convergent formula, take \(G(z)=\int_2^z(\psi(u)-u)du\). Johnston's integrated explicit formula writes \(G(z)=-\sum_\rho z^{1+\rho}/[\rho(1+\rho)]+O(z)\). Substituting \(y=z^k\) and integrating \(k z^{k-1}\,dG(z)\) by parts on \([2,x^{1/k}]\) gives coefficient \(-k/[\rho(k+\rho)]\). The \(O(z)\) remainder produces \(O_k(x)\), including endpoints. Differences on the bounded initial interval are constants. For fixed \(k\) the zero coefficients are absolutely summable, including multiplicities, so the compact-interval integration is legitimate. The weaker remainder in (2) suffices. [Johnston, proof of Lemma 2.6](https://arxiv.org/pdf/2201.06184#page=4)

Let \(K\) be the positive even kernel with bilateral Laplace transform \(\xi(1/2+z)\) and doubly exponential decay. For each \(k\ge1\), put
\[
 K_k(u)=k^{-1}e^{-(k-1)u/(2k)}K(u/k).
\]
This is positive and its transform is \(\xi(k(z+1/2))\). It removes each zero mode from the corresponding term in (2), since the exponent after normalization is \(z=\rho/k-1/2\). Its transform is strictly positive at every real argument. A real mode, including each deterministic prime-power contribution, is retained with its full multiplier. [Kernel and normalization](XI_AREA_ECHO.md) · [Rodgers and Tao, equations (1)–(3)](https://arxiv.org/pdf/1801.05914#page=2)

## The surviving cube bias

Take \(H=K_1*K_2\), with transform \(h(z)=\xi(1/2+z)\xi(1+2z)\). In the Möbius sum, \(k=1\) has its deterministic contribution canceled by the original subtraction of \(y\). The \(k=2\) deterministic term contributes \(-2x^{3/2}/3\) before normalization. Equation (2) and the two factors of \(h\) remove all zero modes of these two terms, at all ordinates. The constants from integration at 2 are included in the decaying remainder. For \(k=3\), ordinary PNT gives \(\int_2^x\psi(y^{1/3})dy=(3/4)x^{4/3}+o(x^{4/3})\). Its Möbius sign is negative. The fourth coefficient is zero. Chebyshev's bound controls all \(k\ge5\) together by \(O(x^{6/5}\log(2x))\).

Consequently the actual observation satisfies
\[
 (H*F)(t)=-\tfrac23h(0)-\tfrac34h(-1/6)e^{-t/6}+o(e^{-t/6}).
                                                                    \tag{3}
\]
For the interchange, extend each zero mode to all real log times by its exponential formula. On negative log times the resulting sums grow at most exponentially by absolute summability, so their contribution to the prehistory has doubly exponential suppression. After subtracting the two deterministic modes, the remaining error is \(o(e^{-t/6})\) for \(t\to+\infty\) and grows at most exponentially elsewhere. Convolution against \(H\) preserves this little-oh estimate by dominated convergence after the exponential reweighting.

To truncate, for large \(|u|\), \(H(u)\ll \exp[-c_1 e^{2|u|/3}]\). Indeed in \(K_1(v)K_2(u-v)\) one has \(|v|\ge |u|/3\) or \(|u-v|\ge2|u|/3\). Use half the corresponding factor's decay for the bound and the remaining integrable factors for the convolution. On \(|u|>\frac32\log(Ct)\) this bound absorbs both the elementary growth \(O(e^{(t+|u|)/2})\) of the observed area and the factor \(e^{t/6}\), for fixed \(C\) sufficiently large. The tail of the centered expression \(F(t-u)+2/3+c e^{-(t-u)/6}\) is then \(o(e^{-t/6})\) after integration. By (3) its total integral is \((c-3/4)h(-1/6)e^{-t/6}+o(e^{-t/6})<0\). Positive weights force a strictly negative value in the retained window, proving (1).

## Every fixed finite level

More generally let \(q\ge2\) be any fixed squarefree integer. Subtract
\(\sum_{2\le k<q}\mu(k)k x^{1+1/k}/(k+1)\) from \(A(x)\). Convolve the normalized remainder with the positive product (convolution) of \(K_k\) over \(k<q\) with \(\mu(k)\ne0\), including \(k=1\), and denote its transform by \(h_q\). The result has first surviving term
\[
 \mu(q)\frac{q}{q+1}\,h_q(1/q-1/2)e^{(1/q-1/2)t}
 +o_q\big(e^{(1/q-1/2)t}\big).
\]
Use (2) for each earlier term, PNT for the \(q\)-term, and \(O_q(x^{1+1/(q+1)}\log(2x))\) for the absolute contribution of the later terms. With \(S_q=\sum_{k<q,\,\mu(k)\ne0} k\), the same tail argument uses radius \((S_q/2)\log(C_q t)\). The sign of the new term changes with \(\mu(q)\). None of these estimates is uniform in \(q\).

The conclusion uses the full underlying prime measure at each stage. These positive filters deliberately annihilate the very zero modes that could create large excursions between observations. Increasing the number of powers handled improves the asymptotic precision of the filtered bias. It also increases the width of the available observation and does not establish a bound on the length of positive runs of the original area.

There is also an approximation on both sides. After the same subtraction divide by \(x^{1+1/q}\), or equivalently multiply the normalized remainder by \(e^{-(1/q-1/2)t}\). Use the positive probability law proportional to \(e^{-(1/q-1/2)u}H_q(u)du\), with \(H_q\) the convolution kernel above. The mean of the rescaled residual tends to \(\mu(q)q/(q+1)\). The truncated mean has the same limit. Continuity and the intermediate value theorem put an actual value within \(o(1)\) of that number somewhere in every such late window, for each fixed \(q\).

## Exact crossings on a fixed multiplicative interval

The density calculation in [the accompanying proof](DENSITY_ISOLATOR.md) improves the *location* by a different argument. For any continuous \(D(x)=-2x^{3/2}/3+o(x^{3/2})\), every sufficiently large interval \([X,KX]\) contains a true equality \(A(x)=D(x)\), for some finite \(K>1\). In fact there are points on both sides with \((A-D)/x^{3/2}>1/1500\) and \(<-1/1500\). No explicit numerical \(K\) or starting \(X\) is obtained.

If a zero is off the critical line, the density isolator supplies both excursions of size \(x^{1+b}\) for a fixed \(b>1/2\), which dominate this template. In the remaining case every zero has real part \(1/2\). The integrated formula and the square bias now give
\[
  e^{-3t/2}(A(e^t)-D(e^t))
  = V(t)+o(1),\qquad
  V(t)=-\sum_\rho e^{i\gamma t}/[\rho(1+\rho)] .
\]
The real, absolutely convergent trigonometric series has mean zero. Its uniform norm is below \(0.047\) by \(\sum_\rho |\Im\rho|^{-2}<0.047\). Its mean square is at least \(2/[(15^2+1/4)(15^2+9/4)]\), using the first conjugate pair below height 15 (multiplicity can only raise this bound). If \(M=\sup V\) and \(m=-\inf V\), taking means in \((M-V)(V+m)\ge0\) gives \(Mm\ge\operatorname{mean}(V^2)\). Both \(M\) and \(m\) are thus greater than \(1/1500\), with strict slack. Uniform almost periodicity gives both strict margins with bounded gaps; the \(o(1)\) error is eventually smaller than the reserved slack. Continuity gives the equality. [Zero-sum estimate, Brent, Platt and Trudgian, Corollary 1](https://arxiv.org/pdf/2009.13791) · [First zeta ordinate, NIST DLMF](https://dlmf.nist.gov/25.10)

One eligible template, using the entire prime-power incidence rule, is
\[
 D_{\rm M}(x)=\int_2^x\sum_{2\le k\le\log_2 y}\mu(k)y^{1/k}\,dy .
\]
It is continuous. Its square term is \(-2x^{3/2}/3+O(1)\), and the sum of all later terms is \(O(x^{4/3}\log x)\). Thus the complete accumulated prime area crosses this particular, explicitly computable comparison function in every sufficiently late fixed multiplicative window. Both alternatives in the proof allow these crossings. The interval between successive crossings may still contain a positive run far longer than the requested power-saving bound.
