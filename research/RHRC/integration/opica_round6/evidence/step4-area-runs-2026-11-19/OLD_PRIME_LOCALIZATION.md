# Localizing the centered prime area to older ordinary primes

**DERIVED on paper.** Put \(A(x)=\int_2^x(\vartheta(t)-t)dt\). The integer factorial projections yield real, signed weights \(K_{x,L}(p)\) on ordinary primes such that

\[
 A(x)+\tfrac23 x^{3/2}=
 \sum_{x^{3/4}/[L\log^2(2L)]<p<x/(L+1)} K_{x,L}(p)\log p+o(x^{3/2}).       \tag{1}
\]

Here one can take \(L=\lfloor\exp(\kappa\sqrt{\log x})\rfloor\) for a sufficiently small, fixed, positive \(\kappa\) specified below in terms of an unconditional prime-number-theorem bound. The formula holds for all large real \(x\), including every true stopped primorial. It gives no estimate of the signed sum on the right. The fixed-\(L\) version retains every prime below \(x/(L+1)\) and has error \(o_L(x^{3/2})\).

## The arithmetic weights

Use \(J_m(y)=\sum_{j\ge1}(1-m\mathbf1_{m\mid j})(y-j)_+\) and the periodic \(d_m\) from [the factorial projections](FACTORIAL_PRIME_PROJECTIONS.md). For integer \(L\ge2\), set \(a_m=-\mu(m)/m\) for \(2\le m\le L\). Set \(R=2L+1\) and use four further coefficients at \(R,4R,16R,64R\). Choose them by the exact real equations

\[
 \sum a_m=1,\quad \sum a_m\log m=1,\quad
 \sum a_m(1-\sqrt m)=1/\zeta(1/2),\quad \sum a_m(m-1)=2.                 \tag{2}
\]

All other coefficients vanish. Subtracting the constant multiple \(\log R\) in the log row and rescaling the last two rows reduces the four-node matrix, by invertible row operations, to columns \((1,i,2^i,4^i)\), \(i=0,1,2,3\). Its determinant is nonzero by the confluent Vandermonde formula, or by taking two forward differences. The same fixed inverse, the harmonic sum and the bounds \(\sum_{m\le L}m^{-1/2}\ll\sqrt L\), \(\sum_{m\le L}(\log m)/m\ll\log^2(2L)\) show that each extra coefficient is \(O(\log^2(2L))\). In particular, for \(r=1,2\),

\[
 \sum |a_m|m^r\ll L^r\log^2(2L).                                        \tag{3}
\]

Set \(J(y)=\sum a_mJ_m(y)\), and for \(0<p\le x\) define \(K_{x,L}(p)=x-p-pJ(x/p)\). For positive integers \(j\), the ramp coefficient in \(J\) is

\[
 w(j)=1-\sum_{m\mid j}m a_m.
\]

Thus \(w(1)=1\), and for \(2\le j\le L\) we have \(w(j)=\sum_{m\mid j}\mu(m)=0\). Throughout \(1\le y\le L+1\), including the last endpoint since its new ramp vanishes, \(J(y)=y-1\). The true residual weight therefore vanishes on the full interval \([x/(L+1),x]\).

The second equation in (2) makes the Lebesgue continuum of the projected ramp exactly \(x^2/2\). Hence \(\int_0^x K_{x,L}(u)du=0\) exactly, at every \(L\). The third equation gives the actual negative square bias \(-\tfrac23 x^{3/2}\) in this projected ramp, by equation (6) of the factorial note. Indeed its coefficient is \(-\tfrac23\zeta(1/2)\sum a_m(1-\sqrt m)\). Subtracting from the native ramp, with its original lower endpoint constant \(+2\), proves the stated fixed-\(L\) version. The fourth equation cancels the term proportional to \(x\) in the remaining weight, giving the exact identity and pointwise upper

\[
 K_{x,L}(p)=p\left[-1+\tfrac12\sum a_m d_m(x/p)\right],\qquad
 |K_{x,L}(p)|\ll pL^2\log^2(2L).                                        \tag{4}
\]

## Uniform estimates permitting a growing cutoff

Take fixed \(c>0\) with \(|\vartheta(v)-v|\ll v\exp(-c\sqrt{\log v})\) for \(v\ge2\). Such constants are unconditional. Choose \(0<\kappa<c/8\). In this paragraph use \(2\le m\le64(2L+1)\) and \(L=\lfloor\exp(\kappa\sqrt{\log x})\rfloor\), so eventually \(m\le x^{1/4}\). [Fiori, Kadiri and Swidinsky](https://arxiv.org/abs/2206.12557)

Write \(U_m(v)=m-1-v^2d_m(v^{-2})=2v^2J_m(v^{-2})\) on \(0<v\le1\), so \(0\le U_m\le m\). For \(0<v<x^{-1/4}\), the prime-square sum and its continuum integral in this rescaled variable contribute \(O(mx^{5/4})\) after multiplication by \(x\), by Chebyshev's upper bound. For \(x^{-1/4}\le v\le1\), the total variation of \(U_m\) is \(O(m^2+m\log x)\). Indeed \(|d_m|\le m^2/4\), \(|d'_m|\le m\) almost everywhere from the integer values \(r(m-r)\), and the absolute derivative is bounded by \(m^2v/2+2m/v\). The number of pieces on this closed interval is finite. Stieltjes integration by parts, including endpoints, now bounds the error of replacing \(d\vartheta(\sqrt x v)\) by \(\sqrt x\,dv\) in \(x\int U_m\,d\vartheta\) by

\[
 O\left(mx^{5/4}+x^{3/2}(m^2+m\log x)\exp[-(c/2)\sqrt{\log x}]\right).
\]

The factor \(c/2\) follows from \(\sqrt x v\ge x^{1/4}\). Powers \(p^a\), \(a\ge3\), cost \(O(mx^{4/3}\log x)\) in the projected ramp for each \(m\) by the same nonnegative kernel bound. The integrated log-factorial error is \(O(mx\log x)\) uniformly, by (4) of the factorial note applied separately at \(x\) and \(x/m\). Combined with (3), every accumulated error divided by \(x^{3/2}\) tends to zero. In the only exponential comparison the factor \(L^2\) has exponent \(2\kappa<c/2\), leaving room for logarithms. This proves the old-prefix identity with this growing cutoff before discarding any small primes.

Finally \(\sum_{p\le U}p\log p\ll U^2\). Using (4), the entire range \(p\le x^{3/4}/[L\log^2(2L)]\) contributes \(O(x^{3/2}/\log^2(2L))\) in absolute value. This proves (1). All omitted ordinary primes and proper powers have been paid for. The window and coefficient choices are independent of any zero, peak, or stop.

## A power cutoff from the supplied external zero ceiling

The project's pinned tracker theorem gives \(\Re\rho<r=0.873346\) for all nontrivial zeta zeros. This paragraph uses that external input. For every fixed \(r<s<1\), the truncated explicit formula, zero counting and removal of powers give \(|\vartheta(t)-t|\ll_s t^s\) for \(t\ge2\), and enlarging the constant gives this estimate for all \(t>0\). The external ceiling is documented with its proof-validation record in [the project audit](../step4-height-window-2026-11-19/STEP4_HEIGHT_AND_GRAPH_RESULTS.md) and [the pinned theorem](https://github.com/GTimG/QuasiRiemannTracker/blob/42cf5415cfaa4205caaa25ab11160724606cdc33/submissions/2026-11-13-continuum-exact-contact/src/Candidate/Main.lean).

The square approximation admits the sharper error \(O_s(x^{1+s/2}m^{1-s/2})\). To see this, integrate by parts against the prime discrepancy on \([\delta,1]\) and send \(\delta\downarrow0\). At 1, \(U_m(1)=0\). At zero the endpoint product tends to zero since \(U_m\) is bounded for each \(m\) and \(\vartheta(\sqrt x\delta)-\sqrt x\delta\to0\). The remaining bound is \(x^{1+s/2}\int_0^1v^s|U'_m(v)|dv\). For \(v<m^{-1/2}\), use \(|U'_m|\ll m^2v+m/v\ll m/v\). For \(v\ge m^{-1/2}\), \(y=v^{-2}\le m\) so all positive terms in \(J_m(y)\) have \(j<m\). Consequently \(U_m(v)=2\sum_{j\le v^{-2}}(1-jv^2)\) and \(|U'_m(v)|=4v\sum_{j\le v^{-2}} j\ll v^{-3}\) almost everywhere. Integrating the two powers gives \(O_s(m^{1-s/2})\). The square integral and its continuum are finite at both endpoints.

The argument for (3) also gives \(\sum|a_m|m^{1-s/2}\ll_s L^{1-s/2}\log^2(2L)\). Take \(L=\lfloor x^\lambda\rfloor\). After summation the square error is \(o(x^{3/2})\) if \(\lambda<(1-s)/(2-s)\). The other two errors are \(O(x^{4/3}L\log^3(2x))\) and \(O(xL\log^3(2x))\), both admissible here. Hence (1) holds for **every** fixed

\[
 0<\lambda<\frac{1-r}{2-r}=0.1124160567\ldots
\]

by choosing \(s>r\) sufficiently close to \(r\) after \(\lambda\) is fixed. At \(\lambda=0.11\) one may use \(s=0.874\): the square power is \(1+0.874/2+0.11(1-0.874/2)=1.49893<1.5\). Equation (1) then uses only primes above a lower cutoff asymptotic to \(x^{0.64}/(0.11\log x)^2\), and below an upper cutoff asymptotic to \(x^{0.89}\). The displayed identity (1) retains the exact floors and endpoints.

## The first unresolved dyadic band

If \(L<j\le2L\), every proper divisor is at most \(L\) and \(j<R\), so \(w(j)=\sum_{m\mid j,\ m<j}\mu(m)=-\mu(j)\). It follows for \(L<y\le2L\) that

\[
 y-1-J(y)=\sum_{L<j\le y}\mu(j)(y-j).
\]

Consequently the first old-prime band \(x/(2L)\le p<x/L\) contributes **exactly**

\[
 \sum_{x/(2L)\le p<x/L}\log p\sum_{L<j\le x/p}\mu(j)(x-pj).               \tag{5}
\]

The band overlaps the range of zero weight when \(L<y\le L+1\). Any term with \(j=y\) is zero. This is an actual prime–Möbius bilinear sum, including all signs and multiplicities. By the unconditional estimate \(M(t)=\sum_{j\le t}\mu(j)\ll t\exp(-c_1\sqrt{\log t})\), the inner unscaled triangle is \(\int_L^y(M(v)-M(L))dv=O(L^2\exp(-c_2\sqrt{\log L}))\). Summing the resulting \(p\log p\) weights gives \(O(x^2\exp(-c_2\sqrt{\log L}))\) for (5). This exhibits a signed saving on that band, still larger than the square-root-scale goal for the stated \(L\). The rest of the interval in (1) has no independently established Step 4 upper. [Lee and Leong](https://arxiv.org/abs/2208.06141)

The external ceiling also gives \(M(t)\ll_s t^s\) for every \(r<s<1\), hence the upper \(O_s(x^2L^{s-1})\) for (5). For completeness, choose \(r<\sigma_0<\sigma_1<s\). At large height \(T\), take concentric disks about \(2+iT\). A disk slightly larger than radius \(2-\sigma_0\) is zero-free and pole-free. Borel–Carathéodory on this disk bounds \(|\log\zeta|\ll\log |T|\) on radius \(2-\sigma_0\), using the polynomial vertical growth of zeta and the Euler-product branch at the center. On radius \(1/2\), the Euler product bounds \(|\log\zeta|\ll1\). Hadamard's three-circles theorem at the intermediate radius \(2-\sigma_1\) yields \(|\log\zeta|\ll(\log|T|)^a\) for a fixed \(a<1\). Thus \(1/\zeta(\sigma+it)\ll_\epsilon (1+|t|)^\epsilon\) for \(\sigma_1\le\sigma\le2\), with the removable value at 1. Apply truncated Perron to \(1/\zeta\) at half-integer \(v\), height \(v^2\), initial line \(1+1/\log v\). The truncation error is \(O(v\log^2(2v)/v^2)\) since \(|\mu|\le1\) and the distance to the nearest integer is \(1/2\). Shift to \(\sigma_1\), crossing no poles. The new vertical line costs \(O_\epsilon(v^{\sigma_1+2\epsilon}\log v)\) and the horizontals \(O_\epsilon(v^{-1+2\epsilon})\). A sufficiently small \(\epsilon>0\) proves the claimed bound at half-integers, hence at all real cutoffs by constancy. Even the resulting power saving in (5) does not reach \(x^{3/2}\).

The full unweighted prime area can therefore be reconstructed to square-scale precision from a moving interval of much earlier primes, carrying explicit arithmetic weights. The null-direction calculation in the factorial note explains why simply taking more scalar factorial projections cannot bound that remaining signed sum. These deductions are paper mathematics. Step 4 and RH remain OPEN.
