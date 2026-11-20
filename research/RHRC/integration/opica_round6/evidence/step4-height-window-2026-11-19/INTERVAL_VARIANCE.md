# Short intervals and the complete source response

**19 November 2026 · DERIVED paper calculation · Step 4 OPEN.** A signed average of ordinary additive prime-counting discrepancies recovers the actual OPICA field with an exponentially small smoothing error. At interval length \(x/(D_h\log^2 x)\), square-root variance up to \(x^{o(1)}\) would suffice. The known unconditional short-interval theorems checked below give a weaker error scale.

## The source and its transfer

Write \(H_h(z)=\int e^{-zv}h(v)\,dv\), \(h=(D^2-\tfrac14)^2(q*q)\), \(S=1/2048\), where \(q\) is the fixed universal-sinc source. The actual field is \(Z(t)=\sum_{n\ge2}\Lambda(n)n^{-1/2}h(t-\log n)\), including every prime power. Write \(A(T)=\int_0^T e^{-(T-t)/2}|Z(t)|\,dt\). The source's two half-pole moments include \(H_h(-1/2)=0\). The independent integer-drive, Möbius and completion equations continue to hold for this same field. The pinned Gevrey theorem for \(q\) gives, for \(f(y)=y^{-1/2}h(-\log y)\) extended by zero, \(\|f^{(j)}\|_\infty\le C_h D_0^j(j!)^2\). This follows by differentiating the convolution, using the finite chain rule for the analytic logarithm on the support, and using the compact profile's flat endpoints. [Pinned physical bounds](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/CCM/UniversalSincPhysicalBounds.lean) · [Derivative and composition details](../step4-signed-response-round2-2026-11-10/RECENT_INVERSE_ATTEMPT.md)

For real \(x\) large let \(g_x(w)=f(w/x)\), \(d\nu=d\psi-dw\) on the positive axis, and \(E_H(r)=\psi(r+H)-\psi(r)-H\). Direct substitution and \(\int f=H_h(-1/2)=0\) give \(Z(\log x)=x^{-1/2}\int g_x\,d\nu\). Fix \(1\le H=o(x)\), and define

\[
B_Hg(w)=\frac1H\int_0^H g(w-v)\,dv,\qquad
k=\lfloor c_0\sqrt{x/H}\rfloor,\qquad W=\sum_{j=0}^{k-1}(I-B_H)^j g_x .
\]

The finite identity \(g_x=B_HW+(I-B_H)^k g_x\) holds pointwise. Iterating the fundamental theorem of calculus gives \(\|(I-B_H)^j g_x\|_\infty\le H^j\|g_x^{(j)}\|_\infty\le C_h(D_0Hj^2/x)^j\) for \(j\ge1\). Choose \(c_0\) once so \(D_0c_0^2\le1/4\). Hence \(\|W\|_\infty\ll_h1\), and the remainder is \(O_h(e^{-c_1\sqrt{x/H}})\). All supports are in \([e^{-S}x,e^Sx+kH]\subset[x/2,2x]\) eventually. Chebyshev's estimate \(\psi(2x)\ll x\) bounds the total variation on these supports by \(O(x)\). Finite Fubini now gives, with all constants independent of the horizon,

\[
 Z(\log x)=\frac1{H\sqrt{x}}\int_{x/2}^{2x} W(r)E_H(r)\,dr
              +O_h\!\left(\sqrt x\,e^{-c_1\sqrt{x/H}}\right). \tag{1}
\]

Endpoint choices in the inner Stieltjes increment agree for almost every \(r\). Thus if \(J(x,H)=\int_{x/2}^{2x}|E_H(r)|^2dr\),

\[
 |Z(\log x)|\ll_h
 \min\!\left(\frac{\int_{x/2}^{2x}|E_H(r)|\,dr}{H\sqrt{x}},
             \frac{\sqrt{J(x,H)}}{H}\right)
 +\sqrt x\,e^{-c_1\sqrt{x/H}}. \tag{2}
\]

Choose \(H=x/[D_h(\log x)^2]\) with fixed \(c_1\sqrt{D_h}\ge 3/2\). The approximation error in (1) is \(O_h(x^{-1})\). For this choice \(J(x,H)\le C_\epsilon xH x^\epsilon\) at all sufficiently large \(x\), for each \(\epsilon>0\), gives \(|Z(\log x)|\ll_{h,\epsilon}x^{\epsilon/2}\log x\) and hence \(A(T)\ll_{h,\eta}e^{\eta T}\) for every \(\eta>0\). Even a first absolute moment \(\int|E_H|\ll_\epsilon H\sqrt{x}\,x^\epsilon\) suffices. Equation (1) asks still less if one keeps the signs. Under RH the classical \(\psi(u)-u=O(\sqrt{u}\log^2u)\) gives \(J\ll xH(\log x)^6\) at this length. Combined with the visible-zero test below, the stated all-\(\epsilon\) near-macroscopic variance condition is equivalent to RH at paper level.

## An exact causal formula at one fixed ratio

There is also a reduction with no approximation at all. It uses the full unweighted discrepancy on intervals \((r,2r]\). Fix \(\ell=\tfrac12\log 2>S\), put \(d\nu_0(u)=e^{-u/2}d[\psi(e^u)-e^u]\) on the entire real line, and set

\[
 E_\ell(v)=e^{-v/2}\big[\psi(e^{v+\ell})-\psi(e^{v-\ell})-e^{v+\ell}+e^{v-\ell}\big],
 \qquad K_\ell(v)=e^{-v/2}{\bf1}_{[-\ell,\ell]}(v).
\]

Then \(K_\ell*\nu_0=E_\ell\) almost everywhere and \(h*\nu_0=Z\) exactly. The latter equality uses the half-pole cancellation again. To represent the actual \(h\) as a filtered copy of \(K_\ell\), put \(g=h'+h/2\) and define

\[
 k(w)=e^{-\ell/2}\sum_{j\ge0}e^{-j\ell}g\!\left(w-(2j+1)\ell\right).
\]

Each term has compact support. The kernel begins at \(w=\ell-S>0\), and \(|k(w)|\ll_{h,\ell}e^{-w/2}\) for \(w\ge0\). Distributional differentiation yields \((D+\tfrac12)K_\ell=e^{\ell/2}\delta_{-\ell}-e^{-\ell/2}\delta_\ell\). The series telescopes to \((D+\tfrac12)(k*K_\ell)=g\). Equality with \(h\) follows from their common zero left tail. Absolute Fubini on every finite horizon is justified by the exponential tail of \(k\) and \(|\nu_0|(du)=e^{u/2}du\) sufficiently far to the left. Consequently, at every real \(t\),

\[
                       Z(t)=(k*E_\ell)(t). \tag{2a}
\]

In particular, \(J_2(X)=\int_X^{2X}|\psi(2r)-\psi(r)-r|^2\,dr\ll_\epsilon X^{2+\epsilon}\) for every \(\epsilon>0\) and all sufficiently large real \(X\) would imply Step 4. Indeed \(r=e^{v-\ell}\) transforms each log block of length \(\log 2\) into a dyadic interval, with \(\int_{\rm block}|E_\ell(v)|^2dv=e^{-\ell}\int_X^{2X}|\psi(2r)-\psi(r)-r|^2r^{-2}\,dr\). Cauchy–Schwarz on each log block in (2a), followed by summation with \(e^{-(t-v)/2}\), gives \(|Z(t)|\ll_{h,\epsilon}e^{\epsilon t/2}\). The part \(v\le0\) is bounded. A first-moment assumption \(\int_X^{2X}|\psi(2r)-\psi(r)-r|\,dr\ll_\epsilon X^{3/2+\epsilon}\) likewise suffices, and retaining the signed \(k\)-projection asks less. Under RH the classical pointwise PNT error gives both assumptions with polylogarithmic losses. Thus the converse again holds. The fixed-ratio variance bound is an independent arithmetic obligation; (2a) establishes a causal transfer for this precise source at one fixed ratio.

## What is needed at common real horizons

Let \(d=\sup_\rho(\Re\rho-1/2)\) for nontrivial zeros. Two inherited paper inputs are \(|Z(t)|\ll_h e^{dt}\) and \(A(T)\ge c_\rho e^{\delta T}\) for each rightward zero of displacement \(\delta>0\) at all sufficiently large real \(T\). For the upper, the pole term of the smoothed explicit formula vanishes, its zero sum converges absolutely by source smoothness and zero counting, and a shifted remainder is bounded. For the lower, the centered-moment argument uses the top nonvanishing derivative at the zero with its actual multiplicity; the fixed seed sees every off-line zero. Centered-moment proof · [Visibility at the pinned commit](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/ExceptionalZero/UniversalSincPhysicalDetector.lean#L107)

Fix \(0<\alpha<1\), \(\kappa>0\). Suppose for each \(\eta>0\) there are arbitrarily late \(T\) for which \(|Z(s)|\le C_\eta e^{\eta T}\) on \([(1-\alpha)T,T]\setminus B_T\), and \(\int_{B_T}e^{-(d+1/2)(T-s)}ds\le C_\eta e^{-\kappa T}\). One sufficient way to obtain the first bound uses (2) at every \(x=e^s\) outside the exceptional set on that common block. Splitting \(A(T)\) into the early part, the good part and the exceptional part gives

\[
A(T)\ll_{h,\eta} e^{[d-\alpha(d+1/2)]T}+e^{\eta T}+e^{(d-\kappa)T}. \tag{3}
\]

If \(d>0\), choose \(\eta<d\), then an actual \(\delta>\max\{\eta,d-\alpha(d+1/2),d-\kappa\}\). Apply the lower at the same sufficiently late \(T\). This works even when no zero attains the supremum. The data need to control the earlier part of the weighted history: a single good value \(x=e^T\) controls only that endpoint. If \(d>0\) and \(\eta<d\), the converse calculation forces exceptional weighted mass \(\gg_{\rho,h}e^{-(d-\delta)T}\) at every sufficiently late \(T\) for the threshold \(|Z(s)|>e^{\eta T}\), whenever \(\delta>\max\{\eta,d-\alpha(d+1/2)\}\). Arbitrarily small positive exponential losses can be used by taking \(\delta\) sufficiently close to \(d\).

## What the short-interval literature supplies

Guth and Maynard, Corollaries 1.3–1.4 and §13.2, treat \(X^{2/15+\epsilon}\le H\le X^{0.99}\) for almost all starting points, with an all-points assertion above \(X^{17/30+\epsilon}\). Their proof treats the full von Mangoldt sum. Its mean-square bound is of the shape \(J(X,H)\ll_\epsilon XH^2 e^{-c(\log X)^{1/4}}\) on fixed power scales in the almost-all range, after covering the support by finitely many dyadic intervals. Substitution in (2) gives \(O_h(\sqrt X e^{-c'(\log X)^{1/4}})\) there. Eventually \(X/[D_h\log^2 X]>X^{0.99}\). Extending the stated size range would still leave the exponent mismatch. Gafni and Tao prove a polynomial saving in the exceptional-set measure for some fixed powers, for example \(\mu(17/30)\le7/12\). Their exceptional set is defined by \(|E_{r^\theta}(r)|\ge b r^\theta\) for fixed \(b>0\). Small relative error of that type can coexist with a growing source response. The good set in (3) instead needs subexponential **normalized source amplitude**. [Guth–Maynard, original paper](https://ora.ox.ac.uk/objects/uuid%3Aad11b8bf-ad2b-4ebf-a627-647f023c378f/files/s73666708v) · [Gafni–Tao, definition and estimates](https://arxiv.org/html/2505.24017v1)

## A sharp limitation of fixed-power variance

If \(H=x^\theta\) at a fixed \(0<\theta<1\), even \(J\ll xH x^{o(1)}\) gives only \(x^{(1-\theta)/2+o(1)}\) by (2). This loss is necessary for an inference based only on that variance and positivity. On \(w\ge1\) take the positive comparison measure \(d\mu(w)=(1+\tfrac12w^{\beta-1})dw\) with \(\beta=1/2+\delta<1\). Its interval discrepancy on \(r\asymp x\) is \(O(Hx^{\beta-1})\), hence its variance is \(O(H^2x^{2\delta})\le O(xH)\) when \(\theta+2\delta\le1\). Its response to exactly the same source is \(\tfrac12H_h(\delta)e^{\delta t}\) for every sufficiently large real \(t\). Here \(H_h(\delta)=(\delta^2-\tfrac14)^2\widehat q(\delta)^2>0\) for \(0<\delta<1/2\), since \(q\ge0\) has mass one. Choosing \(\delta=(1-\theta)/2\) attains the exponent in (2). This comparison measure has no prime divisor identity. Its role is to isolate the limitation of the proposed variance inference. The actual transfer (1) uses the complete prime-power field throughout.

**Open arithmetic obligation.** Bound the signed projection in (1) on the common windows needed by (3), or supply the sufficient near-macroscopic absolute-moment bounds above. No estimate established here eliminates a rightward zero. The new reductions and countertest have no Lean or CI qualification.
