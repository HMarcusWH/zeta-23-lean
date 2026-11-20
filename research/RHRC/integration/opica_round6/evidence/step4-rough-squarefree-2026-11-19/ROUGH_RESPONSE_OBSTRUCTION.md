# The complete rough response and the critical cutoff

19 November 2026. **DERIVED at paper level. Step 4 and RH remain OPEN.** At the cutoff \(y=T^2\), the complete signed rough response detects the displacement of every rightward zero of the frozen source. Even under RH its weighted mass grows faster than every polynomial. The required cofinal, every-positive-exponent upper allows that growth. This note establishes its necessary scale and does not prove the independent upper.

## The fixed source and exact histories

Use the frozen universal-sinc probability seed \(q\), \(h=(D^2-1/4)^2(q*q)\), supported in \([-1/2048,1/2048]\), and \(\widehat f(p)=\int e^{-pt}f(t)\,dt\). Write \(H(p)=(p^2-1/4)^2\widehat q(p)^2\). The genuine fields are
\[
 Z(t)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}h(t-\log n),\qquad
 U(t)=\sum_{n\ge2}\frac{\log n}{\sqrt n}h(t-\log n).
\]
All prime powers, multiplicities and causal histories enter. Let \(N_{\le y}\) place mass \(n^{-1/2}\) at \(\log n\) for each integer composed of primes at most \(y\), including \(1\). Let \(M_{>y}\) use masses \(\mu(n)n^{-1/2}\) on integers with smallest prime factor greater than \(y\), again including \(1\). Freeze the same \(y\) over the entire prefix and its completion. Finite divisor convolution gives
\[
 R_y=M_{>y}*U=N_{\le y}*Z,\quad W_y=a*R_y=N_{\le y}*W,\quad W=a*Z=c*U,
 \qquad A_y(T)=\int_0^T e^{-(T-t)/2}|R_y(t)|\,dt.
\]
Here \(c(t)=1_{t\ge0}(2e^{-3t/2}-e^{-t/2})\) and \(0\le a(t)\le1_{t\ge0}e^{-t/2}\) is the actual floor kernel. The source transport from the original test to its self-convolution and \(W\in L^2\) are reviewed paper inputs. The pinned Lean source gives the original pointwise completion and establishes visibility for its precise physical test and its square at every off-line zeta zero. Thus visibility matters in the proof and is supplied for this seed. An arbitrary kernel with the same vanishing moments need not see every zero. [Native completion](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/CCM/NativeCompletionEquation.lean#L109) · [Floor kernel](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/CCM/NativeFloorCompletionSource.lean#L100) · [Physical visibility and its square](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/ExceptionalZero/UniversalSincPhysicalDetector.lean#L107) · Centered-moment proof

## Why the rough response detects a zero

Put \(d=\sup_{\rho}(\Re\rho-1/2)\), over the nontrivial zeta zeros. Symmetry gives \(d\ge0\). The smoothed explicit formula gives \(|Z(t)|+|Z'(t)|\ll_h e^{dt}\) for \(t\ge0\). Indeed the Mellin test is \(e^{(s-1/2)t}H(s-1/2)\), the pole at \(s=1\) has zero coefficient, and the nontrivial-zero sum converges absolutely by uniform rapid vertical decay and zero counting with multiplicity. Moving to \(\Re s=-1\) leaves \(O_h(e^{-3t/2})\). The same argument applies to \(h'\). On \(\Re p>d\), the genuine Laplace transform is \(-H(p)\zeta'(1/2+p)/\zeta(1/2+p)\), with its removable value at \(p=1/2\). [Classical explicit formula](https://dlmf.nist.gov/25.16#i)

Fix a rightward zero \(\rho=1/2+p,\ \delta=\Re p>0\) of multiplicity \(m\); put \(r=m-1\). The transform of \(a\) vanishes to order \(m\) there. The transform of \(W\) equals \(-\widehat c(p)H(p)\zeta'(1/2+p)\), of order exactly \(r\). Write \(D_\rho=|\widehat W^{(r)}(p)|>0\) and \(P_y(s)=\prod_{p'\le y}(1-(p')^{-s})^{-1}\) over primes. In \(W_y\), the lower derivatives still vanish and the top one acquires precisely the factor \(P_y(\rho)\).

Integrate \(W_y(s)(T-s)^r e^{-ps}\) first over the half-line, then over the prefix. Inserting \(a*R_y\) on the prefix, the first \(m\) vanishing moments of \(a(u)e^{-pu}\) replace the truncated kernel integral by its complementary tail. The tail of the kernel after age \(T-t\) costs \(J_r e^{-(\delta+1/2)(T-t)}\), where \(J_r=r!/(\delta+1/2)^{r+1}\). Cauchy–Schwarz on the output beyond \(T\) therefore gives, for \(0\le\epsilon<\delta\),
\[
 J_r A_y(T)\ge e^{\delta T}D_\rho |P_y(\rho)|
 -e^{\epsilon T}
 \left(\int_0^\infty v^{2r}e^{-2(\delta-\epsilon)v}\,dv\right)^{1/2}
 \|e^{-\epsilon\cdot}W_y\|_2 .
\]
The last norm is at most \(P_y(1/2+\epsilon)\|e^{-\epsilon\cdot}W\|_2\). Also \(|P_y(\rho)|^{-1}\le\prod_{p'\le y}(1+(p')^{-1/2-\delta})\). With \(y=T^2,\epsilon=0\), both logarithmic costs are \(o(T)\), since \(\sum_{p'\le y}1/\sqrt{p'}=O(\sqrt y/\log y)\). For each zero this yields \(\liminf T^{-1}\log(1+A_y(T))\ge\delta\). Conversely \(|R_y(t)|\ll_h e^{dt}P_y(1/2+d)\) from the complete smooth convolution. Taking the supremum over zeros gives the exact rate \(d\), including \(d=0\) by nonnegativity of the logarithm. A cofinal upper \(A_{T^2}(T)\le C_\eta e^{\eta T}\) for every \(\eta>0\), with \(C_\eta\) fixed before the choice of horizon, would suffice.

## The real contribution already present under RH

Let \(\Psi(x,y)\) count all positive \(y\)-smooth integers up to \(x\). For \(t=T+O(1)\), write \(x=e^t,\ y=T^b,\ b\ge2\), and \(\alpha_0=1-1/b,\ \lambda=\alpha_0-1/2\). Suppose first \(d\le\lambda\). The positive real saddle \(\alpha=\alpha(x,y)\) solves \(\sum_{p\le y}\log p/(p^\alpha-1)=t\). PNT, evaluated at \(\alpha_0+A/\log y\) for fixed real \(A\), makes this sum asymptotic to \(be^{-A}T\). Thus
\[
 \alpha=\alpha_0+\frac{\log b+o(1)}{\log y}.
\]
The positive gap of order \(1/\log y\) is essential when \(d=\lambda\).

The following ratio calculation uses the unconditional Hildebrand–Tenenbaum saddle theorem for the positive smooth count. With \(\phi_j=\partial_\alpha^j\log P_y(\alpha)\), it gives \(\Psi(x,y)=x^\alpha P_y(\alpha)(\alpha\sqrt{2\pi\phi_2})^{-1}(1+O(\log y/t+\log y/y))\). Uniformly for \(0\le s\le(\log T)^3\),
\[
 \frac{\Psi(xe^{-s},y)}{\Psi(x,y)}
 =e^{-\alpha s}\bigl(1+O_b((\log T)^6/T)\bigr).
\]
Indeed \(G(t)=t\alpha+\log P_y(\alpha)\) has \(G'=\alpha\) and \(\alpha'=-1/\phi_2\). On this interval \(\phi_2\asymp_b T\log y\) by PNT and \(|\phi_3|\ll_b\phi_2\log y\) by the finite product. The logarithmic prefactor has derivative \(O_b(1/T)\). For all \(0\le s\le t\), Rankin's bound for the numerator and the saddle formula for the denominator give the upper \(O_b(\sqrt{T\log y}\,e^{-\alpha s})\). [Hildebrand and Tenenbaum, original theorem](https://tenenb.perso.math.cnrs.fr/PPP/Psi%2B.pdf)

Set \(F(s)=e^{s/2}Z(s)\). We have \(F(0)=0\) and \(|F'(s)|\ll_h e^{(1/2+d)s}\). Sum the fundamental theorem of calculus for \(F(t-\log n)\) over all smooth \(n\le x\). This retains the unit atom and gives the exact identity
\[
 \frac{e^{t/2}R_y(t)}{\Psi(x,y)}
 =\int_0^t F'(s)\frac{\Psi(xe^{-s},y)}{\Psi(x,y)}\,ds .
\]
Because \(\alpha-1/2-d\gg_b1/\log T\), the local ratio error costs \(O_b((\log T)^7/T)\). The remaining tail past \((\log T)^3\) costs \(O_b(\sqrt{T\log y}\log T\,e^{-c_b(\log T)^2})\). Integration by parts against \(e^{-\alpha s}\) yields the limit
\[
 \frac{e^{t/2}R_y(t)}{\Psi(e^t,y)}
 =\alpha\widehat Z(\alpha-1/2)+o(1)
 \longrightarrow-\alpha_0 H(\lambda)\frac{\zeta'(\alpha_0)}{\zeta(\alpha_0)}<0 .
\]
At \(\lambda=d\) the expression on the right is the real analytic boundary value of the meromorphic formula, reached from the absolutely convergent side. The sign follows from \(H(\lambda)>0\) and \(\zeta(s),\zeta'(s)<0\) for \(0<s<1\). For the derivative sign, \(\eta(s)=\mathbb E[(1+e^{-X_s})^{-1}]\) with \(X_s\) gamma of shape \(s\) and rate one, so \(\eta>0,\eta'\ge0\) by gamma increments. Differentiation of \(\zeta=\eta/(1-2^{1-s})\) gives the stated strict inequality.

For \(b=2\) and RH, \(d=0,\alpha_0=1/2\), and \(H(0)=1/16\). The terminal interval \(T-1\le t\le T\) gives a lower bound for \(A_y(T)\) with this nonzero sign. For the upper bound use the bounded actual \(Z\) and positivity of the summation weights to obtain \(|R_y(t)|\ll_h e^{(\alpha-1/2)T}P_y(\alpha)\) throughout the prefix, using the saddle for \(t=T\). PNT and the saddle equation give \(\log P_y(\alpha)\sim T/\log y\); the saddle prefactor contributes \(O(\log T)\) to the logarithm. Hence
\[
 \boxed{\quad\mathrm{RH}\ \Longrightarrow\
 \log(1+A_{T^2}(T))\sim\frac{1+\log 2}{2}\frac{T}{\log T}.\quad}
\]
If RH fails, a visible rightward zero gives a positive exponential rate by the preceding section. **A polynomial upper for this critical rough field is impossible in both cases.** The subexponential real contribution comes from the complete smooth multiplier. It does not establish any upper for the unresolved off-line case.

For fixed \(b>2\), the same terminal computation when \(d\le\lambda\) yields a lower exponential rate \(\lambda\), since \(\log\Psi(e^t,T^b)/T\to\alpha_0\). When \(d>\lambda\), the centered estimate applies to any zero with \(\delta>\lambda\) by choosing \(\lambda<\epsilon<\delta\), so its Euler log-cost is \(o(T)\). Taking the supremum gives the lower \(d\). An upper follows for any fixed \(p>\max(d,\lambda)\) from \(|R_y(t)|\ll_h e^{pT}P_y(1/2+p)\) and \(\log P_y(1/2+p)=o(T)\). Thus the exact exponential rate is \(\max(d,1/2-1/b)\). Enlarging the power beyond two creates positive exponential growth even under RH.

The signed rough Möbius asymptotic of Lachand–Tenenbaum applies when \(\exp((\log x)^{2/5+\varepsilon})\le y\le x/2\). The critical polynomial calculation above uses the positive smooth count inside the exact identity \(R_y=N_{\le y}*Z\); the signed theorem's stated range excludes \(y=(\log x)^2\) for large \(x\). [Lachand and Tenenbaum, corrected Theorem 1.1](https://tenenb.perso.math.cnrs.fr/PPP/note-som-crib.pdf)

**Qualification.** The source and visibility declarations are pinned to merged commit `c867a8f15320ad6ac69177e0a498de4cb9d744f9`. The moving-cutoff identity, saddle analysis and growth obstructions here have no fresh Lean or CI qualification. The first missing arithmetic step is an independent subexponential upper on the genuine signed response at unbounded common horizons.
