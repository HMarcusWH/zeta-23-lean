# The original two-lobe detector and the signed prime window

**19 November 2026.** The merged source proves the two-lobe normalization, the explicit formula, a uniform Archimedean bound and the reflected-history cutoff. This note derives an exact late Archimedean series in that normalization. The signed ordinary-prime estimate remains OPEN.

Write \(s_0=1/4096\), \(S=2s_0\), \(q\) for the frozen even probability density, \(k=(\partial^2-1/4)q\), and \(h=k*k\). Define \(Q(z)=\int e^{-zv}q(v)\,dv\) and \(H(z)=\int e^{-zv}h(v)\,dv=(z^2-1/4)^2Q(z)^2\). Thus \(h\) is real and even, supported on \([-S,S]\). For \(t=2a\), the translated centers are \(c=1+s_0\) and \(c+t\), and the physical aperture is \(L=t+2c\). The original, normalized trial is \(\phi=(k(\cdot-c)+\sigma k(\cdot-c-t))/\sqrt{2M_k}\), with \(M_k=\int |k|^2>0\) and \(\sigma\in\{1,-1\}\). Its two lobes are disjoint when \(a>s_0\). [Source and scale](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/CCM/UniversalSincSourceFacade.lean#L53) · [Original trial](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/ExceptionalZero/UniversalSincOriginalPhaseDepth.lean#L29)

Let \(C(a)\) denote the actual real Weil cross-correlation and put \(Z(t)=\sum_{n\ge2}\Lambda(n)n^{-1/2}h(t-\log n)\). The exact source identities are
\[
 \Re W(\phi,\phi)=\frac{C(0)+\sigma C(a)}{M_k},\qquad
 C(a)=\operatorname{Arch}(t)-Z(t)-Z(-t).
\]
For \(t>S\), \(Z(-t)=0\). At the origin \(C(0)=\operatorname{Arch}(0)\), since \(S<\log 2\) and both von Mangoldt histories then vanish. \(C(0)\) is a fixed self-energy. The late series below does not evaluate it. At a generated aperture with \(\Re W(\phi,\phi)\le-e^{\beta L}\), the exact consequence is
\[
 \sigma Z(t)\ \ge\ M_k e^{\beta L}+C(0)+\sigma\operatorname{Arch}(t).
\]
The source supplies arbitrarily late such trials for each prescribed phase under an off-line zero, possibly at different apertures. This gives a direct-energy entrance independent of estimating the full predecessor Schur inverse. [Formal normalization and phase-depth theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/ExceptionalZero/UniversalSincOriginalPhaseDepth.lean#L202) · [Formal explicit formula, uniform Archimedean bound and reflected-history lemma](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICARound4/ActualSourceHyperbola.lean#L1461)

## Late Archimedean term

The repository uses the Fourier convention \(\widehat h(r)=\int h(v)e^{irv}dv\) and the gamma bracket \(\Re\psi(1/4+ir/2)-\log\pi\). Pair the digamma integral against \(e^{irt}\widehat h(r)\,dr/(2\pi)\). Constant terms pair with \(h(t)=0\) for \(t>S\). The factor \(\cos(rv/2)\) has two translates, each with coefficient \(1/2\); changing variables \(w=v/2\) supplies the factor two. Evenness of \(h\) and its compact support leave
\[
 \operatorname{Arch}(t)=-\int_0^\infty
       \frac{e^{-w/2}}{1-e^{-2w}}h(t-w)\,dw,\qquad t>S.
\]
For rigor one can first truncate the digamma integral away from zero and infinity. The bracketed numerator before Fourier inversion is \(O((1+|r|)v)\) for small \(v\), integrable against the Schwartz transform. After inversion only \(t-S\le w\le t+S\) survives. [Repository gamma convention](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/ExplicitFormula.lean#L62) · [Digamma integral](https://dlmf.nist.gov/5.9.E16)

Geometric expansion on that strictly positive compact interval is absolutely convergent. Consequently
\[
 \operatorname{Arch}(t)=-\sum_{j=0}^{\infty}
   e^{-(1/2+2j)t}H(-1/2-2j).
\]
The first coefficient vanishes by the source half-pole moment. For \(j\ge1\) every coefficient inside the sum is positive. Thus the Archimedean term is strictly negative and strictly increasing to zero. Its first surviving term is
\[
 \operatorname{Arch}(t)=-36\,Q(5/2)^2 e^{-5t/2}+O_h(e^{-9t/2}).
\]
Indeed \(|H(-\lambda)|\le \|h\|_1e^{S\lambda}\). The leading coefficient in \(Z\)'s ordinary explicit formula from the trivial zero \(\rho=-2\) is also **\(-H(-5/2)\)**, because \(-\zeta'/\zeta\) has residue \(-1\) there. In the large-\(t\) correlation \(C(a)=\operatorname{Arch}(t)-Z(t)\) the two trivial-zero contributions cancel. Counting that residue as a further term in \(C(a)\) would double count it.

## Arithmetic still needed

The complete \(Z(t)\) uses only integers \(e^{t-S}\le n\le e^{t+S}\), with every ordinary prime and proper prime power in that window. For squares, partial summation against the prime number theorem gives \(\sum_p(\log p)/p\,h(t-2\log p)=\tfrac12 H(0)+O_h(e^{-c\sqrt t})\). Higher powers contribute \(O_h((1+t)^2e^{-t/6})\) by counting the possible bases and exponents. Hence a uniform eventual one-sided subexponential bound on the ordinary-prime signed window already suffices through one prescribed phase. This observation retains the already paid square and higher-power corrections. Neither the Archimedean sign nor the thin support proves the signed bound. The window has fixed relative width in the integer variable, so its ordinary-prime population grows exponentially in \(t\). [Conditional RH consumer](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICARound4/ActualSourceHyperbola.lean#L1554) · [Quantitative prime number theorem](https://arxiv.org/abs/2206.12557)
