# Unbounded signed excursions of the true prime area in multiplicative intervals

**DERIVED on paper.** Put \(A_\vartheta(x)=\int_2^x(\vartheta(v)-v)\,dv\), \(A_\pi(x)=\int_2^x(\pi(v)-\operatorname{li}(v))\,dv\), and \(B=\sup_\rho\Re\rho\) over nontrivial zeta zeros. If a zero has real part \(b>1/2\), there are constants \(K>1\) and \(c>0\), depending on that real part and the true zeros, such that **every sufficiently late** \([X,KX]\) contains points \(x_+\) and \(x_-\) satisfying
\[
 A_\vartheta(x_+)>c x_+^{1+b},\qquad A_\vartheta(x_-)<-c x_-^{1+b}. \tag{1}
\]
No zero need attain \(B\). If RH holds, the published signed area theorem gives \(A_\vartheta(x)<0\) at every \(x>2\). Hence in either case some fixed finite multiplicative spacing suffices for negative \(A_\vartheta\) horizons. The off-line alternative actually gives both signs.

## A positive measure isolating one conjugate pair

For sufficiently large \(x\), the integrated explicit formula and the elementary estimate on higher prime powers give
\[
 A_\vartheta(x)=-\sum_\rho\frac{x^{1+\rho}}{\rho(1+\rho)}
              + O(x^{3/2}\log^2 x).
\]
Indeed \(\int_2^x(\psi-\vartheta)\ll x^{3/2}\log^2 x\), and the deterministic terms of the integrated formula cost \(O(x)\). The zero series converges absolutely and uniformly on compact positive \(x\)-intervals because \(\sum_\rho|\Im\rho|^{-2}<\infty\). [Johnston, Lemma 2.3 and proof of Lemma 2.6](https://arxiv.org/pdf/2201.06184#page=4)

Select any \(s\) with \(1/2<s<b\) and the zero \(\rho_*=b+i\gamma_*\) with least positive ordinate at that real part. Ingham's density theorem gives \(N(s,T)\ll_{s,\epsilon}T^{3(1-s)/(2-s)+\epsilon}\). The exponent preceding \(\epsilon\) is strictly less than one for every \(s>1/2\). Choosing a fixed smaller \(\epsilon\) and summing over dyadic octaves gives
\[
 \sum_{\substack{\beta\ge s\\ \gamma>0}}\frac1\gamma<\infty .
\]
The estimate permits multiplicity. [Ingham's estimate in Guth and Maynard, equation (1.2)](https://arxiv.org/html/2405.20552v2#S1)

For each distinct positive-ordinate zero \(\rho=\beta+i\gamma\), \(\beta\ge s\), other than \(\rho_*\), use the probability measure
\[
 \nu_\rho=\frac{e^{(1+\beta)d_\rho}\delta_0+\delta_{d_\rho}}
                 {1+e^{(1+\beta)d_\rho}},\qquad d_\rho=\pi/\gamma.
\]
Its exponential moment at \(z\) is \(M_\rho(z)=(e^{(1+\beta)d_\rho}+e^{zd_\rho})/(1+e^{(1+\beta)d_\rho})\). It vanishes at \(z=1+\rho\) and at its conjugate. Let \(\nu\) be the law of the sum of independent shifts with these individual laws. The sum converges absolutely and its support lies in \([0,W]\), \(W=\sum_{\rho\ne\rho_*}d_\rho<\infty\), where the sum here uses the selected cutoff \(\beta\ge s\). Its exponential moment \(M(z)\) is the locally uniformly convergent product of the \(M_\rho(z)\); this follows from \(|M_\rho(z)-1|\ll_C d_\rho\) on each complex compact set \(C\).

The possible extra zeros of an individual factor matter. At \(z=1+b+i\gamma_*\), zero magnitude would require \(\beta=b\) and \(\gamma_*/\gamma\) to be a positive odd integer. The least-ordinate choice excludes every such other factor. Since \(\sum |M_\rho(1+\rho_*)-1|<\infty\), the product at \(1+\rho_*\) is nonzero as well. Repeated zeros at the selected ordinate and real part have all been spared. Their multiplicity multiplies the surviving coefficient.

Write \(\mathcal{A}(t)=\int A_\vartheta(e^{t+u})\,d\nu(u)\). Integration against \(\nu\) can be interchanged with the absolutely convergent explicit formula. Every unwanted zero with \(\beta\ge s\) disappears. For the others use \(e^{(1+\beta)(t+u)}\le e^{2W}e^{(1+s)t}\); the higher-power cost is \(O_W(e^{3t/2}(1+t)^2)=O_{W,s}(e^{(1+s)t})\). Thus, with \(m_*\) the multiplicity,
\[
 \mathcal A(t)=2e^{(1+b)t}\Re\!\left(
 -\frac{m_*M(1+\rho_*)}{\rho_*(1+\rho_*)}e^{i\gamma_*t}\right)
 +O_{\nu,s}(e^{(1+s)t}).                                      \tag{2}
\]
In every log-time interval of length \(2\pi/\gamma_*\), the cosine attains both extrema. At each such sufficiently late time at least one argument \(e^{t+u}\) in the support of the positive averaging measure attains the signed bound, with a fixed loss at most \(e^{(1+b)W}\) when converting the scale to \(e^{t+u}\). This proves (1) with \(K=\exp(W+2\pi/\gamma_*)\). All constants for the selected pair are fixed before the observation interval.

## When the supremum is unattained

Suppose \(B>1/2\) is unattained. Choose \(s_j\uparrow B\), \(s_1>1/2\), and an actual real part \(b_j>s_j\) for each \(j\). Take the least positive ordinate \(\gamma_j\) on the line \(b_j\). The supports satisfy
\[
 0\le W_j\le\pi\sum_{\substack{\beta\ge s_j\\\gamma>0}}\frac1\gamma
 \longrightarrow0 .
\]
The majorant at \(s_1\) is summable and each zero eventually leaves the tail. Also \(\gamma_j\to\infty\), since bounded height contains finitely many zeros. Hence \(K_j\to1\). For **each fixed** \(K>1\), every sufficiently late \([X,KX]\) contains both signed excursions of (1), with a corresponding fixed \(b_j\) arbitrarily close to \(B\). The thresholds and the positive amplitude constants are allowed to depend on \(K,b_j\).

## When a zero attains the supremum

If \(B>1/2\) is attained, dominated convergence in the same zero series gives
\[
 \frac{A_\vartheta(e^t)}{e^{(1+B)t}}=
 F_B(t)+o(1),\qquad
 F_B(t)=-\sum_{\Re\rho=B}\frac{e^{i(\Im\rho)t}}{\rho(1+\rho)} .
\]
This holds even if infinitely many zeros attain \(B\) or other zeros approach it. The uniformly convergent trigonometric series is real, has mean zero and has a nonzero Fourier coefficient. It takes values of either sign. Indeed a nonzero continuous Bohr almost-periodic function of one sign has nonzero mean: near a point with a strict signed margin, continuity and its relatively dense almost periods reproduce intervals with a fixed signed area. Recurrence of a finite trigonometric polynomial follows by compactness of the group closure of its phase flow, and uniform approximation gives recurrence of the series. We obtain simultaneous fixed-width positive **intervals** and negative intervals in each sufficiently late log window of some fixed length.

At an attained \(B\), these intervals also work for \(A_\pi\). In the [positive-kernel partial summation identity](../step4-strip-2026-11-19/ORDINARY_PRIME_AREA.md), one has \(A_\vartheta(u)=O(u^{1+B})\) and \(-K'_x(u)\ll 1/(u\log^2u)+x/(u^2\log^2u)\) for \(u\ge2\). Integration yields
\[
 A_\pi(x)=\frac{A_\vartheta(x)}{\log x}
            +O_B(x^{1+B}/\log^2 x).
\]
This error is smaller than the attained-edge logarithmic signal. For a spared zero \(b<B\), the last error bound is larger than the isolated signal \(x^{1+b}/\log x\). The same fixed spacing for \(A_\pi\) in the unattained case does not follow from this comparison. Earlier work discusses the distinction between attained-edge sign changes and global counts for the **unsmoothed** prime counting error. [Kaczorowski, Theorem A and introduction](https://personal.math.ubc.ca/~gerg/teaching/592-Fall2018/papers/1991.Kaczorowski_4.pdf)

## Comparison with the endpoint sign-run criterion

The explicit formula gives \(|A_\vartheta'(u)|=|\vartheta(u)-u|\ll_\epsilon X^{B+\epsilon}\) almost everywhere for \(u\asymp X\). A point with \(A_\vartheta(u)>c u^{1+b}\) therefore lies beside a positive interval of length \(\gg X^{1+b-B-\epsilon}\). The same applies to negative excursions. For any fixed integer power \(k\), choose \(b\) sufficiently close to \(B\) and \(\epsilon\) so that \(B-b+\epsilon<1/k\). Consecutive \(n^k\asymp X\) are spaced \(O_k(X^{1-1/k})\), hence each such sign interval contains \(\gg M^{1-k(B-b+\epsilon)}\) consecutive endpoints, \(M=X^{1/k}\). An interval can be clipped inside a slightly enlarged fixed multiplicative window without affecting its exponent, by locating the original excursion in a strictly interior multiplicative subwindow whenever its spacing permits.

When \(B\) is attained, some positive runs have length \(\gg M\). When it is unattained, their length exceeds \(M^{1-\delta}\) for every **fixed** \(\delta>0\) on sufficiently late multiplicative windows (with dependent thresholds and constants), even though negative points occur in every such window. Thus a multiplicative spacing tending to one does not imply a power saving in run length. The missing estimate requires a fixed saving exponent uniformly in the starting point. The unconditional negative-horizon deduction here supplies neither that estimate nor a contradiction with an off-line zero. [Exact sign-run criterion](../step4-strip-2026-11-19/COUNT_SAVING_SCOPE.md)
