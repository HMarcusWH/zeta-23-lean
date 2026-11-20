# The remaining signed covariance on nearly equal primitive labels

**DERIVED on paper, 19 November 2026.** The band theorem supplies an actual arithmetic reduction beyond finite coverage. The hard part can be restricted to pairs very near one another in logarithmic scale, both near the top cutoff in power scale, with a small common divisor. This reduction uses signs when estimating the common-divisor and earlier-label sectors. All fields below use the native coefficients \(\mu_6(n)=\mu(n)\mathbf1_{(n,6)=1}\). Step 4 remains **OPEN**.

## One explicit sufficient inequality

For integer \(X\), fix \(\theta=1/100,\ h_X=\exp(-\sqrt{\log X})\). Partition the terminal labels \(X^{1-\theta}<q\le X\) by \(\lfloor\log(X/q)/h_X\rfloor\). For a fixed integer \(j\) set
\[
 C_j(X)=4\sum_{\substack{q<r\ \text{in the same terminal bin}\\(q,r)<X^\theta}}
 \frac{\mu_6(q)\mu_6(r)}{\sqrt{qr}}\,
 \cos(j\ell)\frac{\sin(5\ell)}{\ell},\qquad \ell=\log(r/q).
\]
A proof that, **for every fixed integer \(j\) and every \(\epsilon>0\), arbitrarily large integer \(X\) satisfy \(C_j(X)\le X^\epsilon\)** would exclude all rightward zeros. This is a signed, one-sided upper. Each \(j,\epsilon\) can use its own sequence of cutoffs. Both \(q/(q,r)\) and \(r/(q,r)\) exceed \(X^{0.98}\), and \(1<r/q\le e^{h_X}\). For a fixed \(j\) the cosine and sinc factors are eventually positive throughout these bins. The products of the actual two Möbius labels supply the varying signs.

## Proof that discarded sectors cannot carry the required exponent

Suppose there is a rightward zero, and put \(b=B-1/2>0\). For any desired sufficiently small loss \(s>0\) there is a fixed integer \(j\) such that
\[
 \|D_X\|_{I_j}^2\gg X^{2b-s},\qquad
 D_X(t)=\sum_{q\le X}\mu_6(q)q^{-1/2-it},\quad I_j=[j-5,j+5]
\]
at **every** sufficiently large \(X\); the norm uses ordinary \(dt\). Here is why near-full power is available on a fixed-width interval. For a zero \(\rho=1/2+\delta+i\gamma\) near the right edge, use the box construction of FIXED_BAND_THEOREM.md, with \(N=\lfloor\kappa\log X\rfloor\), centered at \(\gamma\). Its total lower has exponent at least \(2\delta-\kappa\delta\). The spectral energy outside \([\gamma-4,\gamma+4]\) costs \(O(X^{2b+\eta}2^{-2N})\), using the full truncated-field Plancherel bound in that note. Since \(2\log2>b\), choose \(\kappa\) small enough for the requested loss and then \(\delta\) sufficiently near \(b\), with \(\eta>0\) sufficiently small. The inner-band lower follows. The nearest integer center contains this entire interval. This order of choices works even if no rightmost zero attains \(B\).

The elementary bound used for the discarded sectors is, for \(T\ge1,\ l\ge1\) and fixed bounded \(I\),
\[
 \sup_{t\in I}\left|\sum_{n\le T,\,(n,6l)=1}\mu(n)n^{-1/2-it}\right|
 \ll_{\eta,I} l^\eta T^{b+\eta}\quad(\eta>0).
\]
Indeed the ordinary Mertens upper \(M(y)\ll_\eta y^{B+\eta/2}\) in terms of the true supremum \(B\) passes to the restricted coefficients by convolution with the indicator of numbers supported on the prime divisors of \(6l\). The corresponding Euler product is \(O_\eta(l^\eta)\), since for large \(p\), \((1-p^{-1/2})^{-1}\le p^\eta\), and the finitely many small primes cost a constant. Partial summation against \(n^{-1/2-it}\) proves the claim. If \(B=1\), direct counting gives the required upper. This bound does not assume \(b=0\). The cutoff may also range over an interval by subtraction of prefixes.

The field from \(q\le X^{1-\theta}\) has norm at most \(O_{\eta,j}(X^{(1-\theta)(b+\eta)})\). Choose \(s<2\theta b\), with room for \(\eta\). The triangle inequality therefore forces the terminal field to have squared norm \(\gg X^{2b-s}\). There are at most \(1+\theta\log X/h_X=X^{o(1)}\) terminal bins. Cauchy's inequality gives
\[
 \sum_{\mathcal I}\|D_{\mathcal I}\|_{I_j}^2\ \ge\
 \frac{\|D_{\rm terminal}\|_{I_j}^2}{\#\{\mathcal I\}}
 \gg X^{2b-s-o(1)} .
\]
This positive estimate allows removal of all interactions between different bins. It keeps every signed term within each bin.

It remains to estimate interactions whose two labels share a large common divisor. For a single bin \(\mathcal I\), group the ordered quadratic expansion by the **exact** GCD \(d\). Terms vanish unless \(d\) is squarefree and coprime to six. Write \(q=du,\ r=dv\); the Möbius product is \(\mu^2(d)\mu(u)\mu(v)\) with \((uv,6d)=1,\ (u,v)=1\). Expanding the last indicator by Möbius inversion gives the exact contribution at each frequency \(t\),
\[
 \frac{\mu_6(d)^2}{d}
 \sum_{\substack{e\le X/d\\(e,6d)=1}}\frac{\mu(e)}e
 \left|\sum_{\substack{k:\,dek\in\mathcal I\\(k,6de)=1}}
        \mu(k)\,k^{-1/2-it}\right|^2 .
\]
To verify the coefficient of \(e\), after setting \(u=eu',\ v=ev'\), each nonzero term has \(\mu(e)^2\) and both new labels are coprime to \(e\); hence \(\mu(e)\mu(e)^2=\mu(e)\). The \(d^{-it}\) and \(e^{-it}\) phases cancel inside each squared norm. Applying the restricted prefix estimate at \(T=X/(de)\) and summing the exterior \(d,e\) absolutely now gives the bound for all \(d\ge D\) in one bin,
\[
 \ll_{\eta,j,b}
 X^{2b+2\eta}\sum_{d\ge D}d^{-1-2b}\sum_{e\ge1}e^{-1-2b}
 \ll_{\eta,j,b} X^{2b+2\eta}D^{-2b}.
\]
The same bound holds after integrating on the fixed interval. With \(D=X^\theta\), summing over all bins costs only \(X^{o(1)}\), so this sector is smaller by a fixed power. This calculation controls a **signed** contribution; taking termwise absolute values in the original graph would lose the improvement.

The entire diagonal costs at most \(10\sum_{q\le X}1/q=O(\log X)\), also sufficient if only the \(d<D\) part of it remains. The residual of the same-bin energies after the large-GCD and remaining diagonal terms is exactly \(C_j(X)\). Therefore, for any sufficiently small requested loss \(\lambda>0\), one can fix \(j\) for which \(C_j(X)\gg X^{2b-\lambda}\) at every sufficiently large \(X\) (choose \(s<\min(\lambda,2\theta b)\) with strict room for errors). This contradicts the proposed cofinal upper for that one \(j\). No independent proof of the proposed upper is known from this calculation.

The terminal cancellation is visible on finite graphs, and the signed covariance can have either sign. FIXED_BAND_CHECK.json covers all pairs in three complete bands; NATIVE_PAIR_SECTOR.json tests the additional bin and GCD restrictions at one finite cutoff. Neither finite test determines the sign or growth rate at late cutoffs.
