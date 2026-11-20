# A positive quadrature criterion for the genuine prime response

**DERIVED on paper, 19 November 2026.** There is a fixed deterministic array of \(O_h(n^2)\) times in each log-time block \([n,n+1]\) for which one signed upper would suffice to exclude all off-line zeros. The required arithmetic upper over these infinitely many blocks is OPEN.

Let \(Z(t)=\sum_{d\ge2}\Lambda(d)d^{-1/2}h(t-\log d)\) be the complete real response from [the native window](NATIVE_WINDOW.md). The merged source proves a Gevrey-2 bound for the seed \(q\). Two derivatives and a convolution preserve this order for \(h=k*k\), after increasing the constants: \(((m+2)!)^2/(m!)^2\) grows polynomially in \(m\) and is absorbed in a fixed exponential. Thus \(\|h^{(m)}\|_\infty\le C B^m(m!)^2\) with \(B\ge1\) fixed before all apertures and zeros. Chebyshev's estimate \(\psi(x)=O(x)\), the native window and local finite summation give
\[
 |Z^{(m)}(t)|\le C_h e^{t/2} B^m(m!)^2 \qquad(t\ge1).
\]
For \(g_s(t)=e^{-st}Z(t)\), Leibniz gives the same derivative bound on the block with \(e^{(1/2-\Re s)n}\) and an extra locally bounded factor in \(s\). Indeed, after division by \(B^m(m!)^2\), the sum of derivative factors is bounded by \(\sum_{j=0}^m (|s|/B)^j (m-j)!/(j!m!)\le e^{|s|/B}\). [Formal source derivative bound](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/CCM/UniversalSincPhysicalBounds.lean#L195)

## The sampling rule

For each integer \(n\ge1\), divide \([n,n+1]\) into \(J_n=\lceil e^2 Bn\rceil\) equal panels, each of width \(d_n=1/J_n\). On each panel use ordinary \(n\)-node Gauss–Legendre quadrature. Write \(t_{nj},w_{nj}\) for all resulting nodes and weights in the block. Every \(w_{nj}>0\), and \(\sum_j w_{nj}=1\). These nodes and weights depend only on the fixed source and \(n\). [Gauss quadrature positivity and polynomial exactness](https://dlmf.nist.gov/3.5.v)

Subtract the Taylor polynomial of \(g_s\) of degree \(n-1\) at the left endpoint of each panel. Quadrature integrates it exactly. The uniform panel remainder is at most
\[
 C_s e^{(1/2-\Re s)n} B^n n!d_n^n
 \le C_s e^{(1/2-\Re s)n} e^{-2n}.
\]
The total absolute error on a block is at most twice that supremum, because both the integration measure and the positive quadrature weights have total mass one there. Thus the block-error series is normally convergent on \(\Re s>-3/2\). The sum \(E(s)\) is holomorphic there, since each finite-block error is entire. On the original domain \(\Re s>1/2\),
\[
 D_Z(s):=\sum_{n,j} w_{nj} Z(t_{nj})e^{-s t_{nj}}
 =\widehat Z(s)+E(s),
 \qquad
 \widehat Z(s)=-H(s)\frac{\zeta'(1/2+s)}{\zeta(1/2+s)}.
\]
The integral on \([0,1]\) has been included in the entire correction to \(E\), with the sign fixed by this equality. Thus \(D_Z\) retains every rightward pole and is regular along the positive real axis, including \(s=1/2\). The source double zero removes the pole there. The sinc product is nonzero at shifted rightward zeros \(p=\rho-1/2\): its Fourier argument \(ip\) has nonzero imaginary part and \(p^2-1/4\ne0\). [Formal sinc visibility](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/CCM/UniversalSincDetector.lean#L241)

## The unpaid one-sided estimate

It suffices to prove, with the positive part applied **after** evaluating the complete signed arithmetic field at a node,
\[
 \forall\eta>0\quad \exists C_\eta,n_\eta\quad
 \forall n\ge n_\eta:\quad
 \sum_j w_{nj}\max(Z(t_{nj}),0)\le C_\eta e^{\eta n}.
 \tag{A}
\]
Under (A) the positive-part Dirichlet series \(D_+\) is holomorphic on \(\Re s>0\) by absolute convergence. The negative-part series \(D_-\), formed with \(\max(-Z,0)\), is a positive measure's Laplace transform, initially convergent for \(\Re s>1/2\). On that initial domain \(D_-=D_+-D_Z\), so it has analytic continuation along the entire positive real axis.

For completeness, a positive measure with a finite real convergence abscissa \(a\) must be singular there. If the transform were analytic in a disk about \(a\), take \(s_0>a\) sufficiently close to \(a\). Its Taylor expansion about \(s_0\), evaluated at \(s_0-r<a\) inside the disk of convergence, has nonnegative terms \(\int e^{-s_0t}(rt)^m/m!\,d\mu(t)\). Monotone convergence would give a finite integral at \(s_0-r\), contradicting the abscissa. Applying this to \(D_-\) makes it holomorphic throughout \(\Re s>0\). Then \(D_Z=D_+-D_-\) is holomorphic there. A rightward zero gives residue \(-m_\rho H(\rho-1/2)\ne0\), a contradiction by uniqueness of meromorphic continuation. Reflection addresses leftward zeros. The same implication holds with the two signs interchanged.

At the all-positive-exponent scale, (A) is equivalent to an eventual one-sided bound at every displayed node. A pointwise bound implies (A) by \(\sum_jw_{nj}=1\). Conversely, each weight is at least \(d_n/n^2\). To see this, a cardinal polynomial \(\ell\) on a panel has \(\ell(t_{nj})=1\) and \(w_{nj}=\int\ell^2\) by exactness. Cauchy–Schwarz in the normalized Legendre basis and \(|P_k|\le1\) give \(|\ell(t_{nj})|^2\le(n^2/d_n)\int\ell^2\). Multiplying the bound in (A) by \(O_h(n^3)\) costs an arbitrarily small exponential increment. A signed block sum without the positive part permits cancellation between sample times and does not give this argument.

Each sample still contains the full signed prime-power sum at its stated time. For example, at late \(t\) its ordinary-prime window alone contains asymptotically \((e^S-e^{-S})e^t/t\) primes by the prime number theorem. The polynomial node count concerns only the observation times. It neither provides a polynomial-cost evaluation of all these sums nor proves (A). No numerical quadrature or finite collection of green checks establishes the required eventual arithmetic bound.
