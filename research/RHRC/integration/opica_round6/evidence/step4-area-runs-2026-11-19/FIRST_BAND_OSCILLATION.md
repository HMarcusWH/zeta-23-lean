# Both signs of the first ordinary-prime band

**DERIVED on paper.** Write \(B=\sup_{\zeta(\rho)=0,\,0<\Re\rho<1}\Re\rho\). Assume \(B<1\), as supplied by the project's pinned external zero ceiling. Fix \(0<\lambda<3/8\), \(L=\lfloor X^\lambda\rfloor\), \(P=X/L\), and \(H(s)=\zeta(s)\eta(2s)\eta(3s)\). Let \(c(n)\) be the Dirichlet coefficients of \(1/H(s)\) on \(\Re s>1\). The first band of the actual residual in the [eta projection](ETA_FILTERED_PRIME_LOCALIZATION.md) is

\[
 D(X)=\sum_{P/2\le p<P}\log p
             \sum_{L<n\le 2L}c(n)(X-np)_+ .
\]

Here \(p\) runs over ordinary primes, with its full logarithmic weight. The part \(p\ge X/(L+1)\) is automatically zero. Terms with \(np=X\) are zero. The lower endpoint \(P/2\) is included. For \(u_+=\max(u,0)\), \(u_-=\max(-u,0)\), the exact two growth exponents are

\[
 \limsup_{X\to\infty}\frac{\log(1+D(X)_+)}{\log X}
 =\limsup_{X\to\infty}\frac{\log(1+D(X)_-)}{\log X}
 =2-\lambda(1-B).
 \tag{1}
\]

Even if \(B=1/2\), this single band has both signs at exponent \(2-\lambda/2\). At \(\lambda=0.37\) this is at least \(1.815\). The full centered area has exponent at most \(1+B\), strictly smaller than (1). Cancellation between prime bands is therefore necessary, including under RH.

## Remove the continuum exactly

For any fixed \(B<s<1\), the classical zero-free half-plane consequences are \(\vartheta(v)-v=O_s(v^s)\) and \(\sum_{n\le v}\mu(n)=O_s(v^s)\) for \(v\ge2\). The [earlier localization](OLD_PRIME_LOCALIZATION.md) gives the explicit-formula and zero-free Perron arguments. They use a line strictly between \(B\) and \(s\). The bound \(B<1\) is the external input in (1). [Pinned zero ceiling](https://github.com/GTimG/QuasiRiemannTracker/blob/42cf5415cfaa4205caaa25ab11160724606cdc33/submissions/2026-11-13-continuum-exact-contact/src/Candidate/Main.lean)

The coefficients of \(1/[\eta(2z)\eta(3z)]\) are absolutely summable with weight \(n^{-s}\) for \(s>1/2\). This follows by expanding the two inverse zetas and the two geometric factors \((1-2^{1-kz})^{-1}\), \(k=2,3\). Convolution with \(\mu\) therefore gives \(\sum_{n\le v}c(n)=O_s(v^s)\). At weight \(n^{-1}\) the same factorization gives \(\sum_{n\le v}|c(n)|=O(v)\).

Put \(g(v)=\sum_{L<n\le 2L}c(n)(X-nv)_+\) on \([P/2,P]\). Its continuous, piecewise linear interpolant is the function itself. Almost everywhere its derivative is \(-\sum_{L<n<X/v}n c(n)\), of size \(O_s(L^{1+s})\) by partial summation. Since \(g(P)=0\), its supremum and total variation are both \(O_s(XL^s)\). Stieltjes integration against \(d(\vartheta(v)-v)\), including the left limit at \(P/2\), now costs \(O_s(P^sXL^s)=O_s(X^{1+s})\). The jump of \(\vartheta\) at a prime endpoint has size at most \(\log P\) and is included in the same estimate.

For \(L<n\le2L\), direct integration gives
\[
 \int_{P/2}^{P}(X-nv)_+\,dv
   =\frac{X^2}{2n}\left(1-\frac{n}{2L}\right)^2 .
\]
Thus, exactly up to the stated centered prime error,
\[
 D(X)=\frac{X^2}{2}S(L)+O_s(X^{1+s}),\qquad
 S(y)=\sum_{y<n\le2y}\frac{c(n)}{n}
                \left(1-\frac{n}{2y}\right)^2 .
 \tag{2}
\]
Another partial summation with \(\sum_{n\le v}c(n)=O_s(v^s)\) shows \(S(y)=O_s(y^{s-1})\) for \(y\ge2\). Its kernel \(n^{-1}(1-n/(2y))^2\) decreases on \([y,2y]\), with initial size \(1/(4y)\).

## Every nontrivial zeta zero survives the band

Set \(f(v)=(1-v/2)^2\) for \(1<v\le2\), and set \(f(v)=0\) elsewhere. Define the entire function \(W(z)=\int_1^2 f(v)v^{z-1}\,dv\). Absolute convergence for \(\Re z>0\) gives
\[
 \int_0^\infty S(y)y^{-z-1}\,dy
   =W(z)\sum_{n\ge1}\frac{c(n)}{n^{1+z}}
   =\frac{W(z)}{H(1+z)} .
 \tag{3}
\]
The part \(0<y<1\) defines an entire correction since \(S(y)=0\) for \(y<1/2\).

For \(z=a+ib\) with \(a\le0\) and \(b>0\), set \(h(t)=e^{at}(1-e^t/2)^2\) on \(0\le t\le\log2\). It decreases strictly to zero. Consequently
\[
 \Im W(a+ib)=\frac1b\int_0^{\log2}(-h'(t))(1-\cos bt)\,dt>0 .
\]
Conjugation covers \(b<0\), and \(W(a)>0\) for real \(a\). In particular \(W(\rho-1)\ne0\) for every nontrivial zeta zero \(\rho\). Both eta factors are entire. Hence (3) has a pole at \(\rho-1\), including when another factor also vanishes there. On the real interval \(z>-1\), both eta factors are positive, \(\zeta(1+z)\) has no zeros, and its pole at \(z=0\) gives a removable zero of the reciprocal. There are no real singularities there.

Fix such a zero, \(\beta=\Re\rho\), and any \(-1<d<\beta-1\). Neither \(S(y)\) nor \(-S(y)\) can be eventually bounded above by \(C y^d\), for any \(C>0\). Indeed such a bound makes \(Cy^d\mp S(y)\) eventually nonnegative. On \([1,\infty)\) its Mellin transform is the sum of \(C/(z-d)\), the signed meromorphic function in (3), and an entire correction. Its finite real abscissa must then be a singularity by Landau's theorem for eventually nonnegative Mellin densities. Convergence already holds for \(\Re z>0\). Analyticity at all real \(z>d\) forces the abscissa to be at most \(d\); an abscissa of minus infinity would give the same conclusion. Absolute convergence in this half-plane contradicts the genuine pole at \(\rho-1\). The positive and negative large values can occur on different sequences. [Landau oscillation theorem, Theorem 3 in Lay](https://personal.math.ubc.ca/~gerg/teaching/592-Fall2018/papers/arXiv.Lay.pdf)

To pass to integer cutoffs, take \(N=\lfloor y\rfloor\). For \(y\in[N,N+1)\) the set \(n>y\) is precisely \(n>N\). Use \((1-n/(2y))_+^2\) for the upper endpoint, so a term appears with zero weight on entry. On \(n\le2N+2\) this weight is Lipschitz in \(y\) with constant \(O(1/N)\). Since \(\sum_{N<n\le 2N+2}|c(n)|/n=O(1)\), it follows that
\[
 |S(y)-S(N)|=O(1/N).
\]
This is \(o(N^d)\). Both signs in the preceding conclusion therefore hold on integer sequences \(N\to\infty\).

## Transfer the oscillations to genuine primes

The upper bound in (2) gives (1) with \(\le\), by sending \(s\downarrow B\). For the reverse inequality, \(2+\lambda(B-1)-(1+B)=(1-\lambda)(1-B)>0\). Choose a zeta zero with real part \(\beta\) arbitrarily close to \(B\), choose \(d<\beta-1\) sufficiently near it, and choose \(s>B\) sufficiently near \(B\) that \(2+\lambda d>1+s\). These choices require no zero to attain the supremum. On the positive and negative integer sequences choose the actual real inputs \(X=N^{1/\lambda}\). Then \(L=N\) exactly and the continuum contribution has the indicated sign with magnitude at least \(X^{2+\lambda d}/2\) arbitrarily late. The centered prime error in (2) is of strictly smaller order. Taking \(d\) arbitrarily close to \(B-1\) proves the lower exponents in (1).

Finally the original \(A(X)+(2/3)X^{3/2}\) is \(O_s(X^{1+s})\) by integrating the ordinary-prime discrepancy. The eta projection reproduces it up to \(o(X^{3/2})\), which forces the rest of the retained ordinary-prime interval to compensate the oscillations in (1). This supplies a lower obstruction to controlling the first uncentered band in isolation. An upper for the complete signed response at the Step 4 scale remains open. No new Lean or CI claim is made.
