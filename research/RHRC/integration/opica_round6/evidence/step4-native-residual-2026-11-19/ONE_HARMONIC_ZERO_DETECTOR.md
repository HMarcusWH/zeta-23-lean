# One surviving harmonic detects every off-line zero

19 November 2026. **DERIVED on paper. Step 4 remains OPEN.** A single explicit signed portion of the native residue graph detects every nontrivial zeta zero. There is one prescribed integer observation for each integer cutoff, the reduced numerator is \(1\) together with its conjugate, and the true correction terms are accounted for exactly. A bound holding at every sufficiently large cutoff on this one scalar would suffice for RH. A cofinal upper on the same scalar is too weak: it actually has arbitrarily large cutoffs with magnitude only \(O(L)\).

## The actual signed slice

Use the rational calibration over \(9\mid R,\ 2L<R\le3L\) of the full residue graph. Put \(a=24/25,\ c=21/20,\ n_L=\lfloor cL\rfloor\). Retain the denominators \(aL<q\le L,\ (q,6)=1\). The only multiple of \(q\) through \(L\) is \(q\). A correction modulus \(2^jR,\ j=0,1,2\), could be divisible by \(q\) only if \(q\mid R\), which would require \(9q\mid R\), impossible for \(R\le3L\). Consequently the full divisor coefficient on each retained denominator is precisely \(S_q=-\mu(q)/q\). This also proves the same statement for the distributed five-node calibration with nodes \(4^jR\).

Take both conjugate frequencies \(h=1,q-1\). At the actual site their total is
\[
 T_L=\sum_{\substack{aL<q\le L\\(q,6)=1}}
      \frac{\mu(q)}{2q\sin^2(\pi/q)}
              \cos(2\pi n_L/q).
\]
For all sufficiently large \(L\), \(L+\lfloor L^{5/6}\rfloor<n_L\le L^{1.01}\) and the site scale is \(N=L\). The dyadic denominator scale satisfies \(D>aL/2\). Hence \(K=1\) fails both payment inequalities and every displayed frequency belongs to the actual unpaid sum. This assertion for large \(L\) does not prescribe that a small numerical test must have reached that native site.

Let \(B=\sup\{\Re\rho:\zeta(\rho)=0,\ 0<\Re\rho<1\}\) and \(u_\pm=\max(\pm u,0)\). Then
\[
 \boxed{\quad\limsup_{L\to\infty}
       \frac{\log(1+(T_L)_+)}{\log L}
       =\limsup_{L\to\infty}\frac{\log(1+(T_L)_-)}{\log L}
       =1+B.\quad}                                                     \tag{1}
\]

## The transform has a pole at every shifted zero

Consider the real-variable homogeneous weighted sum
\[
 V(x)=\sum_{\substack{ax<q\le x\\(q,6)=1}}\mu(q)q\cos(2\pi c x/q).
\]
The expansion \(1/[2q\sin^2(\pi/q)]=q/(2\pi^2)+O(1/q)\) is uniform on the slice. Rounding the native site changes the cosine by \(O(1/q)\). For \(L\le x<L+1\), only \(O(1)\) terms enter or leave, each \(O(L)\), and every common term changes by \(O(1)\). Therefore uniformly \(V(x)=2\pi^2 T_L+O(L)\).

For \(\Re s>2\) absolute convergence and the substitution \(v=x/q\) give
\[
 \int_1^\infty V(x)x^{-s-1}dx
 =\frac{m(s)}{\zeta(s-1)(1-2^{1-s})(1-3^{1-s})},\qquad
 m(s)=\int_1^{1/a}\cos(2\pi c v)v^{-s-1}dv .
\]
The finite endpoints have no effect under integration; the \(q=1\) term is included. The local factor in the denominator removes multiples of 2 and 3 from the Möbius Dirichlet series. At \(s=1+\rho\) these two factors are nonzero. For \(\rho=\beta+i\gamma\) put \(b=\log(1/a)\) and \(w(t)=e^{-(1+\beta)t}\cos(2\pi c e^t)\). On \(0\le t\le b\) this density is positive and strictly decreasing: \(1<c e^t\le c/a=35/32<9/8\), so both the sine and the cosine of the phase are positive. For \(\gamma\ne0\) integration by parts rewrites a hypothetical vanishing of \(m(1+\rho)\) as
\[
 w(0)=w(b)e^{-i\gamma b}+\int_0^b(-w'(t))e^{-i\gamma t}\,dt .
\]
The sum of the right-side absolute weights equals \(w(0)\). Equality in the triangle inequality would require constant phase where \(-w'>0\), which fails on this interval. At frequency zero the integral is strictly positive directly. Thus \(m(1+\rho)\ne0\), for all heights at once. Every \(\rho\) gives a pole with its original multiplicity.

If \(B<1\), for any \(B<b'<1\) the standard zero-free half-plane consequence \(M(x)=O_{b'}(x^{b'})\) follows by the zero-free inverse-zeta and Perron argument in the factorial note. Removing multiples of 2 and 3 preserves this upper: the corrected summatory function is \(\sum_{i,j\ge0} M(x/(2^i3^j))\) with arguments at least one, and the two geometric factors converge. Partial summation on \((ax,x]\) uses a weight of size \(O(x)\) and derivative \(O(1)\), giving \(V(x)=O_{b'}(x^{1+b'})\). For \(B=1\) absolute counting gives \(O(x^2)\). This proves the required upper exponent independently of any external numerical ceiling. A strictly smaller absolute growth exponent would put the Mellin transform in a half-plane of absolute convergence containing some pole \(1+\rho\). The rounding error has exponent at most one.

For completeness, the same lower exponent holds for each sign. If, for instance, the positive part had smaller exponent, choose \(1<d<1+B\) strictly above that exponent. Then \(g(x)=C x^d-V(x)\ge0\) on \(x\ge1\) for a suitable \(C\), taking account of the \(O(x)\) rounding error. The Mellin transform of \(g\) has a pole at some \(1+\rho\) with \(1+\Re\rho>d\); its abscissa of convergence is therefore strictly above \(d\). A nonnegative Mellin integral has a real singularity at its finite abscissa of convergence. To see this, if it extended analytically across that real point, expand about a real point just to its right in a disk extending to its left. Its derivatives there are the positive logarithmic moments with alternating signs. Evaluating the Taylor series to the left and applying monotone convergence would extend the defining integral past the abscissa. But \(C/(s-d)\) minus the displayed meromorphic function is regular at every real \(s>d\): zeta has no real zeros for \(s-1>0\), its pole at 1 gives a zero of the reciprocal, and both local factors are nonzero. This is a contradiction. Apply the argument to \(-V\) for the other sign. This proves (1).

## Two different arithmetic requirements

An independent \( |T_L|\ll_\epsilon L^{3/2+\epsilon}\) for *all sufficiently large* \(L\), for every \(\epsilon>0\), would imply \(B=1/2\) by (1) and the functional-equation symmetry. An eventual one-sided upper of the same size would suffice by the corresponding sign exponent. In contrast \(|T_{L+1}-T_L|\ll L\), by the rounding, the endpoint count, and the bounded derivative just used. Equation (1) forces infinitely many sign changes or zeros. Therefore \(|T_L|\ll L\) along an unbounded sequence regardless of the value of \(B\). Small values measured at selected cutoffs cannot establish closure by this scalar route.

This single portion of the graph has its own transform comparison. Its absolute size need not be bounded by the magnitude of the signed sum after other rectangles are included. The full-source criterion instead requires a cofinal upper on the complete residual, which has logarithmic exponent \(B-1\) along all integers if \(B>1/2\). Full-source frequency inequality

**First unresolved arithmetic line on this simpler route.** At \(n_L\) the cosine in \(T_L\) has one sign throughout the denominator interval. Available unconditional partial summation bounds use the known exponent for the actual Möbius summatory function. They do not supply square-root cancellation in this long interval with the stated fixed weight. Even proving just one of the necessary eventual one-sided bounds here would resolve RH. No such bound has been established in this calculation.
