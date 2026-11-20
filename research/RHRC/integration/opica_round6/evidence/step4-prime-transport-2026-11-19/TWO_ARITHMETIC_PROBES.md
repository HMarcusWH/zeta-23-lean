# Two genuine arithmetic observations detect every large response

**DERIVED on paper.** On the original dyadic observation grid, a single sum of nonnegative squared determinants detects the full growth exponent of the signed rough Möbius source at every sufficiently late integer cutoff. The two observation vectors are the genuine primes and the vertices whose largest prime has small cofactor. Their different dependence on the shell position proves a quantitative lower bound independent of the unknown source vector. It removes the separate length-mismatch test required for one observation. The upper on the resulting observable remains open.

## The calculation

Use \(y=\lceil\log_2 X\rceil^2\), \(0<\kappa<.01\) fixed, \(Z=X^\kappa\), and the tree weights \(w_J=2^{-k}/U\) from [the native graph](../step4-harmonic-recovery-2026-11-19/DYADIC_TREE.md). Include either all original nodes or just the fixed coarse nodes. In each node \(J\) record three signed counts:

* \(f_J\) sums the genuine \(\mu(n)\) over all squarefree terminal \(n\) with \(P^-(n)>y\).
* \(p_J\) is minus the number of primes among those vertices.
* \(a_J\) sums the same \(\mu(n)\) over those with \(n/P^+(n)\le Z\).

Primes appear in both observation sets intentionally. Set \(z_J=p_J+i a_J\). Form the exact nonnegative rational observable
\[
 \mathcal D(X)=\sum_{I<J}w_Iw_J\,|z_I f_J-z_J f_I|^2 .
 \tag{1}
\]
Equivalently compute two real Gram determinants. For weighted vectors \(P=(\sqrt{w_J}p_J)_J,\ A=(\sqrt{w_J}a_J)_J,\ F=(\sqrt{w_J}f_J)_J\), write \(\Delta(u,v)=\|u\|^2\|v\|^2-\langle u,v\rangle^2\). Then \(\mathcal D=\Delta(P,F)+\Delta(A,F)\). Each determinant can be computed using three weighted sums; there is no need to enumerate all pairs of nodes. All within-node products retain their actual signs.

## The two observations are quantitatively independent

Let \(0<\sigma<.01\) be fixed. At every sufficiently large \(X\) choose disjoint complete dyadic shells at \(U\asymp X\) and \(V\asymp X^{1-\sigma}\), both entirely inside the original terminal interval. For example take \(U=2^{\lfloor\log_2X\rfloor-1}\) and \(V=2^{\lfloor(1-\sigma)\log_2X\rfloor}\). The scalar product with the unit vector constant \(2^{-s/2}\) on a shell's base nodes and zero elsewhere is its total signed charge divided by \(\sqrt{U2^s}\). Base nodes are also present in the coarse-only calculation.

Write \(P_y=\prod_{p\le y}(1-1/p)^{-1}\). At \(W=U,V\), the two scalar observations of \(P,A\) are respectively
\[
 -\sqrt{W/2^s}\,(1+o(1))/\log W,\qquad
 +\sqrt{W/2^s}\,P_y(1+o(1))/(\log W)^2 .
 \tag{2}
\]
The first follows from ordinary PNT, with every prime retained. The second follows from [the signed cofactor drift](CONE_DRIFT.md). For the second shell the same proof applies with \(\log Z/\log V\to\kappa/(1-\sigma)\in(0,1)\), \(V/Z\to\infty\), \(Z^2<V\), and \(\log y=O(\log\log V)\). These are the parameter restrictions used in its PNT substitution, geometric expansion, and smooth-divisor tail. In particular (2) uses the same \(X,y,Z\) at both observations.

Let \(M\) be the \(2\times2\) matrix obtained by projecting the two columns \(P,A\) onto these orthogonal unit vectors. By (2),
\[
 |\det M|=(1+o_\sigma(1))\,\frac{\sqrt{UV}}{2^s}\,
 P_y\frac{|\log U-\log V|}{(\log U)^2(\log V)^2}.
 \tag{3}
\]
Indeed the two leading products have a limiting ratio different from one **for each fixed \(\sigma>0\)**. No uniformity as \(\sigma\downarrow0\) is used. By the sum-of-squares formula, projection can only decrease the squared area of the two columns. Thus \(\Delta(P,A)\ge|\det M|^2=X^{2-\sigma+o_\sigma(1)}\). The total squared norm \(N=\|P\|^2+\|A\|^2=O(X+\log X)\) by the unsigned tree bound. Write \(\lambda_1\ge\lambda_2\) for the two eigenvalues of their \(2\times2\) Gram matrix. They obey \(\lambda_1+\lambda_2=N,\ \lambda_1\lambda_2=\Delta(P,A)\). Consequently
\[
 X^{1-\sigma-o_\sigma(1)}\le\lambda_2\le\lambda_1\ll X .
\]
The construction of the graph and the columns is independent of \(\sigma\). Taking a lower limit first and then arbitrarily small fixed \(\sigma\) yields \(\lambda_2=X^{1+o(1)}\).

For every real vector \(F'\) on these nodes the elementary spectral inequality now gives
\[
 \lambda_2\|F'\|^2\ \le\ \Delta(P,F')+\Delta(A,F')\
 \le N\|F'\|^2 .
 \tag{4}
\]
Indeed subtract \(\langle P,F'\rangle^2+\langle A,F'\rangle^2\le\lambda_1\|F'\|^2\) from \(N\|F'\|^2\). This is a uniform detection inequality with an independently derived arithmetic lower coefficient. It does not postulate coercivity of the indefinite causal-completion kernel.

## Two neighbouring shells suffice, with a logarithmic conditioning bound

One can quantify the slope in (2). For this calculation **freeze** \(X,y,Z\) and let \(L\) vary over \([\log(X/9),\log(2X)]\). Write
\[
 S_X(L)=\sum_{a\le Z}\frac{\mu_y(a)}{a(L-\log a)}.
\]
The drift calculation yields \(S_X(L)=-P_y/L^2+O_\kappa(P_y(1+\log y)/L^3)\) uniformly here. The corresponding derivative estimate is
\[
 S_X'(L)=2P_y/L^3+O_\kappa(P_y(1+\log y)/L^4).
\]
This second estimate follows by differentiating the **finite exact** sum and estimating its new kernel. In the smooth-divisor expansion of \(\mu_y\), large smooth \(d>\sqrt Z\) again cost arbitrarily high inverse log powers. For \(d\le\sqrt Z\) put \(W=Z/d,\ L'=L-\log d\). The expansion of \((1-v)^{-2}\) is \(1+2v+v^2(3-2v)/(1-v)^2\), with \(v=\log m/L'\) uniformly bounded away from one. In the signed \(m\)-sum the constant moment is \(0\) and the first log moment is \(-1\), up to arbitrary inverse log errors since \(\log W\gg_\kappa L\). The signed remainder after removing \(1/(L')^4\) is bounded: differentiate \((\log m)^2(3-2v)/(m(1-v)^2)\) as a function of \(m\); its derivative is \(O_\kappa((1+\log^2m)/m^2)\). Partial summation against the usual log-saving \(M(m)\) then costs \(O_\kappa(1)\). Thus the sum for the inverse squared denominator starts at \(-2/(L')^3\). Accounting for the minus sign in \(S'_X\) and \(\sum_{d\text{ smooth}}(\log d)/d=O(P_y\log y)\) proves the stated derivative without differentiating an unspecified error.

Define \(r(L)=\int_1^2 S_X(L+\log v)\,dv\,/\,\int_1^2(L+\log v)^{-1}dv\). The quotient rule and the two bounds give \(r'(L)=P_y/L^2+O_\kappa(P_y(1+\log y)/L^3)\). The observed ratio of the cone and prime signed shell charges is \(r(\log W)+O_{\kappa,K}((\log X)^{-K})\) at \(W\asymp X\), for every fixed \(K\). To see this, apply the prime number theorem with arbitrary fixed log savings in the cofactor expansion and at the ordinary prime endpoints, then divide by the prime count \(\asymp W/\log W\). Only the two endpoint approximations are required. Taking \(V=U/2\), with \(U=2^{\lfloor\log_2X\rfloor-1}\), now gives
\[
 r(\log U)-r(\log V)=(1+o(1))P_y\log 2/(\log X)^2 .
\]
These are adjacent whole shells in the terminal interval eventually. Their two projected prime observations have moduli \(\asymp\sqrt{X/2^s}/\log X\), so \(|\det M|\gg_\kappa X2^{-s}P_y/\log^4 X\). Moreover \(N\ll X2^{-s}\): a complete depth in one shell has at most \(U/H\) nodes of length \(H\), with charges at most \(H\) each, so its norm contribution is \(O(H^2/H_0)\). Sum geometrically over \(H\) and then \(U\), also allowing clipped end nodes. Hence
\[
 \boxed{\displaystyle
 c_\kappa\frac{X}{2^s}\frac{P_y^2}{(\log X)^8}\,\|F'\|^2
 \ \le\ \Delta(P,F')+\Delta(A,F')\
 \le C\frac{X}{2^s}\,\|F'\|^2 .}
 \tag{7}
\]
The ratio of the upper and lower coefficients is at most \(O_\kappa((\log X)^8/P_y^2)\). This strengthens the exponent argument to a quantitative conditioning statement for every vector on these nodes. The two consecutive scale measurements require the first nonzero signed cofactor drift and its variation with the scale.

There is also a direct test against just these two shell observations. Let \(e_i\) be their real orthonormal base-average vectors, \(\zeta_i=\langle e_i,P\rangle+i\langle e_i,A\rangle\), and \(u_i=\langle e_i,F\rangle\) for \(i=1,2\). At each weighted node write \(Z_J=P_J+iA_J\). Define \(\mathcal T=\sum_J\sum_{i=1}^2|\zeta_i F_J-Z_J u_i|^2\). If \(Z_J\ne0\), project each complex difference onto the line perpendicular to \(Z_J\) in the real plane. The \(Z_Ju_i\) terms vanish. The squared projections of \(\zeta_1,\zeta_2\) onto *any* unit line sum to at least the smaller squared singular value of the two-shell matrix \(M\). The case \(Z_J=0\) follows directly. Hence \(\mathcal T\ge s_{\min}(M)^2\|F\|^2\). Since the squared Frobenius norm of \(M\) itself is \(O(X2^{-s}/\log^2 X)\) by (2), its smaller squared singular value is at least \(c_\kappa X2^{-s}P_y^2/\log^6 X\). Conversely the square triangle inequality and \(\sum_i |u_i|^2\le\|F\|^2\) give \(\mathcal T\le4N\|F\|^2\). This test needs only two real shell averages of the actual field, two complex shell averages of the probes, and one pass through the nodes. It therefore obeys the same exponent law (5) as the full determinant. With the present dyadic conventions each summed squared term is rational, since the common shell normalization is squared.

## Exact remaining gate

For the genuine vector \(F\), [the rough-source arithmetic transfer](ROUGH_PRIME_TRANSPORT.md) gives \(1+\|F\|^2=X^{2b+o(1)}\), \(b=\sup_\rho\Re\rho-1/2\). It includes the lower from the fixed band and the controls on every excluded sector. In passing from positive node energy to the native primitive covariance, the diagonal costs \(O(\log X)\) and the signed large-GCD correction costs \(O_\epsilon(X^{(1-.01)2b+\epsilon})\) when \(b>0\), or \(O_\epsilon(X^\epsilon)\) at \(b=0\). Combining those bounds with (4) yields
\[
 \boxed{\quad 1+\mathcal D(X)/X=X^{2b+o(1)}.\quad}
 \tag{5}
\]
In particular a single independent arithmetic upper
\[
 \forall\epsilon>0\ \forall R\ \exists\,X\in\mathbb N,\ X\ge R:
 \qquad \mathcal D(X)\le X^{1+\epsilon}
 \tag{6}
\]
would close this route. If \(b>0\), fix any \(\epsilon<2b\); (5) would contradict (6) on every sufficiently late one of its horizons. Conversely \(b=0\) implies (6) at all sufficiently late cutoffs for each \(\epsilon\). The principal obstruction is estimating the squared *actual mixed node counts* in (1). The lower coefficient in (4) cannot serve as their upper. The unconditional Mertens estimate gives \(\mathcal D\ll X^2\exp[-c(\log X)^{3/5}(\log\log X)^{-1/5}]\); the power bound for general \(b\) still has exponent \(1+2b+\epsilon\). [Quantitative cancellation and the one-observation test](GRAM_DISCRIMINANT.md)

The original two-column observations may also be used with the actual compressed source vector from [sparse compensation](SPARSE_COMPENSATION.md) on aligned horizons. Inequality (4) holds for every real vector, and the compressed source preserves the unmasked energy to \(O(\log X)\). The observations themselves remain the original measured columns. The determinant does not assume that a sparse subset by itself obeys the same prime-density formula.

## A portion of the determinant already satisfies the required upper

For a node \(I\) write \(H_I\) for its nominal width and \(H_{0,I}\) for its base width. In (1) every pair of nodes satisfying
\[
 H_I^2H_J^2\le X H_{0,I}H_{0,J}
\]
can be removed **together** at cost \(O(X\log^4(2X))\) at every cutoff. For a fixed shell and depth the weighted sum of \(H_I^2\) over its entire grid is at most \(H_I^2/H_{0,I}\). Since \(|p_I|,|a_I|,|f_I|\le H_I\), the sum of the squared complex minors at two fixed shell-depth choices costs at most a constant times \(H_I^2H_J^2/(H_{0,I}H_{0,J})\). There are \(O(\log^4(2X))\) choices of the two shells and depths. All terms are nonnegative and the argument includes clipped nodes. Therefore (6) is equivalent, with arbitrarily small changes in the preliminary exponent, to its restriction to the complementary pairs whose width product exceeds this threshold. In top shells of comparable size this pays, for example, all pairs with both widths at most order \(X^{3/4}2^{-s/2}\). The difficult signed counts occur in the remaining larger-node comparisons.

At moderate cutoffs the two genuine columns can coincide exactly: if \(Z<y\), the only permitted cofactor in the first sector is 1. Then \(\lambda_2=0\) even while the determinant of a single observation against \(F\) may be positive. The conditioning proof is asymptotic; it makes no finite-cutoff rank promise. The separate [finite Gram calculation](SIGNED_GRAM_CHECK.json) checks the signed counts with the source, cutoffs, and weights fixed. **Step 4 and RH remain OPEN.**
