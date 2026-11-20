# A signed interval bound after subtracting the complete prime density

**DERIVED on paper.** The centered count of all genuine cone labels has the same known upper exponent as the unrestricted Möbius count, uniformly over every interval and in disjoint-node mean square. This removes the previous \(Z^{1-B}\) loss from summing prime errors separately across cofactors. The result also applies to the retained compensation labels on every node at or above the last matching scale. The exponent is still \(B=\sup_\rho\Re\rho\); a square-root upper independent of \(B\) remains open.

## The actual signed measure and its continuum

Use the notation of [CONE_DRIFT.md](CONE_DRIFT.md) and [SPARSE_COMPENSATION.md](SPARSE_COMPENSATION.md). Put \(y=\lceil\log_2X\rceil^2,\ Z=X^\kappa\) and \(\mu_y(a)=\mu(a)\mathbf1_{P^-(a)>y}\) including \(a=1\). For \(X^{.99}/2<U\le X\) and an interval \(I\subset[U,2U)\), define its genuine cone charge and signed ordinary-prime density by
\[
 A(I)=-\sum_{a\le Z}\mu_y(a)\sum_{p:\;ap\in I}1,\qquad
 d(I)=-\sum_{a\le Z}\frac{\mu_y(a)}a\int_I\frac{du}{\log(u/a)} .
\]
The large prime uniquely determines the cofactor, since \(\kappa<.01\). Half-open intervals include precisely the original graph labels. For every grid of spacing \(1\le H\le U\), and arbitrary subintervals \(I_j\) individually selected in its cells,
\[
 \sum_j |A(I_j)-d(I_j)|^2\ll_{\epsilon,\kappa} X^\epsilon U^{2B}.  \tag{1}
\]
In particular each individual centered charge is \(O_{\epsilon,\kappa}(X^\epsilon U^B)\). The full continuum \(d\) is used at the actual endpoints. Subtracting just its first inverse-log term would leave much larger deterministic errors. The same conclusions hold when the prime atoms are weighted by \(\log p\) and the continuum is ordinary length in the prime coordinate.

## Uniform finite cofactor transform

Assume first \(B<1\). Write \(D_Z(s)=\sum_{a\le Z}\mu_y(a)a^{-s}\). For fixed \(B<\sigma<1\), fixed \(C\), and arbitrarily small \(\epsilon>0\),
\[
 \sup_{\substack{\Re s\ge\sigma\\|\Im s|\le X^C}} |D_Z(s)|
         \ll_{\epsilon,\sigma,C}X^\epsilon.                          \tag{2}
\]
To see this, fix \(B<\sigma'<\sigma\) and \(|t|\le X^C\). The truncated Perron proof for twisted coefficients gives, uniformly for \(1\le v\le 2X\),
\[
 \left|\sum_{a\le v}\mu_y(a)a^{-it}\right|\ll_{\epsilon,\sigma',C}
                 X^\epsilon v^{\sigma'}.
\]
Use a half-integer cutoff and height \(W=(3+X+X^C)^4\), and move to \(\Re w=\sigma'\). For the Dirichlet series \(1/\zeta(w+it)\) on that contour the subpower reciprocal upper strictly to the right of \(B\) is available. The rough Euler factor costs at most
\(\prod_{p\le y}(1-p^{-\sigma'})^{-1}=\exp(o_{\sigma'}(\log X))\) because \(\sigma'>1/2\). The vertical integral contributes at most \(v^{\sigma'}X^\epsilon\) after a suitably small preliminary loss. The horizontals cost \(O(X^\epsilon v/W)\), and the truncation error is \(O(v\log^2(2v)/W)\) for coefficients of modulus at most one. The pole of zeta is removable for its reciprocal. Partial summation against \(v^{-\Re s}\) proves (2) by \(\sigma'<\sigma\); for \(\Re s>2\) absolute convergence suffices. This is the same sharp twisted-prefix contour as in [the preceding factorial calculation](../step4-matched-fibres-2026-11-19/FACTORIAL_TERMINAL_MASS_EXPONENT.md).

## Centering before the contour shift

Write the transforms initially on \(\Re s>1\) as
\[
 W_1(s)=\sum_p(\log p)p^{-s}-\int_2^\infty t^{-s}\,dt,\qquad
 W_0(s)=\sum_p p^{-s}-\int_2^\infty \frac{t^{-s}}{\log t}\,dt .
\]
Here
\[
 W_1(s)=-\frac{\zeta'(s)}{\zeta(s)}
    -\sum_{p,k\ge2}(\log p)p^{-ks}-\frac{2^{1-s}}{s-1},
\]
where the double sum means all primes \(p\) and integers \(k\ge2\). Thus \(W_1\) is holomorphic on \(\Re s>B\), including 1, and is bounded by \(O_\sigma(\log^C(2+|\Im s|))\) on \(\Re s\ge\sigma>B\) for a fixed \(C\). The higher-power series converges absolutely; the log-derivative bound follows by Cauchy on a small zero-free disk from the earlier analytic \(\log\zeta\) bound at large heights, and by continuity at bounded heights after the pole is canceled. Also \(W_0'=-W_1\). Extend \(W_0\) by its antiderivative on this half-plane, using its absolutely convergent value at 2. Integrating \(W_1\) along the bounded horizontal segment from \(2+it\) gives the same polylogarithmic bound for \(W_0\). This handles the ordinary-prime logarithmic singularity without choosing separate branches across \(s=1\).

The exact centered measures now have transforms \(-D_Z(s)W_i(s)\). On \(\Re s>1\) this follows by the finite prime dilations and the substitution \(u=at\). Discrete coefficients have modulus at most \(\log(2n)/\log 2\): each divisor prime \(p\mid n\) gives at most one cofactor \(a=n/p\), and \(\sum_{p\mid n}\log p\le\log n\). The unsigned continuous density is \(O(\log(2Z))\) since \(t\ge2\) and \(\sum_{a\le Z}1/a\ll\log(2Z)\).

Sharp truncated Perron at half-integer endpoints \(z\asymp U\), initial line \(1+1/\log(2U)\), and height \(V=(2X)^4\) therefore costs \(O(U\log^C(2X)/V)\) per endpoint. For the continuous part, integrate \((z/u)^{1+1/\log(2U)}\min(1,(V|\log(z/u)|)^{-1})\) against the bounded density. Within distance \(O(U)\) of \(z\) the result is \(O(U\log^C(2X)/V)\) by the integral of the reciprocal distance truncated at \(U/V\). The tails follow from absolute integrability on the initial line. For the integer atoms use the harmonic sum of reciprocal distances to the half integer. Moving an actual interval endpoint by at most one to its half-integer enclosure changes only the continuum by \(O(\log X)\). Empty integer intervals cost the same separately. Summed over a grid with \(H\ge1\), their endpoint-error squares cost \(O(U\log^2(2X))\).

Shift to \(\sigma\); no residues remain after centering. The high horizontal integrals are \(O_{\sigma,\epsilon}(UX^\epsilon/V)\) by (2). On the new vertical one has \(|D_Z(s)W_i(s)|\ll_{\sigma,\epsilon}X^\epsilon\) uniformly through \(V\). Apply the disjoint-interval argument of [TREE_INTERVALS.md](TREE_INTERVALS.md): on \(|t|\le U/H\) keep the exact difference of the two endpoint kernels and use Cauchy plus Plancherel for the disjoint intervals. On each higher dyadic frequency band use the separated left and right log endpoints and the sampling inequality there. Each squared band cost is \(O_{\epsilon,\sigma}(X^\epsilon U^{2\sigma})\). Summing their square roots, then choosing \(\sigma-B\) and preliminary losses sufficiently small, proves (1). If \(B=1\), total variation \(O(U\log^C(2X))\) on the shell suffices. This proof permits any \(Z\le X^\kappa\) under the same assumptions.

For the logarithmic share, partial summation against \(1/\log u\) gives, uniformly in each \(I\subset[U,2U)\),
\[
 \sum_{\substack{ap\in I\\a\le Z}}\mu_y(ap)\frac{\log p}{\log(ap)}
  =-\left(\sum_{a\le Z}\frac{\mu_y(a)}a\right)
        \int_I \frac{du}{\log u} + O_{\epsilon,\kappa}(X^\epsilon U^B).
\]
In the error use the preceding uniform prime-weighted bound for all subinterval prefixes. This improves the \(U^B Z^{1-B}\) signed error from separate prime estimates. The continuum term itself is retained.

## Which covariance remains?

On every original node at or above the last matching scale, write \(L_J\) for the actual signed charge of the retained compensation vertices and \(Q_J\) for the signed charge of the large-cofactor complement. The matching delivers \(L_J=A(J)\) exactly. The centered charges \(L_J-d(J)\) and \(Q_J+d(J)\) therefore both obey the square-energy upper \(O_\epsilon(X^\epsilon U^{2B})\) in each shell and depth. For the latter subtract the former from the full rough charge, which satisfies the same restricted maximal interval bound. As normalized tree energies these are \(O_\epsilon(X^{2b+\epsilon})\) in total. This quantifies the cancellation of the exponent-one component exhibited in [CONE_DRIFT.md](CONE_DRIFT.md).

The continuum charges are signed real numbers attached to intervals and have no integer GCD. This energy comparison does not assign them a primitive-pair mask. The original mask calculation and all irregular residual incidences still use the original integer charges of [SPARSE_COMPENSATION.md](SPARSE_COMPENSATION.md). An independent subpower upper for their total signed covariance has not followed from the centered estimate. No new formal theorem or Step 4 closure is asserted.
