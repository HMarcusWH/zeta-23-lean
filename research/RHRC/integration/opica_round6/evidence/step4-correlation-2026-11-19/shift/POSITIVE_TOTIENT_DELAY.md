# Positive arithmetic delay equations for the visible shifted fields

**Paper result.** The exponentially small all-integer comparison in the composite-shell calculation can itself be read as an exact, strictly positive, arithmetic average of the *visible* prime field over delays. Choosing the tilt two even gives coefficients bounded away from zero with a bounded summatory discrepancy. These properties hold without a putative off-line zero assumption.

Use \(F_\alpha=(e^{-\alpha u}\Phi(u))*P\) and let \(I_\alpha\) have bilateral transform \(-J(z)G(w+\alpha)\zeta'(w)\) for \(w=1/2+z\). For \(\alpha=1,2\) define
\[
 g_\alpha(n)=\sum_{d\mid n}\frac{\mu(d)}{d^\alpha}
            =\prod_{p\mid n}(1-p^{-\alpha}).
\]
The exact transfer identities on \(\Re w>1\) are
\[
 \sum_{n\ge1}\frac{g_\alpha(n)}{n^w}=\frac{\zeta(w)}{\zeta(w+\alpha)},\qquad
 \sum_{n\ge1}\frac{g_\alpha(n)}{\sqrt n}F_\alpha(t-\log n)=I_\alpha(t).
\]
All coefficients are strictly positive. The second equality follows by absolute Fubini in the transform half-plane and uniqueness for these continuous functions. At fixed \(t\) the large-delay tail converges absolutely because \(F_\alpha(v)\) decays faster than any exponential as \(v\to-\infty\). It is an infinite identity with the finitely trimmed tails restored by that bound. The transform cancellation takes place against the actual Mangoldt logarithmic derivative.

For \(\alpha=1\), \(g_1=\varphi(n)/n\) and the independent contour argument gives \(I_1(t)=O_j(e^{-3t})\). For \(\alpha=2\) we have \(1/\zeta(2)\le g_2(n)\le1\) and
\[
 \left|\sum_{n\le x}g_2(n)-\frac{x}{\zeta(3)}\right|
 \le\sum_{d\le x}d^{-2}+x\sum_{d>x}d^{-3}=O(1)\qquad(x\ge1).
\]
The independent comparison transform has its elementary \(w=1\) pole canceled by the double zero of \(J\). The gamma factor \(G(w+2)\) is regular at \(w=-2\); its first possible pole is \(w=-4\). Displacing to \(\Re z=-4\) yields \(|I_2(t)|\ll_j e^{-4t}\). The visible field has universal residue \(-m_\rho J(\rho-1/2)\xi(\rho+2)\ne0\) at every rightward zero and is locally recoverable inside the native terminal windows by the same positive theta kernel estimate as tilt one. Here “recoverable” refers to quadrature of this particular observation from the prime field on that window, with independent exponential trimming cost.

The ratio of the archimedean factors also simplifies exactly:
\[
 \frac{G(w+2)}{G(w)}=\frac{(w+2)(w+1)}{2\pi(w-1)}.
\]
Its real pole at \(w=1\) is canceled against the untilted field transform. This gives a direct relation between \(I_2\) and the already bounded untilted theta observation. None of these inversions requires a hypothesis about the growth of \(F_\alpha\) beyond the elementary exponential bound needed for the initial Laplace half-plane.

**Budget check.** The exact delay multiplier \(\zeta(w)/\zeta(w+\alpha)\) extends analytically to a function that vanishes at every nontrivial \(\rho\), whereas \(\xi(w+\alpha)\) does not vanish at a rightward \(\rho\). Thus positivity of the delay weights, their explicit equidistribution and bounded delay output alone give no zero-visible inverse norm. A bilateral growing pure exponential does not have the genuine field's rapid decay at negative time and cannot be substituted inside the positive infinite sum at that exponent. The obstruction is the analytic multiplier identity on the authentic histories, rather than an illegitimate termwise evaluation of a divergent Dirichlet series at a hypothetical zero.

The split also supplies a precise arithmetic experiment. Let \(E_2(x)=\sum_{n\le x}g_2(n)-(x-1)/\zeta(3)\) for \(x\ge1\), with \(E_2(1^-)=0\). Put \(f_t(x)=x^{-1/2}F_2(t-\log x)\). Stieltjes integration by parts gives
\[
 I_2(t)=\frac{e^{t/2}}{\zeta(3)}
          \int_{-\infty}^{t}e^{-v/2}F_2(v)dv
        +\int_1^\infty E_2(x)x^{-3/2}
           [\tfrac12 F_2(t-\log x)+F_2'(t-\log x)]\,dx.
\]
A finite left boundary term is included via the specified \(E_2(1^-)\); the term at infinity is zero. The first signed weighted moment over the *whole* line vanishes because \(\widehat F_2(1/2)=0\); the external upper exponent below \(1/2\) ensures absolute convergence there. Hence that first term is also the negative of the complementary future integral, with the same coefficient. This identifies the exact bounded-discrepancy factor multiplying the derivative of the genuine field. Replacing it by \(\sup |E_2|\) leaves the full derivative-sized error. Obtaining the required signed output upper from this identity remains OPEN.
