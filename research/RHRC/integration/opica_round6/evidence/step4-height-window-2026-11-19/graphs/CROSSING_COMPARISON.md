# Falsification of a geometric proof of crossing stability

**Paper comparison.** Here is a test of whether the prime locations, the Euler product structure, positivity of coefficients, the fixed-width limits and the existing positive exponent upper force the two crossing locations to agree on the required scale. The same two comparison sources may be chosen to agree with any specified finite list of genuine prime-power coefficients. They are distinct from the actual Mangoldt divisor source. At least one violates the proposed crossing estimate at every sufficiently large horizon.

Let \(d\in[0,b]\) be the genuine native displacement supremum, where \(b=0.3733458561\ldots\) is the external ceiling. Take \(c_1=1/8,c_2=1/4\), and for each set \(\alpha=1/2-c\). Choose any fixed real \(\omega>1\). Choose \(P_*\) above the prescribed finite prefix and large enough that \(2P_*^{-\alpha}<1\) for both choices. For every prime power define the altered coefficient
\[
 \Lambda_c(p^k)=\log p\,[1-2{\bf1}_{p>P_*} p^{-k\alpha}\cos(\omega k\log p)] .
\]
It stays positive. This is an actual logarithmic derivative of a comparison Euler product where it converges absolutely. Multiply the zeta product by the two factors \(1-p^{-s-\alpha+i\omega}\) and \(1-p^{-s-\alpha-i\omega}\) at each prime \(p>P_*\). All ordinary prime locations, ordered pair ratios, source derivatives, and the phase order of cuts are preserved. Each changed coefficient has a relative change tending to zero at large base prime. Consequently the fixed-width PNT limits in the dense-pair calculation are identical, including the alternating signs across widths. This comparison does change the genuine divisor equation \(\Lambda=\mu*\log\).

On the ordinary-prime field the difference at \(t\) is
\[
 -2e^{ct}\Re\left(e^{i\omega t}J(c+i\omega)\right)+o(e^{ct}),
 \qquad J(z)=\int j(v)e^{-zv}dv .
\]
This follows by partial summation on the fixed-ratio interval for the prime bases. The omission of the finitely many bases below \(P_*\) costs nothing at sufficiently late ordinary-prime samples. The actual sinc transform has no zeros off its imaginary axis before the half-pole polynomial is applied. Here \(\Re(c+i\omega)>0\) and \(c+i\omega\ne\pm1/2\), so \(J(c+i\omega)\ne0\). All proper powers remain bounded in the full field by the Chebyshev argument, since the multiplier is bounded by three.

The weighted norm of the perturbation over the fixed terminal quadrature is bounded above and below by positive constants times \(e^{cn}\). For the lower bound take the last whole time period of the cosine. Its squared integral is positive uniformly in \(n\)'s terminal phase. The mesh tends to zero, and exactness on constants and positive weights approximate this uniformly equicontinuous translated profile there. The \(o(e^{ct})\) term is uniform at all sufficiently late nodes. The genuine ordinary-prime norm has exponential rate \(d\) in the sense of \(\log(1+\|\cdot\|)/n\). If \(c\ne d\) the triangle and reverse triangle inequalities therefore show that the modified norm has rate \(\max(c,d)>0\). At least one of the two fixed \(c\)'s differs from \(d\). Both modified norms have upper exponential rate at most \(b\).

For that comparison source its individual jump is still \(O_j(n^4\log(n)e^{-n})\), and the diagonal is still \(O_j(n\log n)\). The two actual cut locations in [the crossing calculation](ACTUAL_PRIME_CUT_LOCATIONS.md) must therefore be separated by \(\exp((1+2\max(c,d)-o(1))n)\) or more rank positions on this same prime-ratio graph. This falsifies an inference from the tested geometric and PNT properties alone. The model supplies no evidence about a zero of the genuine zeta function. It pinpoints what a positive argument needs beyond the cut construction: information about the exact prime weights or an equivalent identity distinguishing these altered Euler products.
