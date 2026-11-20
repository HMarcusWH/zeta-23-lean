# Unconditional bound for the complete signed residual

**DERIVED on paper.** With the notation and genuine arithmetic weights of the squarefree reduction, the following fully coupled bound is available for all sufficiently large \(T\):
\[
 |C_2(T)+C_{\ge3}(T)|\ll_h (1+T)^{1.801}
 \exp\!\left(\frac{T}{2}-0.1853\frac{T^{3/5}}{(\log T)^{1/5}}\right). \tag{1}
\]
Here the implied constant is fixed by the K5 carrier and the absolute constants in the squarefree estimate. The real coefficient in the exponent is retained from the prime-number theorem used below. This strengthens the stretched-square-root saving in the main report and gives a precise measure of the remaining gap. The upper in (1) still has limiting exponential rate \(1/2\).

For \(x\ge23\), Johnston and Yang's Theorem 1.4, equation (1.7), gives \(|\psi(x)-x|\le 0.026\, x(\log x)^{1.801}\exp(-0.1853\,r(\log x))\) where \(r(t)=t^{3/5}/(\log t)^{1/5}\). [Original theorem](https://arxiv.org/pdf/2204.01980#page=2)

Here are the details transferring this to the fixed kernel. For \(m=13,15,17\), the trigonometric autocorrelations in the preceding paper are analytic in their separation on the closed interval from the inside. Their endpoint zeros have orders at least \(m\). Therefore \(|k_m(1-v)|\ll v^m\), \(|k_m'(1-v)|\ll v^{m-1}\). Inserting the latter in \(\int_t^T L^{m-1}k_m'(t/L)dL\), with the moving-endpoint term zero, gives
\[
 |W_T'(T-h)|\ll (1+h)^{17},\qquad |W_T(T-h)|\ll (1+h)^{18}.
\]
At \(t=0\) one may use the one-sided derivative. This prices the normalization at the actual sampling point rather than with the uniform \(T^{18}\) bound.

Put \(g(x)=x^{-1/2}W_T(\log x)\), \(E(x)=\psi(x)-x\). Partial summation gives \(I(T)=[gE]_1^{e^T}-\int_1^{e^T}E(x)g'(x)dx\), since the atomic and continuum measures in the aperture report are the pushforward of \(x^{-1/2}dE(x)\). The lower endpoint supplies \(W_T(0)\) and the upper endpoint vanishes. The initial segment up to \(e^{t_0}\), with \(t_0\) fixed and \(e^{t_0}\ge23\), costs polynomially in \(T\). On the remainder use \(t=\log x\) and \(h=T-t\). The absolute integrand in \(dt\) is bounded by
\[
 C(1+T)^{1.801}(1+h)^{18}e^{t/2-0.1853r(t)} .
\]
Choose \(t_0\) so the derivative of \(t/2-0.1853r(t)\) is at least \(1/4\) for \(t\ge t_0\). The integral costs at most the claimed bound times the fixed integral of \((1+h)^{18}e^{-h/4}\). Equation (3) of the main report adds \(\mathrm{poly}(T)e^{O(T/\log T)}\), absorbed in (1).

This is a two-sided bound on the coupled residual, including the signs of both sectors. For each \(0<\eta<1/2\) the right side of (1), divided by \(e^{\eta T}\), tends to infinity. The available unconditional estimate consequently leaves the eventual one-sided Step 4 inequality open.
