# Exact growth of the full variation across true outer-prime fibres

19 November 2026. **DERIVED on paper.** Let \(B\) be the supremum of the real parts of the nontrivial zeta zeros. At the pinned project ceiling \(1/2\le B<1\). For either of the actual four-moment prime-area observations, sum the complete signed cofactor response at each outer prime before taking its absolute value. Write
\[
  K_{i,x}(q)=\sum_{j\le x/q}(x-qj)r_i(j),\qquad
  V_i(x)=\sum_{q\in\mathcal P_i(x)}(\log q)|K_{i,x}(q)|.
\]
Then at the native cutoffs \(\lambda_1=.11,\lambda_2=.37\),
\[
 \boxed{\displaystyle\limsup_{x\to\infty}\frac{\log(1+V_i(x))}{\log x}
       =2-\lambda_i(1-B).}
\]
This is the complete nonnegative observable. The cofactor signs, powers, and exceptional corrections are retained inside each absolute value. A one-sided estimate for this observable at the stated critical exponent would close the mathematical gap. This pass derives the equivalence and partial upper; the critical estimate is open.

## A uniform signed estimate inside every outer-prime fibre

Use \(H_1(s)=\zeta(s)\), \(H_2(s)=\zeta(s)\eta(2s)\eta(3s)\), and \(C_i=1/H_i\). Denote their coefficients by \(h_i,c_i\). The divisor convolution \(h_i*c_i\) is the unit. We have \(\sum_{e\le t}|h_i(e)|\ll t\): for the second coefficient, sum over \(ab^2d^3\le t\) and use convergence of \(\sum b^{-2}d^{-3}\). For \(B<s<1\),
\[
 N_i(t)=\sum_{d\le t}c_i(d)=O_s(t^s).
\]
For \(c_1=\mu\) this is the classical zero-free consequence; for \(c_2\) convolve with the coefficients of \(1/[\eta(2z)\eta(3z)]\), whose absolute Dirichlet series converges at \(s>1/2\). Without any power ceiling, \(N_i(t)\ll_A t/\log^A(2t)\) for every fixed \(A>0\). [Power-bound derivation and pinned input](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md) · [Unconditional estimates for the coefficients](COMPLETE_TERMINAL_COMPOSITES.md)

Keep the actual four calibrations. The low coefficients are \(a_m=-c_i(m)/m\) at \(2\le m\le L\). The extra coefficients lie at \(m=4^kR,\ 0\le k\le3,\ R\asymp L,\ R>2L\), either at one centre or averaged over the permitted centres. The normalized four-by-four system has a fixed inverse. For a single centre each extra coefficient is in fact \(O_s(L^{s-1}\log^2(2L))\). To see this, partial summation at 1 gives \(\sum c_i(m)/m=C_i(1)=0\) and \(-\sum c_i(m)\log(m)/m=C_i'(1)\); convergence and differentiation follow from the displayed prefix bound (also from the arbitrary-log bound at the endpoint). Here \(C_1'(1)=1\) and \(C_2'(1)=1/[\eta(2)\eta(3)]\), exactly the required logarithmic moments. The two errors after truncation are \(O_s(L^{s-1}\log(2L))\). Subtracting \(\log R\) times the first row adds at most one log. For any fractional or integer moment used by either filter, with \(v\in\{1/2,2/3,1\}\), partial summation gives \(\sum_{m\le L}c_i(m)m^{v-1}=O_s(L^{v+s-1})\) since \(v+s>1\). Divide the residual by \(R^v\), including its fixed target: it now costs \(O_s(L^{s-1})\). This proves the coefficient estimate. In the distributed case the **sum of absolute values of all extra coefficients** satisfies the same bound by the triangle inequality. The same proof with arbitrary-log Mertens savings, splitting small arguments at \(\sqrt L\) in positive-power sums, gives \(O_A((\log(2L))^{-A})\) for this sum. [Exact factorial calibrations](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md) · [Exact eta calibrations](../step4-area-runs-2026-11-19/ETA_FILTERED_PRIME_LOCALIZATION.md)

The full residual coefficients have the finite identity
\[
 r_i(j)=\sum_{\substack{ed=j\\d>L}} h_i(e)c_i(d)
       +\sum_{\substack{m\mid j\\m\ {\rm extra}}}m a_m h_i(j/m).
\]
Indeed the constant coefficient in the finite multiplier is \(\sum a_m=1\); the nonunit Dirichlet coefficients are \(-ma_m\). Subtracting its convolution with \(h_i\) from the unit gives the two plus signs above. This includes \(j=1\) and all the low zeros. For \(Y=x/q\ge L\) and \(e\le Y/L\), finite partial summation gives
\[
 \sum_{L<d\le Y/e}(x-qed)c_i(d)
   =qe\int_L^{Y/e}(N_i(t)-N_i(L))\,dt
   \ll_s x(Y/e)^s.
\]
Since \(\sum_{e\le Y/L}|h_i(e)|e^{-s}\ll_s (Y/L)^{1-s}\), this term summed over \(e\) costs \(O_s(xY L^{s-1})\). The remaining correction terms cost \(O(xY\sum_{\rm extra}|a_m|)\), using the absolute prefix of \(h_i\). Consequently, uniformly in all outer primes,
\[
 |K_{i,x}(q)|\ll_s xY L^{s-1}\log^2(2L).
\]
Unconditionally, the same argument gives \(O_A(xY/\log^A(2L))\) on the native ranges: use \(t\ge L\) for the Mertens savings and absorb \(\sum_{e\le Y/L}|h_i(e)|/e\ll\log(2Y)\ll\log(2L)\) by increasing the fixed log power. Summing the power bound with \(\sum_{q\le x}(\log q)/q\ll\log(2x)\) and letting \(s\downarrow B\) gives the upper half of the displayed equality. It also gives the same bound uniformly for any choice of outer phases of modulus at most one.

## Sharpness, with both signs

The native range includes the entire active first band \(x/(2L)\le q<x/(L+1)\), for both cutoffs. On \(L<j\le2L\) the full coefficient is \(c_i(j)\); all correction positions exceed \(2L\), and every proper divisor is at most \(L\). The signed first-band subtotal \(D_i(x)\) has positive and negative limsup exponents \(2-\lambda_i(1-B)\). The earlier first-band proof states this for eta. For the factorial filter the identical argument uses \(H_1=\zeta\) in place of \(H_2\). Here are the points required for that substitution. [First-band proof](../step4-area-runs-2026-11-19/FIRST_BAND_OSCILLATION.md)

Prime partial summation replaces the outer measure by Lebesgue measure with error \(O_s(x^{1+s})\), since \(\sum_{L<j<u}j c_i(j)=O_s(L^{1+s})\) for \(u\le2L\). The continuum is \(x^2 S_i^*(L)/2\), where \(S_i^*(y)=\sum_{y<j\le2y}c_i(j)(1-j/(2y))^2/j\). Its Mellin transform is \(C_i(1+z)\int_1^2(1-v/2)^2 v^{z-1}dv\). The integral is nonzero at every \(z=\rho-1\) by the strict sine-transform sign of the decreasing function \(e^{\Re(z)t}(1-e^t/2)^2\) on \(0\le t\le\log 2\). Both \(C_i\) have poles at all nontrivial zeros of \(\zeta\), and no pole on the real interval \(1+z>0\). Landau's oscillation argument therefore gives both signs at exponents arbitrarily close to \(B-1\) for \(S_i^*\). Rounding \(y\) to \(\lfloor y\rfloor\) costs \(O(1/y)\) using the absolute coefficient prefix. The continuum exponent exceeds \(1+B\) by \((1-\lambda_i)(1-B)>0\), so its lower exponents transfer to the true outer primes. Since \(|D_i(x)|\le V_i(x)\), this proves sharpness. The two signs may occur on different sequences. Indeed the separate positive and negative *fibre masses* of the full observations both have the same limsup exponent, by the same argument and the upper for \(V_i\).

## What would suffice to close the gap

| Observable | Upper exponent from the ceiling \(r=.873346\), to arbitrary \(\epsilon\) | Required upper exponent, to arbitrary \(\epsilon\) |
|---|---:|---:|
| Full factorial fibre variation \(V_1\) | 1.98606806 | 1.945 |
| Full eta fibre variation \(V_2\) | 1.95313802 | 1.815 |

A proof that \(V_1(x)\ll_\epsilon x^{1.945+\epsilon}\) **or** \(V_2(x)\ll_\epsilon x^{1.815+\epsilon}\) for all sufficiently large real \(x\), for every \(\epsilon>0\), forces \(B\le1/2\) by the equality above. Zeta symmetry then gives RH. Conversely RH gives these bounds. A cofinal set of isolated horizons does not suffice for this limsup argument. Estimating every native cofactor prefix by square-root Mertens cancellation would assume a condition as strong as the conclusion.

Even under RH the correct growth exponents of the two unsigned outer sums exceed \(3/2\). Thus an absolute-value estimate across outer primes cannot produce the required \(x^{3/2+o(1)}\) upper for the original signed observation on all sufficiently large horizons. A sharp estimate at the *larger* critical powers above could still close by detecting the zero supremum via the genuine first band. The existing formal Step 4 norm implication has its own hypothesis. No new Lean theorem about \(V_i\), or production closure, is asserted.
