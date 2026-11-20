# What recurs in the two prime cutoffs

**Paper result, 19 November 2026.** Suppose the genuine displacement supremum \(d\) is positive. Write \(p=\rho-1/2\) and \(A_p=m_\rho J(p)\). On the physical transverse branch of [the cut-rate theorem](ACTUAL_CROSSING_RATE.md), the normalized difference of the two cut locations has the explicit asymptotic
\[
  e^{(1-2d)n}(x_1-x_0)=\frac{H_d(n)}{K'(\Delta_*)}+o(1),\qquad
 H_d(t)=\int_0^\infty e^{-2du}
     \left|\sum_{\Re p=d} A_p e^{i\Im(p)(t-u)}\right|^2du .
\]
The scalar \(H_d\) is uniformly almost periodic. It is identically zero when no zero attains the supremum. If the supremum is attained it is bounded away from zero uniformly in \(t\). This describes exactly which scaled signal can recur.

Indeed the source transform has \(\sum_p|A_p|<\infty\), including both signs and multiplicity. Let \(F_d(t)=-\sum_{\Re p=d} A_p e^{i\Im(p)t}\). By dominated convergence, the absolute sum of \(A_p e^{(\Re p-d)t}\) over the other zeros tends to zero. The trivial-zero contribution decays as well. Thus \(e^{-dt}P(t)=F_d(t)+o(1)\) pointwise and uniformly on sufficiently late tails. \(F_d\) is a uniform limit of finite trigonometric sums. Its squared modulus convolved against the integrable exponential kernel gives the stated uniformly almost-periodic \(H_d\).

For the positive quadrature at \(t_i\in[n-2\log n,n]\), multiply the full native energy by \(e^{-2dn}\). Replacing \(e^{-dt_i}P(t_i)\) by \(F_d(t_i)\) gives \(o(1)\), since \(\sum w_i e^{-2d(n-t_i)}=O_d(1)\). This follows from positivity and constant-exactness on each panel of width \(O(1/n)\), comparing the exponential's supremum and infimum. The same quadrature sum for the approximating integrand \(e^{-2d(n-v)}|F_d(v)|^2\) differs from its integral by \(o(1)\). Use uniform continuity and boundedness of \(F_d\) on the line, and sum each panel's oscillation against that exponential weight. Extending the integral over backwards age \(u\) to infinity costs \(O_d(n^{-4d})\). The identical argument gives the asymptotic for the continuous integral. Restoring the ordinary-prime energy causes \(o(1)\) after normalization by \(e^{-2dn}\) by the proved prime-power norm bound. Its diagonal costs \(O(n\log n)e^{-2dn}\). The signed calibration \(S_n/[W_n(x_1-x_0)]\to K'(\Delta_*)\), with \(W_n/e^n\to1\), now gives the displayed relation. Likewise \(e^{-2dn}R_Y(n)=H_d(n)+o(1)\) for the continuous fixed-sieve covariance on the original log window.

If any top zero exists, choose one of its distinct ordinates \(\gamma_0\), with nonzero genuine coefficient \(A_0\). The top ordinates have no finite accumulation, so \(\sum_{\gamma\ne\gamma_0}|A_\gamma|/|\gamma-\gamma_0|<\infty\). The average of \(F_d(t-u)e^{i\gamma_0u}\) over \(0\le u\le W\) then differs from \(-A_0 e^{i\gamma_0t}\) by at most \(2W^{-1}\sum_{\gamma\ne\gamma_0}|A_\gamma|/|\gamma-\gamma_0|\), uniformly in \(t\). Choose one fixed \(W\) large enough to make this less than \(|A_0|/2\). Cauchy–Schwarz yields
\(H_d(t)\ge e^{-2dW}W|A_0|^2/4>0\).
A recurrence of phases, including along integer shifts, therefore repeats a positive scaled energy and a nonzero rescaled cut separation. Multiplication back by \(e^{2dn}\) prevents this from transferring a finite negative covariance to every late recurrence.

If no extremal zero exists, then \(F_d=H_d=0\) although the unscaled field still has growth rate \(d\). Finite-phase recurrence at the supremum has no nonzero leading profile in that case. The [short-window filter theorem](FIXED_WINDOW_ZERO_ISOLATION.md) detects each *individual* positive displacement in either case. The outstanding independent sign bound concerns the genuine unscaled arithmetic field.
