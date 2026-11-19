# How long the actual negative covariance lasts

Set \(H(t)=P(t)^2-E_Y(t)\) at the single cutoff \(Y=10^7\). The calculation below uses the full signed divisor expansion of \(H\). It gives a distinction between the **frequency** and the **duration** of negative intervals, beyond a finite sign test. All assertions on this page are paper deductions.

If \(d=0\), \(H(t)<-10^{73}\) eventually by the pointwise diagonal and prime-field bounds. Suppose instead \(d>0\). There are constants \(B,c>0\), independent of the observation time, such that every sufficiently late interval \([t-B,t]\) contains a subinterval of length at least \(c e^{-dt}\) on which \(H<-10^{73}\). In particular, recurrent negative signs, even at bounded gaps, are compatible with a rightward zero. [Pointwise diagonal estimate](divisor/FIXED_SIEVE_RECURRENCE_AUDIT.md) · [Actual short-window energy](cuts/FIXED_WINDOW_ZERO_ISOLATION.md)

To prove this, fix \(0<\alpha<d\). For each distinct rightward shifted zero \(p=\rho-1/2\) with \(\Re p\ge\alpha\) and positive ordinate \(\gamma\), put \(h_p=\pi/\gamma\). Ingham's density theorem gives \(N(1/2+\alpha,T)\ll T^\kappa\) for some \(\kappa<1\), so \(L=\sum h_p<\infty\). There are no positive real shifted nontrivial zeros. Multiply the two-point probability measures
\[
 \nu_p=\frac{e^{-h_p\Re p}\delta_0+\delta_{h_p}}{1+e^{-h_p\Re p}}
\]
by convolution. Their product is a probability \(\nu\) supported on \([0,L]\). Its Laplace transform vanishes at every such \(p\) and its conjugate. This uses only the half-turn \(e^{-i\gamma h_p}=-1\). Repeated zeros in the explicit formula multiply the coefficient, so one vanishing factor at that frequency suffices. Convolve \(\nu\) with the uniform probability on \([0,L+2]\) to obtain a density \(g\), supported on \([0,2L+2]\), bounded above by \(1/(L+2)\), and equal to \(1/(L+2)\) throughout \((L,L+2)\). The absolute convergence of the native explicit formula then gives \(|g*P(t)|\ll e^{\alpha t}\). The density may depend on the actual zero configuration. It is used here to deduce oscillation under the hypothetical case \(d>0\).

On the interior unit interval \([t-L-3/2,t-L-1/2]\), the exact short-window energy rate gives \(\int P^2=\exp((2d+o(1))t)\). The independent absolute source-weight bound gives \(\sup|P|\ll e^{dt}\) there. Thus \(\int g(u)|P(t-u)|du\ge\exp((d-o(1))t)\). Subtracting and adding \(g*P(t)\) proves that the integrals of **both** \(P_+\) and \(P_-\) against this positive density are at least \(\exp((d-o(1))t)\). Both signs occur somewhere in \([t-2L-2,t]\). Continuity supplies a real zero there, at every sufficiently late \(t\).

Differentiating the source's absolutely convergent explicit formula once gives \(|P'(v)|\le C_j e^{dv}\) for \(v\ge1\), since \(\sum_\rho(1+|\rho|)|J(\rho-1/2)|<\infty\); the trivial-zero derivative converges uniformly there. Apply the preceding bounded-gap conclusion to the interior of \([t-(2L+4),t]\), leaving a unit of margin at both ends. About the resulting zero of \(P\), an interval of length \(c e^{-dt}\) has \(|P|\le1\), with \(c>0\) chosen from the derivative bound alone. The pointwise diagonal bound \(E_Y>1.1\cdot10^{73}-2\) proves the promised strict covariance inequality on that interval.

At the other extreme, for every fixed \(0<\lambda<2d/[3(1/2-d)]\), all sufficiently late intervals \([t-t^{-\lambda},t]\) have **positive integrated** covariance by the short-window theorem. In particular none can have \(H\le0\) everywhere on it. Conversely, independent arithmetic evidence proving nonpositive integrated covariance at arbitrarily late real horizons of width \(t^{-\lambda}\) would give
\[
 d\le\frac{3\lambda}{4+6\lambda}.
\]
This implication follows by solving the preceding strict condition for \(d\); it claims nothing extra at equality. For example a recurrent width \(1/t\) would give \(d\le 3/10\). Recurrence at width \(1/\log(2+t)\) would give \(d=0\). The proven bounded-gap occurrence at width \(c e^{-dt}\) leaves this duration estimate open. It guarantees no corresponding recurrence at integer centers.

[Native explicit formula](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeExplicitFormula.lean) · [Ingham's density estimate](https://doi.org/10.1093/qmath/os-11.1.201) · [Proof and norm bound for the short-window isolation filter](cuts/FIXED_WINDOW_ZERO_ISOLATION.md)
