# A finite spectral comparison for the same signed ordinary-prime sum

Fix the slowly modulated probe \(\tau_n=1/\log(n+3)\), the positive taper and the ordinary-prime sum \(M_n\) of the [localization](POISSON_PRIME_RANGE.md). The estimates there, including the removal of all higher powers inside the taper, hold for this prescribed modulation as well. The following paper comparison is unconditional given the merged source results and the published finite zero verification.

Let \(\mathcal A_n\) consist of distinct nontrivial zeros \(\rho=1/2+\delta+i\gamma\) with
\[
 \delta>0,\qquad 256n\delta>(|\gamma|-1)^2\sqrt{|\gamma|}.
\]
These sets are finite and contain only ordinates above \(3\cdot10^{12}\) in absolute value. From the elementary strip \(\delta<1/2\) and \((|\gamma|-1)^2\ge|\gamma|^2/2\) in this range, \(|\gamma|<(256n)^{2/5}\). Put \(p=\rho-1/2\), \(a_p=-m_\rho J(p)\), \(r_p(\tau)=(-1-p+i\tau)/(1-p+i\tau)\) and define the finite, complex sum
\[
 F_n=\sum_{\rho\in\mathcal A_n}
       \frac{\sqrt2\,a_p}{1-p+i\tau_n}r_p(\tau_n)^n .
\]
For every fixed \(\epsilon>0\),
\[
 \{n: |M_n-F_n|<\epsilon\}\quad\hbox{has positive lower density}.
\]

To check this comparison, contributions with \(\delta<0\) individually tend to zero by weak convergence of the probe since their exponentials belong to \(L^2(0,\infty)\). The uniform stable-mode Fejér bound and \(\sum |a_p|<\infty\) allow dominated convergence even if the displacements approach zero. The compact initial history and trivial-zero correction are also in \(L^2\). The entire higher-power aggregate inside the taper and the two deleted ordinary-prime ranges cost \(o(1)\). All rightward modes may be replaced by their untruncated rational multipliers with total error \(O_j(e^{-cn})\) using the positive margin computed in the localization.

For a rightward mode outside \(\mathcal A_n\) the absolute value of the multiplier is at most \(2\sqrt2 \exp(\sqrt{|\gamma|}/128)\). This uses \(\log|r_p|\le2\delta/(|\gamma|-1)^2\). The native bin-weight estimate \(3000(k+2)^{15}e^{-k/32}\) for \(k=\lfloor\sqrt{|\gamma|}\rfloor\) makes the enlarged weights summable. Each fixed rightward zero eventually leaves this omitted set. Its whole omitted contribution consequently tends to zero, regardless of the distribution of such zeros. What remains in \(M_n-F_n\) is the actual critical-line component plus \(o(1)\). The [phase recurrence](jets/UNSHIFTED_COFINAL_GRAPH.md) gives the density conclusion.

This rules out the unactivated high-ordinate tail, leftward zeros and stable source corrections as independent obstructions on those returns. Bounding \(F_n\) by assuming the active set empty would assume the desired exclusion. A direct signed arithmetic estimate on \(M_n\), or on the remaining primitive graph, is still needed. [Finite-height theorem](https://arxiv.org/abs/2004.09765) · [Native envelope and bin estimates](../step4-correlation-2026-11-19/FIXED_SIEVE_SIGN.md)
