# The signed Möbius covariance can be restricted to coprime, localized factors

**Paper deduction, 19 November 2026.** In a slightly damped energy of the actual one-copy prime field, every pair of divisor channels sharing a large prime can be removed at a cost that is a vanishing fraction of the *actual energy*. This holds at every sufficiently large finite horizon. It uses \(\Lambda=\mu*\log\) and complete signed sums over the affected divisors. It leaves one explicit signed sum over squarefree products.

## Exact marked histories

Use the genuine compactly supported source \(j=(D^2-1/4)^2q_s\), \(s=1/4096\). Denote its full prime-power and integer drives by \(P,U\) respectively. Both vanish at negative times. For integers \(k\ge1\) write \(S_k f(t)=k^{-1/2} f(t-\log k)\) with that history convention. Dirichlet convolution yields
\[
 P=\sum_m\mu(m)S_mU.
\]
This is a locally finite identity in real time. For \(y\ge2\), let \(\Pi_y=\prod_{p\le y}p\), \(V_y=\sum_{a\mid\Pi_y}\mu(a)S_aU\) and \(c_r=\mu(r) S_r V_y\) on \(y\)-rough squarefree \(r\), including 1. Then \(P=\sum_r c_r\). For every \(y\)-rough squarefree \(u\),
\[
 M_u:=\sum_{u\mid r} c_r
 =\mu(u)S_u\prod_{p\mid u}(1-S_p)^{-1}P.                    \tag{1}
\]
Indeed the remaining squarefree divisors of \(m/u\) omit all primes dividing \(u\). The geometric inverses remove exactly those factors from the Möbius convolution. Every expansion is finite on a fixed observing horizon. The right side retains all prime powers in \(P\). [Source history laws](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeSourceFamily.lean) · Previous divisor localization

For \(T>0,\ \sigma>0\), write \(E=\int_0^T e^{-2\sigma t}P(t)^2dt\). Causality gives \(\|S_p f\|_{\sigma,T}\le p^{-1/2-\sigma}\|f\|_{\sigma,T}\). For \(u=\prod_{p\mid u}p\), (1) therefore implies
\[
 \|M_u\|_{\sigma,T}^2
 \le E\prod_{p\mid u}\frac{p^{-1-2\sigma}}{(1-p^{-1/2-\sigma})^2}.
\]
This is a relative estimate. It requires no previously established upper for \(E\).

## Sum over all shared factors

Let \(G\) be the integrated sum of the ordered products \(c_r(t)c_v(t)\) for \((r,v)=1\), with the same damping. Möbius inclusion–exclusion on their common divisor gives
\[
 G=\sum_u\mu(u)\|M_u\|_{\sigma,T}^2,\qquad
 |E-G|\le E\left[\prod_{p>y}\left(1+
  \frac{p^{-1-2\sigma}}{(1-p^{-1/2-\sigma})^2}\right)-1\right].       \tag{2}
\]
The \(u=1\) term is exactly \(E\). Only the majorant uses the infinite product. For \(y\ge4\) its logarithm is at most \(4\sum_{k>y}k^{-1-2\sigma}\le(2/\sigma)y^{-2\sigma}\) for integer \(y\). Set, for late integers \(n\),
\[
 T=n,\qquad y=\lfloor\log\log n\rfloor,\qquad \sigma=(\log y)^{-1/2}.
\]
The bracket in (2) is \(o(1)\), and \(\sigma=o(1)\). This proves \(G=(1+o(1))E\) for all such horizons, with a deterministic error bound independent of the input energy. It removes the **signed total** of all shared-factor pairs. Individual absolute products can be much larger.

## Localize the remaining coprime core

From the integer sampling estimate for the genuine \(U\), for fixed \(A>0\) one can choose \(K=K_{A,j}\) so that for \(0\le t\le n\),
\[
 \sum_{m\le e^t/(Kn^2)} m^{-1/2}|U(t-\log m)|\ll_{A,j}e^{-An}.
\]
Indeed \( |U(\log z)|\le C(1+\log z)\sqrt z\,e^{-c\sqrt z}\) for \(z\ge1\), and the harmonic sum up to \(e^t\) costs at most \(1+n\). If \(r\le e^t/(Kn^2\Pi_y)\) then every \(ra\) with \(a\mid\Pi_y\) is in this paid range. Distinct rough/small-prime factorizations are unique, so the *sum of the absolute values* of all such \(c_r(t)\) is \(O(e^{-An})\). At the other endpoint \(r\le e^{t+s}\) by the causal support. Also \(\sum_r |c_r(t)|\ll_j (1+n)^2e^{n/2}\) on the whole horizon, using the same unique factorization and the elementary envelope of \(U\). Removing every ordered pair touching a paid small \(r\) from \(G\) therefore costs \(O_j(e^{-n})\) after integration, with \(A=3\). This step also works on the coprime subset before summing signs.

Write \(I_t=(e^t/(Kn^2\Pi_y), e^{t+s}]\); the lower endpoint is strict. Since \(\log\Pi_y\le y\log y=o(\log n)\), every retained pair has larger-to-smaller ratio at most \(n^{2+o(1)}\). Coprimality identifies their product \(m\) as squarefree and yields the exact signed coefficient \(\mu(r)\mu(m/r)=\mu(m)\). The resulting scalar is
\[
 G_n^*=\int_0^n e^{-2\sigma t}
 \sum_{\substack{m\ {\rm squarefree}\\(m,\Pi_y)=1}}\frac{\mu(m)}{\sqrt m}
 \sum_{\substack{r\mid m\\r,m/r\in I_t}}
 V_y(t-\log r)\,V_y(t-\log(m/r))\,dt .
\]
It includes both orders of distinct factors, with \(m=1\) counted once when applicable. We have proved
\[
       |G_n^*-E|\le o(1)E+O_j(e^{-n}).                         \tag{3}
\]
No product, shared-factor class, initial history, or proper prime power has been discarded without a signed or absolute restoration bound.

## Attempt at the actual upper

The merged native window theorem gives the displacement \(d\) as the exponential growth rate of the one-copy energy. For the cumulative undamped \(F(n)=\int_0^n P^2\), the same rate follows from the terminal-window lower and summing the native upper on unit subintervals. For late \(n\), \(e^{-2\sigma n}F(n)\le E\le F(n)\), and \(\sigma\to0\). Hence (3) gives
\[
 \lim_{n\to\infty}\frac{\log(1+\max(0,G_n^*))}{2n}=d.
\]
A one-sided independent upper \(G_n^*\le C_\eta e^{\eta n}\) on arbitrarily late common horizons for every \(\eta>0\) is sufficient and necessary for \(d=0\). The transfer has paper status. [Exact native window theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeWindowRate.lean#L1154)

The surviving weights are unitary-divisor correlations of the same integer drive. Taking \(|\mu(m)|\) and counting admissible factor pairs gives an exponential upper. Even the constant small-prime cases still leave pairs of two distinct large primes in the support. Whole-product identities for \(\mu\) do not by themselves bound the signed average against this divisor-dependent kernel. In particular the relative bound for shared factors in (2) cannot be counted a second time as an independent upper for \(G_n^*\). **The residual bound and Step 4 remain OPEN.**
