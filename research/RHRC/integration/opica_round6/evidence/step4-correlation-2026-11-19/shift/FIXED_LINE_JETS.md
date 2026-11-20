# A fixed-line test for the complete square

**19 November 2026. Paper deductions.** The cofinal fixed-sieve sign has an equivalent formulation on the single line of absolute Dirichlet convergence \(\Re s=3/2\). With the actual one-copy source and its complete prime-power coefficients, 115,001 consecutive normalized derivative norms on this line are less than \(10^{63}\). For 65,001 orders the complete signed difference from the prescribed diagonal is less than \(-10^{70}\). An upper at unbounded orders remains **OPEN**. These are analytic deductions over the full infinite time integral, with rational checks on the finite endpoints. They are not evaluations on a frequency mesh or new Lean results.

Use the exact fields, shifts, \(Y=10^7\), and displacement \(d\) of the [fixed-sieve note](../FIXED_SIEVE_SIGN.md). In particular \(P=\sum_m\Lambda(m)m^{-1/2}j(\cdot-\log m)\), with the one-copy even source \(j\) and \(J(z)=\int j(v)e^{-zv}dv\). \(P\), the integer drive and \(V_Y\) vanish on negative times. For \(k=0,1,\ldots\) put
\[
 d\mu_k(t)=\frac{2^{2k+1}}{(2k)!}t^{2k}e^{-2t}dt,\qquad
 A_k=\int_0^\infty P(t)^2d\mu_k(t),\quad D_k=\int_0^\infty E_Y(t)d\mu_k(t).
\]
Each measure has total mass one. The objects compared below are formed from the same field. Every signed ordered cross term contributes to \(A_k-D_k\).

## Exact fixed-line formulas

Taking the Laplace transform in the region of absolute convergence, differentiating there, and applying Plancherel to \(t^ke^{-t}P(t)\) gives
\[
 A_k=\frac{2^{2k+1}}{(2k)!\,2\pi}\int_{\mathbb R}
 \left|\left.\partial_z^k\!\left[-J(z)\frac{\zeta'(1/2+z)}{\zeta(1/2+z)}\right]\right|_{z=1+i\tau}\right|^2\,d\tau . \tag{1}
\]
Every fixed order of the absolute prime-power Dirichlet series converges on this line, including every term produced by differentiation of \(J\). Elementary counting and compact support give \(|P(t)|\ll_j(1+t)e^{t/2}\), paying integrability for each fixed order. The vertical integral uses all real frequencies. For the diagonal, Tonelli and time translation give, with \(r\) restricted to \((r,\Pi_Y)=1\),
\[
 D_k=\frac{2^{2k+1}}{(2k)!}\sum_r\frac{\mu(r)^2}{r^3}
     \int_0^\infty (u+\log r)^{2k}e^{-2u}V_Y(u)^2du . \tag{2}
\]
The absolutely convergent binomial moments here have the genuine squarefree rough weights. \(E_Y\) is bounded and tends to \(L_Y>10^{73}\), so \(D_k\to L_Y\) since the gamma probabilities leave every fixed compact interval. [Fixed-sieve density, energy, constants and source links](../FIXED_SIEVE_SIGN.md)

## What an unbounded set of orders would prove

For the actual field one has
\[
 \lim_{k\to\infty}\frac{\log(1+A_k)}{2k}=-\log(1-d). \tag{3}
\]
The absolutely summable native explicit formula gives \(|P(t)|\le C_j e^{dt}\) globally, using a finite bound on the initial interval. Thus \(A_k\le C_j^2(1-d)^{-(2k+1)}\). If \(d=0\) this already gives the rate. If \(d>0\), set \(T_k= k/(1-d)\). On \([T_k-2\log T_k,T_k]\), the unnormalized gamma weight is at least \(T_k^{2k}e^{-2T_k-O(\log k)}\). The logarithm of the full native field energy on that interval is \((2d+o(1))T_k\) by the terminal-window theorem. Multiplying the two and using \(\log((2k)!)=2k\log(2k)-2k+O(\log k)\) gives the matching lower in (3). The same proof uses integer \(\lfloor T_k\rfloor\) if desired. [Native fixed-source window theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeWindowRate.lean#L1154)

Under \(d=0\) the conditional global bound \(|P|<10^{31}\) gives \(A_k<10^{62}\). If \(d>0\), (3) shows \(A_k\to\infty\). Therefore either of **\(A_k\le10^{63}\) for unbounded integers \(k\)** or **\(A_k-D_k\le0\) for unbounded integers \(k\)** is equivalent to the cofinal native sign and to \(d=0\). A cofinal argument with a bounded vertical frequency range, on real values of \(\zeta'/\zeta\) only, or with an upper of the form \(e^{ck}\) for one fixed \(c>0\) does not supply either premise.

## Finite bounds with every prime and every time retained

Separating the verified low ordinates from the genuinely unverified high ordinates in the fixed-sieve certificate gives the unconditional, all-time inequality
\[
 |P(t)|\le 10^{31}+e^{-53890+bt}\quad(t\ge0),\qquad b<0.374.
\]
Here all critical-line and trivial-zero contributions fit in the first term for \(t\ge1\). The rough count already covers the finite initial interval. The second term uses published finite zero verification, the single sinc-product tail, and the external uniform displacement ceiling. Applying Minkowski in \(L^2(\mu_k)\) yields
\[
 \sqrt{A_k}\le 10^{31}+e^{-53890}(1-b)^{-k-1/2}.
\]
Since \(e^{0.4685}>500/313\) and \(0.4685(115000+1/2)<53890\), this proves \(A_k<(10^{31}+1)^2<10^{63}\) for every integer \(0\le k\le115000\). The rational certificate below uses a partial exponential series with positive terms. [Upstream high-ordinate and source estimates](../FIXED_SIEVE_SIGN.md) · [Scalar certificate](FIXED_LINE_JET_CHECK.json)

The [all-horizon diagonal lower bound](../ALL_HORIZON_DIAGONAL.md) also gives \(D_k> 10^{72}/24\) for every integer \(k\ge50000\). Here are the constants. The density \(f_k\) of \(\mu_k\) has mode \(k\), mean \(k+1/2\), and variance \((2k+1)/4\). By Chebyshev's inequality the interval within \(\sqrt{2k+1}\) of the mean, of length at most \(3\sqrt{k}\), carries at least \(3/4\) of the mass. Thus \(f_k(k)\ge1/(4\sqrt{k})\). For \(v\in[0,\sqrt{k}]\), \(\log(1+x)\ge x-x^2/2\) gives \(f_k(k+v)/f_k(k)\ge e^{-v^2/k}\ge e^{-1}>1/3\). Put \(m=\lceil2\log(2k)\rceil\). For \(k\ge50000\), \(m\le\sqrt{k}/4\) and \(m\le(6/5)2\log k\). These follow from \(m\le2\log(2k)+1\), the two inequalities at 50000, and their increasing slack. The native windows ending at \(k+hm\), \(1\le h\le\lfloor\sqrt{k}/m\rfloor\), lie disjointly in \([k,k+\sqrt{k}]\). Their combined length is at least \((\sqrt{k}/m-1)2\log k\ge(5/8)\sqrt{k}\). Each exceeds \(10^{72}\) in mean diagonal energy by the parent bound. Multiplying by the density minimum gives \(D_k\ge(5/96)10^{72}>10^{72}/24\).

Consequently \(A_k-D_k<-10^{70}\) for **every order from 50,000 to 115,000 inclusive**. This supplies 65,001 consecutive complete signed comparisons. The calculation does not extrapolate in \(k\). [Reproducible endpoint checks](check_fixed_line_jets.py)

A contrary signed derivative observation at any integer \(k\ge50000\) would force a specific rightward zero in a finite range of ordinates, despite the unbounded time and frequency integrals in (1). Indeed \(A_k\ge D_k\) would give \(\sqrt{A_k}>10^{35}\). Apply Minkowski to each native zero separately. A zero with displacement \(\delta_\rho\) costs at most its absolute source weight times \((1-\delta_\rho)^{-k-1/2}\). This application may use the explicit formula on \(t\ge1\) only; on \(t<1\) use the independently bounded initial field, and reserve \(2\cdot10^{31}\) in total for the initial, critical and trivial terms. In each unverified bin \(m=\lfloor\sqrt{|\Im\rho|}\rfloor\) the sum of the absolute source weights is at most \(3000(m+2)^{15}e^{-m/32}\). If every rightward zero missed the following strict inequality, each whole bin, including leftward terms whose gamma cost is at most one, would contribute at most \(10^{34}(m+2)^{-2}\). The sum plus the reserved terms is below \(10^{35}\), a contradiction. Thus one and the same zero must satisfy
\[
 (k+1/2)\log\frac1{1-\delta_\rho}
 >m/32-17\log(m+2)+\log(10^{34}/3000)>\sqrt{|\Im\rho|}/33 .
\]
The second inequality follows at \(m\ge1732050\) from \(m/1056-17\log(m+2)-1/33>0\) with increasing left side. The external ceiling and the already checked \(-\log(1-0.374)<0.4685\) now imply \(3\cdot10^{12}<|\Im\rho|<(16k)^2\). This gives a finite-height consequence of a hypothetical measured failure; no such failure was observed. [Native bin bounds and parallel terminal-time localization](../COUNTERSIGN_ZERO_HEIGHT.md)

## Why a Landau argument stops at the real singularity

For \(d>0\) write \(a_\gamma=-m_\rho J(\rho-1/2)\) on the rightmost attained line \(\Re\rho=1/2+d\), and \(H(t)=\sum_\gamma a_\gamma e^{i\gamma t}\), with an empty sum if the supremum is unattained. Absolute summability in the native explicit formula and dominated convergence give \(e^{-dt}P(t)=H(t)+o(1)\). This includes every nonmaximal term, irrespective of how close its real part is to the supremum. For the real nonnegative transform \(F(z)=\int_0^\infty e^{-zt}P(t)^2dt\), the terminal bounds prove its abscissa is \(2d\). Landau's theorem makes this a positive real singularity. Equivalently, analyticity there would permit the positive Taylor coefficients of \(F(x-h)\) at a nearby \(x>2d\) to integrate the exponential at an abscissa below \(2d\), contradicting the terminal lower. Subtracting the diagonal cannot remove the singularity because \(E_Y\) is bounded. In fact
\[
 \lim_{\epsilon\downarrow0}\epsilon\int_0^\infty e^{-(2d+\epsilon)t}
 (P(t)^2-E_Y(t))dt=\sum_\gamma |a_\gamma|^2 . \tag{4}
\]
Abel averaging of the absolutely convergent square of \(H\) retains equal frequencies. A rightward zero and its conjugate therefore contribute at a *real* exponent even when \(\zeta\) has no positive real zero in the critical strip. An unattained supremum can have zero limit in (4) while still giving a genuine singularity. In the same way gamma averaging gives \((1-d)^{2k+1}A_k\to\sum_\gamma |a_\gamma|^2\), using the shape-\((2k+1)\) gamma measure with rate \(2(1-d)\). The coarse exponential rate and the limiting multiplier answer different questions.

Trying to bound (1) by termwise absolute values has an arithmetic cost that can be evaluated. Replacing \(j\) by \(|j|\) makes the actual complete positive prime-power field asymptotic to \(c_j e^{t/2}\), where \(c_j=\int e^{-v/2}|j(v)|dv>0\), by PNT and partial summation over the fixed compact support. Its exact normalized moments grow as \(c_j^2 2^{2k+1}\). The exponential persists although the Dirichlet series is absolutely convergent at every order being tested. Absolute convergence on the fixed line or positivity of a rough diagonal consequently does not prove the required signed cancellation at unbounded orders. The fixed source and the native theorem turn such an independent proof into Step 4; the present derivation establishes the finite range and the obstruction only.
