# Simultaneous runs of the two signed prime areas from the native window theorem

**DERIVED on paper.** Define \(A_\vartheta(x)=\int_2^x(\vartheta(u)-u)\,du\) and \(A_\pi(x)=\int_2^x(\pi(u)-\operatorname{li}(u))\,du\), using the ordinary primes and the usual principal-value logarithmic integral. Write \(B=\sup_\rho\Re\rho,\ d=B-1/2\). If \(d>0\), fix \(0<\epsilon<1\). Among the integers \(M^{1-\epsilon}\le n\le M\), let \(L_\pm(M)\) be the longest run of consecutive integers on which both \(\pm A_\vartheta(n^4)>0\) and \(\pm A_\pi(n^4)>0\). Then
\[
 \lim_{M\to\infty}\frac{\log(1+L_+(M))}{\log M}
 =\lim_{M\to\infty}\frac{\log(1+L_-(M))}{\log M}=1 .                       \tag{1}
\]
The two runs can be different. The statement holds for every sufficiently late band in the limiting sense (1), even if no zero attains \(B\). Under RH the positive run has length zero by Johnston. Thus a fixed power saving on positive **joint** runs along any unbounded sequence of such bands would close this criterion. Establishing that saving for the actual prime counts is **OPEN**. The proof combines the merged unsigned native terminal-window theorem, an exact change of source, and a separate sign argument.

**Unconditional exclusion of longer gaps.** The second limit in (1) holds in either case. Under RH both areas are negative for every \(x>2\) by Johnston's Theorems 1.1 and 1.2. Under failure of RH, part 4 gives that limit. In particular, if a contiguous positive run starts at \(m\to\infty\) and ends at \(b\), then \(\log b/\log m\to1\): a run reaching \(m^{1+\delta}\) would contain the full tested band ending there for \(\epsilon<\delta/(1+\delta)\), which must contain a simultaneous negative. This rules out gaps of fixed power in the multiplicative horizon and still permits near-linear runs in a single dyad. [Johnston's two unweighted sign criteria](https://arxiv.org/pdf/2201.06184#page=2)

## 1. Passing from the literal source to the unsigned areas

For the prime powers put \(\psi(x)=\sum_{n\le x}\Lambda(n)\) and \(\Pi(x)=\sum_{2\le n\le x}\Lambda(n)/\log n\). Put \(A_\psi=\int_2^x(\psi-u)\), \(A_\Pi=\int_2^x(\Pi-\operatorname{li})\), and \(U_b(t)=e^{-3t/2}A_b(e^t)\). For \(t>\log2\), distributional differentiation gives, with \(D=d/dt\) and \(\mathcal L=(D+3/2)(D+1/2)\),
\[
 \mathcal L U_\psi
 =t\mathcal L U_\Pi
 =\sum_{m\ge2}\frac{\Lambda(m)}{\sqrt m}\delta_{\log m}-e^{t/2}.            \tag{2}
\]
Indeed \(e^{-3t/2}(D^2-D)A_b(e^t)\) differentiates its summatory function once, with the atom at each \(\log m\) carrying \(e^{-t/2}\); differentiating \(\operatorname{li}(e^t)\) supplies \(e^t/t\). After convolution with the actual compact order-zero pulse \(j\) supported on \([-s_0,s_0]\), the last exponential vanishes by \(J(1/2)=0\). The left side therefore equals the actual native field \(P(v)\) for \(v>\log2+s_0\). Moving the two derivatives onto \(j(v-t)\) or \(t\,j(v-t)\) costs respectively a fixed constant or \(O_j(1+v)\) in \(L^1(dt)\). The unconditional proper-prime-power bounds give \(U_\psi-U_\vartheta=O(1)\), \(U_\Pi-U_\pi=O(1)\). It follows that for \(b=\vartheta,\pi\),
\[
 |P(v)|\le C_j(1+v)\big(1+\sup_{|t-v|\le s_0}|U_b(t)|\big).
\]
Every prime power and the continuum are accounted for in (2). [Pinned order-zero source](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeSourceFamily.lean#L19) · [Pinned pole-moment cancellation](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeExplicitFormula.lean#L165) · [Higher-power bounds, Lemma 2.3](https://arxiv.org/pdf/2201.06184#page=3)

With \(d>0\), the merged native theorem at order 0 and \(C=2\) gives \(\int_{T-2\log T}^T |P(v)|^2dv=\exp((2d+o(1))T)\) at every sufficiently large real \(T\). Taking a maximum and using (2), for either area there is \(t=T+O(\log T)\) with \(|U_b(t)|\ge \exp(dT-o(T))\). Define the real normalized area \(F_b(t)=e^{-dt}U_b(t)=e^{-(1+B)t}A_b(e^t)\). The unsigned maximum supplies \(|F_b(t)|\ge e^{-o(T)}\). Squaring alone cannot tell which sign occurs. [Exact native window theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeWindowRate.lean#L1154-L1158)

## 2. The common spectral gap for the actual areas

For either \(b\) one has, for \(t\ge2\),
\[
 F_b(t)=G_b(t)+O(e^{-c t}),\qquad
 G_b(t)=\int e^{(r+i\gamma)t}\,d\mu_b(r,\gamma),                         \tag{3}
\]
where \(c>0,\ -9/8\le r\le0,\ |\gamma|>14\), the measure has finite total variation and \(\int (1+|\gamma|)^{1/2}|d\mu_b|<\infty\). Conjugate modes are paired. The two real functions \(G_b\) are uniformly \(1/2\)-Hölder on \(t\ge0\): each exponential has increment bounded by \(\min(2,(|r|+|\gamma|)|h|)\) on this half-line. This continuity estimate applies to \(G_b\), so no derivative bound on an individual prime-counting jump is used.

For \(\vartheta\), the integrated explicit formula gives masses \(-1/[\rho(1+\rho)]\) at \(r+i\gamma=\rho-B\), repeated with multiplicity. The affine and trivial-zero terms cost \(O(e^{-Bt})\); removing proper powers costs \(O(e^{-dt})\). The usual zero count \(N(H)=O(H\log(2+H))\) proves the claimed summability. [Integrated explicit formula](https://arxiv.org/pdf/2201.06184#page=4) · [Ordinate gap and counting bounds](https://arxiv.org/pdf/2009.13791)

For \(\pi\) the factor \(1/\log n\) must also be paid. Let \(\nu=\sum_{n\ge2}\Lambda(n)\delta_n-{\bf1}_{[2,\infty)}du\) and \(I_w(x)=\int_{[2,x]}(x-u)u^{-w}\,d\nu(u)\). Fix \(s=1/8\). Uniformly on \(0\le w\le s,\ x\ge4\),
\[
 I_w(x)=-\sum_\rho
       \frac{x^{1+\rho-w}}{(\rho-w)(1+\rho-w)}+O(x).                     \tag{4}
\]
Here are the endpoint details. \(I_0=A_\psi(x)+O(x)\) with an affine difference. In the integrated explicit formula, the second derivative of the affine remainder is zero and the twice-differentiated trivial-zero series is \(O(x^{-3})\) for \(x\ge3\). The left side of (4) has distributional second derivative \(x^{-w}I_0''(x)\). The second derivative of its displayed zero sum is \(x^{-w}\) times the second derivative of the corresponding \(w=0\) sum. To see this, truncate to finitely many zeros, differentiate as distributions, and take the limit using local uniform absolute convergence of both undifferentiated sums, uniform in \(w\). Thus the residual in (4) has second derivative \(O(x^{-3})\). Its values at 3 and 4 are uniformly bounded by the convergent ordinate sum and finite arithmetic sums. Integrating the residual's second derivative controls its affine constants uniformly and proves (4).

Use \(1/\log u=\int_0^s u^{-w}\,dw+u^{-s}/\log u\) for \(u\ge2\). The last multiplier \(f(u)=u^{-s}/\log u\) has \(|f^{(j)}(u)|\ll u^{-s-j}\) for \(j=0,1,2\). Twice integrating by parts against \(I_0''=\nu\) gives the tail as \(f(x)I_0(x)+\int_2^x((x-u)f''(u)-2f'(u))I_0(u)\,du\), with the atom at 2 included by extending the primitive as zero below 2. From \(|I_0(u)|\ll u^{1+B}\) it is \(O(x^{1+B-s})\), since \(B>s\). The integral with multiplier \(1/\log u\) differs from \(A_\Pi(x)\) by an affine function due to the continuum's lower endpoint. Removing higher powers then costs \(O(x^{3/2})\). Consequently (3) holds for \(\pi\) with measure obtained by integrating the masses \(-dw/[(\rho-w)(1+\rho-w)]\) at \(r+i\gamma=\rho-B-w\), \(0\le w\le s\), and \(c=\min(s,d)\). This proves the same spectral gap for the two genuine areas even when their large values are smaller than a fixed negative power of \(t\) after normalization.

## 3. Recovering both signs near every unsigned peak

Let \(t_0=T+O(\log T)\) be an unsigned peak from part 1 and put \(v=\min(1,|G_b(t_0)|)>0\). Then \(\log(1/v)=o(T)\). For independent uniform \(V_i\in[-1,1]\), let \(S_N=\sum_{i=1}^N V_i\). Each mode \(z=r+i\gamma\) in (3) satisfies
\[
 |\mathbb E e^{z V_i}|=|\sinh(z)/z|
 \le \cosh(9/8)/14<1/8.
\]
It follows directly that \(|\mathbb E G_b(t_0+S_N)|\le\|\mu_b\|8^{-N}\) when \(N<t_0\). This is a statement about a positive averaging measure on the same area.

Uniform Hölder continuity gives an interval \(|u|\le w=c_0v^2\), \(0<c_0\le1\) fixed, with \(G_b(t_0+u)\) of the same sign as \(G_b(t_0)\) and of magnitude at least \(v/2\). The density of \(S_N\) is symmetric decreasing away from zero and supported on \([-N,N]\), hence \(\Pr(|S_N|\le w)\ge w/N\). Symmetric decrease follows by iterating convolution with the uniform law; the derivative of its next convolution on \(u>0\) is half the difference of the previous density at \(u+1,u-1\). Thus the one-sign contribution to the expectation has magnitude at least \(v w/(2N)\).

Choose \(N=\lceil C(1+\log(1/v)+\log(2+T))\rceil\) for a sufficiently large fixed \(C\). Then \(N=o(T)\) and \(\|\mu_b\|8^{-N}<vw/(4N)\) eventually. The opposite-sign part must have mean magnitude at least \(v w/(4N)\). Some actual point within distance \(N\) of \(t_0\) has that opposite sign with at least this magnitude. Both normalized amplitudes are \(\exp(-o(T))\), so the exponentially small correction in (3) transfers their signs to the real area.

For any fixed \(\epsilon\in(0,1)\) and either sign this shows
\[
 \lim_{T\to\infty}\frac1T
 \log\!\left(1+\max_{(1-\epsilon)T\le t\le T}
             (\pm A_b(e^t))_+\right)=1+B.                              \tag{5}
\]
Indeed seed the argument at \((1-\sigma)T\) for arbitrary fixed \(0<\sigma<\epsilon\). Its two witnesses remain in the band and have logarithmic rate at least \((1+B)(1-\sigma)\). Let \(\sigma\downarrow0\) after taking the liminf. The upper follows from (3). The same two signs have positive intervals of log-time width \(\exp(-o(T))\) around such peaks by Hölder continuity of \(G_b\). Peak times realizing the rate in (5) satisfy \(t=T-o(T)\).

## 4. Putting both signs on the same actual quartic endpoints

The record argument here is necessary because (5) alone allows the signs of the two areas to be misaligned. From the ordinary identities for \(\vartheta,\pi,\operatorname{li}\), two integrations by parts give exactly
\[
 A_\vartheta(x)=\log x\, A_\pi(x)
 -\int_2^x\left(\frac1u+\frac{x}{u^2}\right)A_\pi(u)\,du
 +c_2(x-2),\qquad c_2=\operatorname{li}(2)\log2-2.                    \tag{6}
\]
Indeed \(\vartheta(x)=\pi(x)\log x-\int_2^x\pi(u)/u\,du\). The derivative of \(\operatorname{li}(x)\log x-\int_2^x\operatorname{li}(u)/u\,du-x\) vanishes, giving the stated lower-end constant.

Fix \(1<\alpha<1+B\) and a sign \(\sigma=\pm1\). For each \(X=e^T\) choose a maximum \(x_T\) of \(\sigma A_\pi(x)/x^\alpha\) over \([2,X]\). By (5) its value is at least \(\exp((1+B-\alpha)T-o(T))\). The upper from (3) forces \(\log x_T=T-o(T)\) and \(\sigma A_\pi(x_T)\ge\exp((1+B)T-o(T))\). On \(2\le u\le x_T\), the signed area \(\sigma A_\pi(u)\le \sigma A_\pi(x_T)(u/x_T)^\alpha\). The integral kernel in (6) is positive. Therefore
\[
 \sigma A_\vartheta(x_T)\ \ge\
 \big(\log x_T-1/\alpha-1/(\alpha-1)\big)\sigma A_\pi(x_T)-|c_2|x_T .
\]
This gives both areas the same sign and amplitudes \(\exp((1+B)T-o(T))\) at the same \(x_T\). Using (3) for each, one single left interval of length \(\exp(-o(T))\) in \(\log x\) preserves both signs. Taking a left interval also handles a record attained exactly at \(X\). Put \(X=M^4\). All the consecutive fourth powers in this interval lie between \(M^{4(1-\epsilon)}\) and \(M^4\); there are \(M^{1-o(1)}\) of them because the associated \(n\)-span is bounded below by a constant times \(x_T^{1/4}\exp(-o(T))\). This proves (1).

## 5. If a zero attains the right edge

When \(B>1/2\) is attained, \(F_\vartheta(t)\) differs by \(o(1)\) from
\[
 F_*(t)=-\sum_{\Re\rho=B}\frac{e^{i\gamma t}}{\rho(1+\rho)} .
\]
Dominated convergence handles all the other zeros, even without a gap in their real parts. The right-edge sum is a uniformly convergent almost-periodic real function of mean zero. At each distinct ordinate its nonzero coefficient includes its full multiplicity. Hence it has positive and negative intervals of fixed width and margins, both recurring with bounded gaps. For clarity, finite partial sums have relatively dense uniform almost-periods by compactness of the closure of their phase rotations on a finite torus. The absolute tail upgrades the fixed-accuracy recurrence to the whole sum. Its mean-zero and nonvanishing properties then preclude a one-sign function.

The forward Abel equation from ordinary primes, obtained from (6) or from \(\pi(x)=\vartheta(x)/\log x+\int_2^x\vartheta(u)/(u\log^2u)\,du\), gives
\[
 A_\pi(x)=A_\vartheta(x)/\log x+O(x^{1+B}/\log^2 x).
\]
In detail the remainder is \(O(x)\) plus the integral of \(A_\vartheta(u)\) times \(1/(u\log^2u)+x/(u^2\log^2u)+2(x-u)/(u^2\log^3u)\). Use \(|A_\vartheta(u)|\ll u^{1+B}\), splitting at \(\sqrt x\). Thus \(tF_\pi(t)=F_*(t)+o(1)\), with the same leading function. For some fixed \(K>1,\eta>0\), each sufficiently late interval \(M\le n\le KM\) therefore contains joint-positive and joint-negative runs of at least \(\eta M\) consecutive fourth powers. The constants depend on the actual right-edge spectrum.

This case also gives simultaneous scale tests: for any fixed integer \(J\), one can choose an integer \(q\ge2\), fixed for all horizons, such that the same positive and negative intervals work for every scale \(n,qn,\ldots,q^Jn\). Pick a sufficiently accurate arbitrarily large almost-period \(h\) of \(F_*\), and an integer \(q\) with \(4\log q\) close enough to \(h\), possible because the mesh tends to zero. Uniform continuity and telescoping give \(\sup_t|F_*(t+4j\log q)-F_*(t)|\) below the strict sign margin for \(0\le j\le J\). Prescribing an arbitrary \(q\) instead of making this choice can fail for an oscillatory source.

There is a positive result on the **prescribed powers** \(n,n^2,\ldots,n^J\) in this attained case. For every conjugate pair on the right edge,
\[
 \Re\!\left(-\frac1{\rho(1+\rho)}\right)
 =\frac{\gamma^2-B(1+B)}{|\rho(1+\rho)|^2}>0
\]
because \(|\gamma|>14\). Thus \(F_*(0)>0\) and it has a positive margin on some neighborhood of zero. If \(h\) is a sufficiently accurate almost-period, telescoping from zero shows that all \(F_*(jh)\) retain that positive margin, \(1\le j\le J\). Uniform continuity keeps this true on an interval of fixed positive width about \(h\) for the variable \(t\) in \(F_*(jt)\). Such \(h\) occur with bounded gaps. The two asymptotics for \(F_\vartheta\) and \(tF_\pi\) at \(jt\) transfer positivity to both areas. With \(t=4\log n\), every sufficiently late \([M,K_J M]\) therefore contains at least \(\eta_J M\) consecutive integers \(n\) for which both \(A_\vartheta(n^{4j})\) and \(A_\pi(n^{4j})\) are positive for **every** \(1\le j\le J\). The fixed constants \(K_J>1,\eta_J>0\) depend on \(J\) and the right-edge spectrum. This argument controls joint positivity on the prescribed powers; a mean-zero oscillation alone gives no matching statement about joint negativity on all of them.

**Falsification boundary.** In the general case (1) concerns \(M^{1-\epsilon}\le n\le M\). It supplies neither a fixed fraction of every dyadic interval nor aligned signs on arbitrary preset dilations. A single cosine already illustrates that an energy rate can be identical with either sign, and that a half-period translation reverses the sign. The argument above uses the actual prime-power source in (2), verified native growth, the gap in the actual area spectra, and the ordinary-prime identity (6). A new upper on joint-positive run lengths from the arithmetic remains the missing input. This note is a paper derivation and carries no new Lean or CI authority.
