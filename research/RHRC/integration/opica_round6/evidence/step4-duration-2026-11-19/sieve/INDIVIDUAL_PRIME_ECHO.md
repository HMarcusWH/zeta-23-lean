# The signed contribution of each new prime on the squarefree graph

**DERIVED on paper, 19 November 2026. Step 4 remains OPEN.** Consider the actual integer drive \(U\) and its complete finite Euler filter over all primes below \(p\). When \(p\) grows, the filtered drive and its translate by \(\log p\) have correlation tending to \(-1\). Translation by \(2\log p\) gives correlation tending to \(+1\). The limiting correlation for translation by \(\lambda\log p\) is \(\cos(\pi\lambda)\). This identifies the contribution at each successive prime to the squarefree grouping, strengthening the previous aggregate sign for growing cutoffs. The negative recurrence required on whole native windows at the fixed cutoff remains an arithmetic question.

## Exact arithmetic edges

Use the one-copy native \(j=(D^2-1/4)^2q_{1/4096}\). Let \(S_mf(t)=m^{-1/2}f(t-\log m)\), \(U=\sum_{k\ge2}(\log k)S_k j\), and \(P=\sum_{k\ge2}\Lambda(k)S_kj\). Each has causal support. For a finite prime set \(B\), write \(M_B=\prod_{q\in B}q\), \(V_B=\prod_{q\in B}(1-S_q)U\) and
\[
 E_B(t)=\sum_{(r,M_B)=1}\frac{\mu^2(r)}r V_B(t-\log r)^2,\qquad
 L_B=\frac{1}{\zeta(2)}\prod_{q\in B}(1+1/q)^{-1}\|V_B\|_2^2 .
\]
The genuine Möbius expansion of \(P\) is recovered by summing the signed core components \({\bf1}_{(r,M_B)=1}\mu(r)S_r V_B\). For a prime \(m\notin B\), pair each squarefree \(r\) coprime to \(mM_B\) with \(mr\). The squared terms cancel on subtraction, giving the pointwise edge
\[
 E_{B\cup\{m\}}-E_B
 =-\frac2{\sqrt m}\sum_{(r,mM_B)=1}\frac{\mu^2(r)}r
 V_B(t-\log r)V_B(t-\log r-\log m).
 \tag{1}
\]
The corresponding fixed-mask translation limit is exact:
\[
 \frac{L_{B\cup\{m\}}}{L_B}
 =1-\frac{2\sqrt m}{m+1}
 \frac{\int V_B(t)V_B(t-\log m)\,dt}{\int V_B(t)^2\,dt}.
 \tag{2}
\]
This follows directly from \(V_{B\cup\{m\}}=(1-S_m)V_B\) and the squarefree density factor. [Möbius grouping and source](../../step4-correlation-2026-11-19/divisor/ROUGH_CORE_PHASE_TRANSITION.md)

## The narrow pair of frequencies

Set \(B=B_p=\{q:q<p\}\), with \(p\to\infty\) through primes. Fix \(0\le\sigma<1/2\), \(u=1/2+\sigma\), \(h=1-u>0\), \(\ell=\log p\). Write \(v(t)=e^{-\sigma t}V_{B_p}(t)\) and \(d\nu=|\widehat v(\tau)|^2d\tau/(2\pi\|v\|_2^2)\). Put \(A=\sum_{q<p}q^{-u}\sim p^h/(h\ell)\). For every fixed \(\epsilon>0\), except on a set of \(\nu\)-measure at most \(\exp(-c_{\epsilon,h}A/\ell^2)\) for sufficiently large \(p\),
\[
 \min_{\pm}\left|\ell^2\left(\tau\mp\frac{\pi}{\ell}\right)
                 \mp\frac{\pi}{h}\right|<\epsilon,
 \tag{3}
\]
where the two signs in each expression are taken together. The profile is real, so \(\nu\) is even and each frequency band receives asymptotic mass \(1/2\).

**Height control.** Uniformly for \(|\tau|\le p^2\),
\[
 \frac1A\sum_{q<p}q^{-u-i\tau}
 =\frac{h}{h-i\tau}e^{-i\tau\ell}+o(1).
 \tag{4}
\]
For detail use the already inspected fixed zero-free ceiling \(\theta<1\) and choose any \(\alpha\) with \(\theta<\alpha<1\). For \(\sqrt p\le x\le p\), truncated Perron at height \(H=p^{12}\) applied to \(-\zeta'(s+i\tau)/\zeta(s+i\tau)\) gives
\[
 \sum_{k\le x}\Lambda(k)k^{-i\tau}
 =\frac{x^{1-i\tau}}{1-i\tau}+O_\alpha(x^\alpha\ell^3).
\]
Use \(x'=\lfloor x\rfloor+1/2\), with the same sum and main-term difference at most one by differentiation. Starting at \(1+1/\log x'\), terms outside \([x'/2,2x']\) cost \(O(x'\log^2 x'/H)\) by absolute summation. The remaining error is \(O(x'\log^2 x'/H)\) by the half-integer spacing and \(|\Lambda(k)|\le\log k\). Shift the integral to \(\alpha\), crossing the pole at \(1-i\tau\). On the fixed vertical line and both horizontals the logarithmic derivative is \(O_\alpha(\log^2(2+H+p^2))\). Indeed the local logarithmic-derivative formula at height \(t\) has \(O(\log(2+|t|))\) zeros within unit height, all at horizontal distance at least \(\alpha-\theta\). The simple pole at 1 is separated on the integration segments. The vertical integral costs \(O(x^\alpha \ell^3)\), and the horizontals \(O(x\ell^2/H)\). To pass to (4), discard the range below \(\sqrt p\) at \(O_u(p^{h/2})\), using absolute values. Remove prime powers of exponent at least two and perform partial summation on the remaining range with weight \(x^{-u}/\log x\). Their weighted contribution is \(O(\log^2 p)\) by summing over bases and exponents. The error from the Perron estimate is \(O_{u,\alpha}((1+p^{\max(\alpha-u,0)})\ell^4)\). The resulting main integral \(\int_{\sqrt p}^p x^{-u-i\tau}dx/\log x\) is \(p^{h-i\tau}/[(h-i\tau)\ell]+O_u(p^h/\ell^2+p^{h/2})\), uniformly by integration by parts. Changing either prime endpoint costs \(O(1)\). This proves (4). [External fixed ceiling](https://github.com/GTimG/QuasiRiemannTracker/blob/42cf5415cfaa4205caaa25ab11160724606cdc33/submissions/2026-11-13-continuum-exact-contact/src/Candidate/Main.lean) · [Perron and local logarithmic derivative](https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/)

The same estimate (4) follows from the classical Vinogradov–Korobov region independently of the external fixed ceiling. With \(X=p\) (or the real endpoint \(X=p^k\) in the companion theorem), set \(H=X^{12}\), \(Q=H+X^2+4\), \(\delta=[120(\log Q)^{2/3}(\log\log Q)^{1/3}]^{-1}\). Ford's Theorem 5 and compact low-height nonvanishing on the line \(\Re s=1\) imply that all zeros up to height \(Q\) have real part at most \(1-2\delta\), for \(X\) large. Shift the Perron contour above to \(1-\delta\). On the vertical side both neighboring zeros and the pole at 1 are at distance at least \(\delta\). On the horizontal sides the zeros have this horizontal separation and the pole has vertical distance at least \(H-X^2\). The local logarithmic derivative therefore costs \(O(\log Q/\delta)=O(\log^2 X)\). The previous error is now \(O(x^{1-\delta}\log^3 X)\) uniformly for \(\sqrt X\le x\le X\); relative to \(x\) this is \(O_D((\log X)^{-D})\) for every fixed \(D\). Real-weight partial summation gives (4) as before with \(o(1)\) normalized error. Thus both the prime echo and the all-mask optimum require no fixed power saving for the ordinary prime number theorem. [Ford, Theorem 5](https://arxiv.org/pdf/1910.08205#page=3) · [Tao, local zero count and logarithmic derivative](https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/)

Define the loss \(D(\tau)=\sum_{q<p}q^{-u}(1+\cos(\tau\log q))\). The finite filter satisfies
\[
 \log\left|\prod_{q<p}(1-q^{-u-i\tau})\right|
 = A-D(\tau)+O_u(\log p).
 \tag{5}
\]
This follows from the absolutely convergent expansion of each Euler logarithm beyond its linear term and \(\sum_{q<p}q^{-2u}\le\sum_{m\le p}1/m\). The error is \(o(A/\ell^2)\). The genuine source has \(\widehat U(\sigma+i\tau)=-J(\sigma+i\tau)\zeta'(u+i\tau)\), where \(J\) has the native single-sinc decay and cancels the pole of \(\zeta'\) in its entire continuation. In particular at large height \(|\widehat U(\sigma+i\tau)|\ll_{\sigma,j}\exp(-c_{\sigma,j}\sqrt{|\tau|})\), allowing for a polynomial factor by shrinking \(c_{\sigma,j}>0\). This follows from the Gevrey-2 derivative bound for \(e^{-\sigma t}j(t)\) and the polynomial vertical growth of \(\zeta'\). Thus beyond \(p^2\) the \(\widehat v\)-mass costs \(O(\exp(2A+O(\ell)-c p))\). Here \(p\gg A\). Equation (4) implies a fixed positive gap \(D\ge c_\delta A\) at \(|\tau|\ge\delta\) up to \(p^2\), since \(|h/(h-i\tau)|<1\) there. For \(|\tau|\) sufficiently small it also gives a gap if the distance of \(\tau\ell\) from the odd multiples of \(\pi\) exceeds a fixed \(\delta>0\). [Native source regularity](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/CCM/UniversalSincInverseGevreyBounds.lean)

**Separating the first two peaks.** Choose an odd multiple \(s\) of \(\pi\) nearest \(\tau\ell\), and write \(\beta=\tau\ell-s\). Give \(x_q=\log(p/q)\) mass \(q^{-u}/A\). Its first four moments tend respectively to \(j!/h^j\), \(1\le j\le4\). Partial summation by PNT proves this: on fixed intervals of \(x_q\) the limiting density is \(h e^{-h x}\), and the tail beyond \(K\) up to \(x\le\ell/2\) is bounded by \(C_h\sum_{k\ge K}(1+k)^4 e^{-hk}\) using the PNT upper for prime counts. The remaining \(q<\sqrt p\) costs \(O(\ell^5 p^{-h/2})\). Write \(\bar x=\mathbb E x_q\to1/h\) and \(s_x^2=\operatorname{Var}(x_q)\to1/h^2\). Taylor's inequality for \(1-\cos z\), with global remainder at most \(|z|^4/24\), gives
\[
 \frac{D(\tau)}A=
 \tfrac12\big[(\beta-\tau\bar x)^2+\tau^2s_x^2\big]
 +O_h((|\beta|+|\tau|)^4).
 \tag{6}
\]
For \(|\beta|,|\tau|\) sufficiently small, this is bounded below by \(c_h(\beta^2+\tau^2)\). The preceding fixed-gap bounds handle the complement of that neighborhood.

At \(\tau_*=\pi/(\ell-\bar x)\) the first square vanishes. Throughout \(|\tau-\tau_*|\le\ell^{-3}\), equation (6) gives \(D/A=(\pi^2/(2h^2)+o(1))/\ell^2\). Since the nonzero entire \(\widehat U\) has at most a finite-order zero at \(\sigma\), this whole band has \(|\widehat U(\sigma+i\tau)|\ge c\ell^{-m}\) for some fixed \(m\). Its width and source weight cost \(O(\log\ell)=o(A/\ell^2)\) in the log normalization. Equations (5) and (6) therefore give a lower bound \(\exp(2A-(\pi^2/h^2+o(1))A/\ell^2)\) for \(2\pi\|v\|_2^2\).

For \(D/A\) within \((\pi^2/(2h^2)+1)/\ell^2\), the fixed gaps and local quadratic lower already give \(\ell|\tau|+\ell|\beta|\ll_h1\) below height \(p^2\). Only finitely many \(s\) remain. Along any subsequence inside that range with \(s\) fixed and \(\ell\beta\to b\), necessarily \(\ell\tau\to s\) and
\[
 \ell^2D/A\longrightarrow\tfrac12[(b-s/h)^2+s^2/h^2].
\]
The unique minimizers over such \(s,b\) have \(s=\pm\pi\), \(b=s/h\). Compactness gives a strictly positive additional gap in this last display outside (3), for every \(\epsilon>0\). Integrate (5) there with the fixed finite total \(\int|\widehat U(\sigma+i\tau)|^2d\tau\) and divide by the normalization lower. Add the discarded high tail. This proves (3), including the exponential exceptional measure.

## Consequences for time and arithmetic

For any \(m=m(p)>0\) with \(\log m/\log p\to\lambda\in\mathbb R\), the overlap of the normalized filtered drive obeys
\[
 C_{p,\sigma}(m)=
 \frac{\int v(t)v(t-\log m)\,dt}{\int v^2}
 =\int\cos(\tau\log m)d\nu(\tau)\longrightarrow\cos(\pi\lambda).
 \tag{7}
\]
This includes the individually resolved first loss
\[
 \ell^2(1+C_{p,\sigma}(p))\longrightarrow \frac{\pi^2}{2h^2}.
 \tag{8}
\]
Indeed \(\ell\beta\to\pm\pi/h\) on (3) with arbitrary prescribed error, and the exceptional mass is \(o(\ell^{-2})\). The bounded integrand \(1-\cos\beta\) gives uniform integrability after multiplication by \(\ell^2\).

At \(\sigma=0\), (2) and (8) yield for each sufficiently large successive prime
\[
 L_{B_p\cup\{p\}}-L_{B_p}
 =\frac{2\sqrt p}{p+1}L_{B_p}
 \left(1-\frac{2\pi^2+o(1)}{(\log p)^2}\right)>0 .
 \tag{9}
\]
For each fixed \(0<\kappa<1\) this statement also holds with \(E_{B_p\cup\{p\}}(t)-E_{B_p}(t)\) on the left, retaining \(L_{B_p}\) on the right, uniformly along all \(p,n\to\infty\) with \(p\le\kappa^2n^2/4\), \(n-2\log n\le t\le n\). Indeed the [squarefree sampling proof](../../step4-correlation-2026-11-19/divisor/FIXED_SIEVE_RECURRENCE_AUDIT.md) gives absolute error \(O(e^{-c n})\) for cutoffs \(\le n\). For \(n<Z\le\kappa^2 n^2/4\) the proof gives absolute error \(O(e^{-c_\kappa n})\) on the low-\(v\) part and relative tail \(O(n^C\exp[-c_\kappa\sqrt Z/\log Z])\). Both are \(o(L_{B_p}p^{-1/2}\ell^{-2})\) in absolute size for \(Z=p,p-1\) (the relative bound is multiplied by its own \(L_Z\)). In this range \(Z>n\), and \(L_Z\sim L_{B_p}\) for the two choices by (2). This also proves the result for any positive terminal average, with total weight included. In particular every separate edge changes the energy with the same positive sign across these complete windows. No effective threshold in \(p\) is asserted by (8) or (9).

Equation (7) also makes a different, testable sign prediction for an isolated insertion into the **same** base mask \(B_p\). Choose primes \(m\sim p^2\); such choices exist by PNT. Then (2) gives \(L_{B_p\cup\{m\}}-L_{B_p}=-(2+o(1))L_{B_p}/\sqrt m\). Intermediate primes have not been inserted in this mask. Its sign differs from a sequential insertion at the full prefix ending just below \(m\). The continuum profile (7) applies uniformly when \(\lambda=\log m/\log p\) ranges over any fixed compact set, by subsequence compactness. It likewise determines the Gram matrix of any fixed finite family of these translated profiles: normalized entry \(i,j\) tends to \(\cos(\pi(\lambda_i-\lambda_j))\), which has rank at most two. All these statements concern the genuine finite-filter histories.

## A whole block of negative graph contributions at every late native window

Use zero tilt and take the first \(\lfloor p^{3/2}/\ell^4\rfloor\) primes in \([p^2,2p^2]\) as the set \(S\). PNT ensures availability. Let \(b=\sum_{m\in S}m^{-1/2}\asymp\sqrt p/\ell^4\), so \(b\to\infty\) and \(b=o(A/\ell^2)\). Then the full simultaneous regrouping, including every mixed product among these primes, satisfies
\[
 \log\frac{L_{B_p\cup S}}{L_{B_p}}=-(2+o(1))b,\qquad
 L_{B_p\cup S}-L_{B_p}=-(1-o(1))L_{B_p}.
 \tag{10}
\]
Indeed the squared-norm ratio is the expectation under the original \(\nu\) of \(\prod_{m\in S}|1-m^{-1/2-i\tau}|^2\). On the good bands (3), \(\cos(\tau\log m)=1+o(1)\) uniformly over \(S\), because \(\log m=2\ell+O(1)\). Its log is thus \(-(2+o(1))b\), since \(\sum_{m\in S}m^{-1}=o(b)\). The bad bands contribute at most \(\exp((2+o(1))b-cA/\ell^2)=o(e^{-3b})\). The log density ratio is \(O(\sum_{m\in S}m^{-1})=o(b)\).

Fix \(0<a<2\) and take \(p\) the first prime at or above \(n^a\) for each integer \(n\); hence \(p\sim n^a\). Equation (10) holds with \(L\) replaced by **both actual grouped energies** \(E(t)\), uniformly on the full terminal window. For completeness the effective squarefree sampling proof extends to \(B_p\cup S\) as follows. All sieving primes are \(\le 2p^2\ll n^{2a}\), so the Bonferroni proof with \(K\sim\eta n/\log n\) gives discrepancy \(O(xe^{-\eta n/2}+\sqrt{x}\exp(C_a\eta n))\) for any sufficiently small fixed \(\eta>0\). This argument uses an upper bound on the number of sieving primes and the sum of their reciprocal densities, both bounded by those for the full prefix up to \(2p^2\). On \(v=t-\log r\le n/2\), the relative discrepancy costs \(\exp(-c_a n)\); the squared variation of the filter costs at most \(\exp(O(A+b))=\exp(o(n))\) by translation Minkowski applied to \(U,U'\). For the tail choose small fixed \(\delta>0\) such that \(a(1/2+2\delta)<1\). The log absolute Euler product with weights \(q^{-1/2+\delta}\) costs \(O(p^{1/2+\delta}+b p^{2\delta})=o(n)\). The tilted \(U,U'\) bounds therefore give \(|V(v)|\ll\exp(-\delta v+o(n))\) throughout the tail, and the total active discrete harmonic mass is \(O(n)\). Both cutoffs have absolute sampling error \(O(e^{-c n})\). Their translation limits grow as \(\exp((2+o(1))A)\) by (5), (10) and \(b=o(A)\); their density factors cost \(O(\log n)\). Thus
\[
 E_{B_p\cup S}(t)-E_{B_p}(t)=-(1-o(1))E_{B_p}(t)
\]
at **each** node and also under the normalized positive native window average. The energy remaining after this negative block still grows as \(\exp((2+o(1))A)\); the cancellation is large relative to the base but has not reached the fixed original floor. The block was selected using only the prime cutoff and precedes observation of \(P\).

[Exact algebra and Euler-band diagnostic](check_individual_prime.py) · [Finite results](INDIVIDUAL_PRIME_CHECK.json). The replay verifies 55 regrouping identities using integer-valued test histories. It also samples the actual undamped Euler product in the first and third positive resonance bands through \(p=10{,}000{,}019\). There its sampled first-band peak has log modulus \(401.62\), versus \(251.20\) in the third, with \(\cos(\tau\log p)=-0.9151\) and \(\cos(2\tau\log p)=+0.6747\) at the former. These samples concern the Euler factors alone. Equations (3) and (10) use the full source-weighted integral.

For fixed original cutoff \(Y\), the successive additions through \(Z\le\kappa^2n^2/4\) reconstruct the entire ordered contribution from pairs that acquire a common rough core between the two cutoffs. Equations (1) and (9) show individually positive contributions from every successive sufficiently large prime, in the stated late-time regime. To obtain a negative full native window at \(Y=10^7\), the signed interaction of pairs whose rough cores remain different at \(Z\) must overcome these gains. The sign of an isolated skipped-prime insertion cannot be transferred to that complete remaining interaction. No independent cofinal upper for this last sector follows here.

Optimizing over all choices of additional prime layers gives a sharper result in the [companion all-mask theorem](OPTIMAL_PRIME_MASKS.md). It computes the best possible remaining grouped energy at each fixed polynomial prime range and constructs masks attaining it.
