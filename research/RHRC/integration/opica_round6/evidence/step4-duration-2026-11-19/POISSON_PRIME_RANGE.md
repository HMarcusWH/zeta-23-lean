# The signed prime test can be localized to log primes below 2.33 × 10⁻²⁵ times the order

**Paper result.** A positive, explicitly specified weight confines the unresolved ordinary primes in the [single-coefficient criterion](jets/SINGLE_SCALAR_CAYLEY.md) to
\[
 2^{-20}n^{1/5}<\log p\le 2.33\cdot10^{-25}n+2 .
\]
Every discarded contribution, including all proper prime powers, has an independent bounded total error as \(n\to\infty\). This is a statement about a prescribed smooth partition of the **whole** actual input. A hard cut of the original, unweighted summands need not have the same cancellation. No estimate for the remaining signed sum at unbounded orders has been proved here.

## A finite first-prime quantity

Use \(s=1/4096\), the unchanged \(j\), \(\tau_n=(n+1)^{-1/3}\), and \(\ell_n(t)=\sqrt2e^{-t}L_n(2t)\) from the companion. Write
\[
 \lambda=10^6,\quad m=\max(1,\lceil 2.27\cdot10^{-19}n\rceil),
 \quad k=\lceil m/100\rceil,\qquad
 Q_l(x)=e^{-x}\sum_{i=0}^{l-1}x^i/i!,\quad
 W_n(t)=k^{-1}\sum_{l=m+1}^{m+k}Q_l(\lambda t).
\]
For \(n\ge1\) the weights are in \([0,1]\) on the positive half-line. With \(T_n=2.33\cdot10^{-25}n+2\), form
\[
 M_n=\sum_{2^{-20}n^{1/5}<\log p\le T_n}
 \frac{\log p}{\sqrt p}\int_0^\infty
 \ell_n(t)e^{-i\tau_n t}W_n(t)j(t-\log p)\,dt .
\]
Only ordinary primes appear in this finite sum. All constants and cutoffs are chosen before the order or any hypothetical zero. We prove \(b_n=M_n+O_j(1)\) for the genuine full prime-power coefficient of the companion. If there is a rightward zero, \(b_{n+1}/b_n\) tends to a nonreal constant of modulus greater than one, and \(|b_n|\) grows exponentially at all large orders. Under RH \(b_n\) is bounded. Consequently the following *adjacent arithmetic comparison* is equivalent to Step 4:
\[
 \frac{1+|M_{n+1}|}{n+1}\le\frac{1+|M_n|}{n}
 \quad\text{for arbitrarily large integers }n .
\]
Boundedness gives infinitely many such reversals because the positive normalized sequence tends to zero. In the opposite case the bounded error leaves the limiting ratio greater than one. This proof only gives the implication once the independent reversals are established.

The [stable-mode calculation](jets/POISSON_STABLE_MODES.md) gives a stronger target for this same finite sum. Every proper prime power together costs \(o(1)\) inside the retained weight. Under RH the low critical modes also tend to zero there, and the total remaining native weight gives \(\limsup |M_n|<e^{-50000}\). With a rightward zero the bounded difference from \(b_n\) gives exponential growth. Hence a proof from the ordinary primes that \(|M_n|\le1\) at arbitrarily large orders would suffice. The small upper under RH is a conditional implication only.

## The discarded smooth part at every order

The exact native formula writes \(P=\sum_p a_p e^{pt}+B\) on \([0,\infty)\), where here \(p=\delta+i\gamma\) denotes a shifted zero, \(\sum|a_p|<\infty\), and \(B\in L^2\) includes the genuine finite initial history and trivial terms. The prime index in \(M_n\) has a different meaning. For a single exponential the damped integral is
\[
 T_p(z)=\int_0^\infty \ell_n(t)e^{(p-i\tau_n-z)t}dt
 =\frac{\sqrt2}{1+z+i\tau_n-p}
      \left(\frac{z+i\tau_n-p-1}{z+i\tau_n-p+1}\right)^n .
\]
Multiplication by \(Q_l(\lambda t)\) takes the first \(l\) coefficients of \(f(w)=T_p(\lambda(1-w))\) and sums them at \(w=1\). The statement follows by differentiating where the integral converges. Values outside that region in the estimates below are values of the displayed rational function.

*Non-growing modes.* If \(\delta\le0\), then \(|f(w)|\le\sqrt2\) on \(|w|\le1\). Indeed \(\Re(\lambda(1-w)+i\tau_n-p)\ge0\) and the Cayley quotient has modulus at most one. The average of the partial sums of lengths \(m+1,\ldots,m+k\) at 1 is the difference of two Fejér means with coefficients \((m+k)/k\) and \(m/k\). Each mean has modulus at most \(\sqrt2\), by its nonnegative kernel of total mass one. The retained multiplier is at most \(201\sqrt2\); the discarded multiplier costs at most \(202\sqrt2\). This uniformity includes the frequencies at the edge of the smooth partition. The \(B\) term costs at most \(\|B\|_2\) since \(\|\ell_n\|_2=1\).

*Rightward modes.* Published finite verification implies \(|\gamma|>H=3\cdot10^{12}\), and the external zero-free ceiling gives \(\delta<0.374\). Take the Taylor circle \(|w|=q=1.01\). The rational function has no pole in this disk. There \(z=\lambda(1-w)\) gives \(\delta-\Re z\le0.374+10000\) and \(|\Im z+\tau_n-\gamma|\ge H-1010001\). Thus
\[
 \log\left|\frac{z+i\tau_n-p-1}{z+i\tau_n-p+1}\right|
 \le g=\frac{2(10000+0.374)}{(H-1010001)^2}.
\]
By Cauchy's estimate the absolute Taylor tail at 1 after \(l\) coefficients is bounded by
\[
 \frac{\sqrt2}{H-1010001}\frac{q}{q-1}
                 \exp(gn-l\log q).
\]
Since \(2.27\cdot10^{-19}\log q-g>0\), all these tails are exponentially small in \(n\), uniformly over the whole unverified right half-strip. Sum using the actual absolute source weights. This pays \(\int \ell_n e^{-i\tau_n t}(1-W_n)P\) on the complete field at every order. [Platt–Trudgian](https://arxiv.org/abs/2004.09765) · [External all-moduli theorem](https://github.com/GTimG/QuasiRiemannTracker/blob/42cf5415cfaa4205caaa25ab11160724606cdc33/submissions/2026-11-13-continuum-exact-contact/src/Candidate/Main.lean#L274-L290) · [Native source and explicit formula](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeExplicitFormula.lean)

The same highpass estimate works using only the elementary critical strip and the finite verified height. Replacing \(0.374\) by \(1/2\) in \(g\) still leaves \(2.27\cdot10^{-19}\log(1.01)-g>3\cdot10^{-23}\). Thus the ordinary-prime reduction and its cofinal criterion do not require the external improvement of the zero-free half-plane. The separate quoted finite sensitivity bounds use their stated inputs. [Directed check](LOCALIZATION_CONSTANTS.json) · [Finite-height theorem](https://arxiv.org/abs/2004.09765)

## Restore the arithmetic outside the finite sum

1. For \(x=\lambda t\ge1.01(m+k)\), the exponential Markov bound for a Poisson variable gives \(Q_l(x)\le\exp[-x(1-(1+\log1.01)/1.01)]\le e^{-40t}\) for all included \(l\). Integer rounding gives \(T_n-s\ge1.01(m+k)/\lambda\). Therefore all pulses with \(\log p>T_n\) in the retained weight contribute \(o(1)\), even if their absolute values are used. Indeed their sum against \(|j|\) is at most \(C_j(1+t)e^{t/2}\), starts at \(t\ge T_n-s\), and the \(L^2\) norm of this envelope times \(e^{-40t}\) tends to zero. Apply Cauchy–Schwarz with \(\|\ell_n\|_2=1\).
2. On the pulses with \(\log p\le2^{-20}n^{1/5}\), \(\lambda t=o(m)\) for large \(n\). With \(\lambda t\le m/(2e)\), the usual upper Poisson tail gives \(1-W_n(t)\le2^{-m}\) there. The elementary absolute-prime envelope integrated on this range costs only \(\exp(o(n))\); Cauchy–Schwarz again suffices. Thus replacing \(W_n\) by 1 costs \(o(1)\). The unweighted genuine first-prime sum on this small range is \(o(1)\) by integration by parts in the native Laguerre equation in the companion.
3. The full higher-power channel is \(1/32+B_2(t)\), \(B_2\in L^2(0,\infty)\), as proved using the even-power identity and the unconditional prime number theorem. After weighting, its \(B_2\) term costs at most \(\|B_2\|_2\); apply the non-growing-mode Fejér bound to the constant. This pays every proper prime power at unbounded orders. The same full-Poisson partition and every source sign were used before this removal.

For the weaker subexponential upper the lower cut may also be raised to \(n/\log(n+2)\) asymptotically. The additional absolute prime sum costs \(\exp(o(n))\) using \(W_n\le1\), compact source support and \(\|\ell_n\|_2=1\). At practical orders that lower cut can exceed the upper cut; its asymptotic information is meaningful only at sufficiently large \(n\). The fixed bounded-error statement and adjacent-order test above use the \(n^{1/5}\) cut throughout. [Numerical margins](LOCALIZATION_CONSTANTS.json) · [Full single-prime reduction and source derivative bounds](jets/SINGLE_SCALAR_CAYLEY.md)
