# The native squarefree optimum up to a stretched-exponential prime cutoff

**DERIVED on paper, 19 November 2026.** Fix \(0<a<2\). Take the first prime \(p\ge n^a\), let \(\ell=\log p\), \(A=\sum_{q<p}q^{-1/2}\sim2\sqrt p/\ell\), and set \(Y=e^s\). Assume \(s/\ell\to\infty\) and \(s\le c\sqrt{n\ell/A}\) for a sufficiently small absolute \(c>0\). This includes \(s=n^\beta\) for every \(0<\beta\le(1-a/2)/2\), and reaches \(s\asymp n^{1/2-a/4}\log n\) with a sufficiently small leading constant. Allow **every** prime mask \(M\) containing the prefix \(B_p=\{q:q<p\}\) and otherwise using primes up to \(Y\). For the genuine one-copy source and \(n-2\log n\le t\le n\),
\[
 \frac1A\min_{B_p\subseteq M\subseteq\{q\le Y\}}\log E_M(t)\ \longrightarrow\ 1
 \quad\text{uniformly in }t.                                    \tag{1}
\]
The same minimum rate holds for the normalized positive native observation average, with a common mask across all nodes. This extends the [bounded-degree design theorem](OPTIMAL_PRIME_MASKS.md) from polynomial ranges to \(Y=\exp(n^\beta)\), whose allowed logarithmic ratios grow as \(K=s/\ell\). Both the masks and their full signed residual between distinct rough cores use the original divisor equation.

For the upper choose any fixed integer \(k\), use its already constructed mask up to \(p^k\), and apply its native limit \(\sec(\pi/(k+2))\). Eventually \(p^k\le Y\). Now increase \(k\) to infinity. This proves the upper uniformly, including for a single chosen mask on an entire window. The all-finite-mask [translation limit theorem](UNRESTRICTED_TRANSLATION_LIMIT.md) supplies the independent lower \(\log L_M\ge(1-o(1))A\). Its all-mask uniformity is needed because \(K\) now grows. To carry this lower to the native time window, handle small and large total Euler mass separately.

## Squarefree sampling on the retained interval

Let \(N_M(x)\) count squarefree \(r\le x\) coprime to the mask, and \(c_M=\zeta(2)^{-1}\prod_{q\in M}(1+1/q)^{-1}\). For \(v=t-\log r\in[0,n/2]\), \(x=e^{t-v}\ge e^{n/2}/n^2\). Uniformly over all masks,
\[
 \left|N_M(x)/x-c_M\right|
 \le \exp(-c_a (n/s)\log n).
 \tag{2}
\]
Indeed apply the [squarefree-multiple count and Bonferroni sandwich](../../step4-correlation-2026-11-19/divisor/FIXED_SIEVE_RECURRENCE_AUDIT.md) at consecutive even and odd orders \(D\sim\kappa n/s\), with \(\kappa>0\) sufficiently small and fixed. The normalized finite-count errors together cost at most \(3(D+1)(2Y)^D/\sqrt{x}\le e^{-c n}\). The factorial tail is at most \(e^B B^{D}/D!\) up to the immaterial shift by one, where \(B=\sum_{q\le Y}1/(q+1)=O(\log n)\): take \(z=1+1/\log Y\) and use \(\sum_{q\le Y}1/q\le e\log\zeta(z)\). Since \(D\gg\sqrt n\) and \(s/\log n\to\infty\), Stirling and the finite-count bound give (2). Also \(\log c_M=O(\log n)\).

Set \(H_\sigma=\sum_{q\in M}q^{-1/2-\sigma}\), \(H_* =n/(8es)\). For any \(0\le\sigma\le1/2\) with \(H_\sigma\le H_*\), let \(W(v)=e^{-\sigma v}V_M(v)\). Causality gives \(W(v)=0\) for \(v<0\). Translation Minkowski gives \(\|W\|_2+\|W'\|_2\le C_j e^{H_\sigma}\), uniformly since the corresponding weighted drive norms are bounded on this compact tilt range. Thus the integrated variation and the endpoint cost for sampling \(W^2\) below \(n/2\) are \(O_j(e^{2H_*})\). Stieltjes partial summation with (2) gives absolute error \(\le\exp(-c'_a (n/s)\log n)\). Throughout \(v\ge n/2\) one also has
\[
 |W(v)|\le C_j e^{-v/s}\prod_{q\in M}(1+q^{-1/2-\sigma+1/s})
 \le C_j e^{-v/s+eH_*},
 \tag{3}
\]
using the uniform bound for \(e^{-(\sigma-1/s)v}U(v)\) and \(\log q\le s\). The continuous tail and the active discrete tail cost \(O_j((n+s)e^{-n/s+2eH_*})=o(1)\); the latter uses \(\sum_{r\le e^t}1/r=O(n)\). Consequently if \(H_0\le H_*\), taking \(\sigma=0\) gives \(E_M(t)=L_M+o(1)\) uniformly. This proves (1)'s lower for these masks.

## Dense masks force a larger positive observable before the horizon

Suppose \(H_0>H_*\). Choose \(0<\sigma<1/2\) with \(H_\sigma=H_*\); this is possible because \(H_{1/2}=O(\log n)\). For all \(q\ge p\) the ratio \(\lambda_q=\log q/\ell\) lies in \([1,K]\). There is a probability density \(w_K\) supported in a fixed compact interval with uniformly bounded supremum, whose cosine transform satisfies
\[
 \widehat w_K(\lambda)\le-c_0/K\quad(1\le\lambda\le K),\qquad
 \widehat w_K(\lambda)\le0\quad(\lambda\ge1) .                         \tag{4}
\]
Here \(c_0>0\) is independent of \(K\ge1\). To construct it, take a fixed even compact probability density \(w_1\) with \(\widehat w_1(\lambda)\le-c_1/\lambda^2\) on \(\lambda\ge1\). Start from a density proportional to \(|x|e^{-|x|/2}\) and smoothly cut off its tails at sufficiently large fixed radius: the transform error is \(O(e^{-R/4}/\lambda^2)\) by two integrations by parts, and the uncut transform is \(\le-3/(25\lambda^2)\). Next take a fixed smooth compact nonnegative convolution \(r=\chi*\widetilde\chi\) of integral one whose transform \(T\) is nonnegative and \(\min_{|\lambda|\le1/2}T(\lambda)>0\). One can take \(\chi\) a nonnegative probability bump supported on \([-1/10,1/10]\). Set \(D=\lceil K\rceil\) and form the nonnegative density before normalization
\[
 b_K=w_1+\epsilon r(x)\left(1-\frac1D\sum_{j=1}^D\cos(jx)\right).
\]
Since \(\sup_{\lambda\ge1}\lambda^2T(\lambda)<\infty\), choose a fixed small \(\epsilon>0\) so that \(\widehat w_1+\epsilon T\le0\) on \(\lambda\ge1\). Every remaining term in \(\widehat b_K\) is nonpositive. On \([1,K]\) one integer \(j\in[1,D]\) lies within distance \(1/2\), so its translated \(T(\lambda-j)\) supplies a strict \(-c/D\). The normalization lies between 1 and \(1+2\epsilon\). This proves (4).

On averaging \(-\sum_{q\in M}q^{-1/2-\sigma}\cos(\lambda_q x)\) against this density, the primes at least \(p\) give \(\ge c_0(H_*-A)/K\), while the entire prefix can cost at most \(A\). Here \(H_*/K=n\ell/(8e s^2)\ge A/(8e c^2)\). By choosing the absolute constant \(c\) in the stated prime-size range sufficiently small, the averaged negative cosine sum is at least \(4A\). Some \(x\) on the fixed compact support attains that value. The derivative costs at most \(KH_*\), so an interval of length \(\gg A/(KH_*)\) has gain at least \(3A\).

The weighted Euler log has uniform linearization error \(O(\sum_{q\le Y}q^{-1})=O(\log n)\). Hence on the corresponding frequency interval in \(\tau=x/\ell\) it is at least \((3-o(1))A\). These intervals lie in one compact height range and have lengths \(\ge n^{-C}\). The entire, nonzero genuine \(\widehat U\) costs at most a fixed polynomial in \(n\) in its integrated lower, uniformly throughout \(0\le\sigma\le1/2\). In detail, factor off the finitely many zeros on a larger compact rectangle. For a frequency interval of length \(l\le1\), remove portions of total length \(l/2\) around their projected ordinates. On the remainder every zero factor has modulus \(\gg_j l\), and the nonvanishing factor has a positive compact minimum. Plancherel therefore gives \(\int_0^\infty W^2\ge\exp((6-o(1))A)\). Its tail beyond \(n/2\) is negligible by (3). Applying the sampling result to the earlier interval and using \(V_M^2\ge W^2\) there proves \(\log E_M(t)\ge(6-o(1))A\). Thus the dense masks do strictly worse than the optimal construction, and (1) follows.

## Consequence for genuine signed pairs

At the arbitrarily late common instants \(t_j\) where \(P(t_j)\to0\), every mask considered above has complete distinct-core covariance \(P(t_j)^2-E_M(t_j)=-E_M(t_j)+o(1)\), simultaneously and with absolute error independent of the mask. In particular this cancellation survives every regrouping up to prime size \(\exp(n^\beta)\) in (1), even when the mask is selected after the observation. Given any fixed \(\beta<1/2\), one can take a sufficiently small fixed \(a>0\) to obtain this conclusion. The growing floor prices signed pairs at near-zero instants. The missing fixed-cutoff statement concerns arbitrarily late *whole windows* of the required duration. These quantifiers still differ.
