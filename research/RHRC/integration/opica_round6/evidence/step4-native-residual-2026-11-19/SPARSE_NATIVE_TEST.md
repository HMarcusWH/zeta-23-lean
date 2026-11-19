# A sparse set of native arithmetic observations suffices

19 November 2026. **DERIVED on paper.** The residual Fourier sum left by the native numerator bound can be tested on \(O(L^{1/4}\log^2 L/\log\log L)\) specified integer sites. Each observation still uses every signed coefficient in the remaining sum at that site. The resulting weighted sum of local maxima gives an equivalent critical bound. This supplies a finite arithmetic target suited to further calculation. Its asymptotic upper is open.

## The restriction supplied by the graph

Fix the same rational three-moment distributed Möbius calibration. For \(N=2^jL\), let \(G_N(u)\) be the sum over the unpaid rectangles at this site scale, using signed frequency representatives \(\alpha\in[-1/2,1/2]\), conjugate pairs and \(e^{2\pi i\alpha u}\). At integer \(u\) this extension agrees with the original arithmetic sum. For sufficiently large \(L\) there is no self-conjugate Nyquist term in the unpaid range. \(G_N\) is real on \(\mathbb R\). Every surviving frequency satisfies
\[
 |\alpha|=h_*/q<2K/D<2L^{1/4}/N ,
\]
where the last inequality is exactly the failure of the numerator bound \(D^4L\le N^4K^4\). Also \(\sum_\alpha |A_\alpha|\ll_C L^2\log^3(2L)\). Indeed at each \(q\) the coefficients are \(O(q\log^3(2L)/h_*^2)\); sum over \(h_*\), and then \(q\le CL\). Hence
\[
 \sup_{u\in\mathbb R}|G_N^{(p)}(u)|
 \ll_C L^2\log^3(2L)(4\pi L^{1/4}/N)^p .
\]
No amplitude cancellation or control on other translates is assumed here.

## A deterministic integer sampling rule

Let \(p=\lceil8\log L/\log\log L\rceil\) for all sufficiently large \(L\), and \(W=\lfloor N/L^{1/4}\rfloor\). Intersect each dyadic block \(N<n\le2N\) with the actual residual sites \(L+\lfloor L^{5/6}\rfloor<n\le\lfloor L^{1.01}\rfloor\). Partition the consecutive surviving sites into successive groups of \(W\) sites, with the last group allowed to be shorter. For a group of \(w\) sites starting at \(u\), use all sites if \(w<2p\). Otherwise use the \(p\) sites
\[
 x_i=u+\left\lfloor i(w-1)/(p-1)\right\rfloor,\qquad 0\le i<p.
\]
They include both endpoints and each gap is at least \((w-1)/(2(p-1))\). Denote their largest absolute observation by \(M_w=\max_i |G_N(x_i)|\). Define the fully native statistic \(S_L=\sum_{\rm groups} (w/N^3) M_w\).

For \(w\ge2p\), interpolate the observations by the real polynomial \(P\) of degree \(<p\). The real Lagrange remainder and the derivative bound give
\[
 \sup_{[u,u+w-1]} |G_N-P|
 \ll_C L^2\log^3(2L)(4\pi)^p/p! \le L^{-4}
\]
for all sufficiently large \(L\), since \(p\log p=(8+o(1))\log L\). For each Lagrange basis polynomial \(\ell_i\), bound every numerator factor by \(w-1\). The denominator is at least \([(w-1)/(2(p-1))]^{p-1}i!(p-1-i)!\). Summing over \(i\) and using \((p-1)!\ge[(p-1)/e]^{p-1}\) gives
\[
 \sum_i|\ell_i(x)|\le(4e)^p,\qquad
 \sum_i|\ell_i'(x)|\le(p-1)(4e)^p/(w-1).
\]
The second bound follows by differentiating each product before applying its numerator estimate. Write \(V=p(4e)^p=L^{o(1)}\). The first bound gives \(\sum_{\rm group}|G_N(n)|\le w((4e)^p M_w+L^{-4})\). For the reverse estimate choose a sample attaining \(M_w\). An interval of length \((w-1)/(2V)\) extends from this sample into the group in at least one direction. Throughout that interval \(|P|\ge M_w/2\) by the derivative bound. The interval contains at least \(\max(1,(w-1)/(2V))\) integer sites, counting its integer starting point. If \(M_w\ge4L^{-4}\), these sites have \(|G_N|\ge M_w/4\); otherwise use \(w M_w\le4wL^{-4}\). This yields
\[
 wM_w\ll V\sum_{\rm group}|G_N(n)|+wL^{-4}.
\]
When \(w<2p\), sampling every site gives the two estimates directly with the same subpower loss.

On each group \(n^{-3}\) lies between \(1/(8N^3)\) and \(1/N^3\), and \(\sum_{\rm groups} w/N^3\ll L^{-2}\). In terms of the full residual \(H_L\) from the linked note we have therefore proved
\[
 H_L\ll V S_L+O_C(L^{-6}),\qquad
 S_L\ll V H_L+O_C(L^{-6}).
\]
There are \(O(L^{1/4}+1)\) groups per block and \(O(\log L)\) blocks. The stated count of distinct native sites follows. More generally a single rectangle with \(D\asymp N\asymp L,\ K=1\) needs only \(O(p)\) native samples on this first dyadic block for the same type of comparison: use intervals of length a sufficiently small fixed multiple of \(D/K\) and its frequency upper \(2K/D\).

## The missing arithmetic at these sites

It suffices to bound \(S_L\le L^{-1/2+\epsilon}\) at arbitrarily large integer \(L\), for each \(\epsilon>0\). Both subpower losses are absorbed by first choosing a smaller \(\epsilon\). If \(B>1/2\) this sparse statistic itself has logarithmic exponent \(B-1\) as \(L\) tends to infinity through all integers. This follows from the two-sided inequality and the original residue criterion. Bounds on independent random shifts, values of the full knot that have already cancelled against the paid frequency part, or a finite set of verified cutoffs do not supply the required estimate on these particular signed observations.
## Constant upper loss with a different choice of integer nodes

The same sample count also admits a fixed-constant upper comparison. In each full-size cell take an angular mesh of spacing at most \(1/(28p)\) on \([0,\pi]\), including the endpoints, send each angle \(\theta\) to \(u+(w-1)(1+\cos\theta)/2\), and round to the nearest integer (ties downward). Use the set of distinct rounded nodes. If \(w-1<(200p)^2\), just take all the sites of the cell. Call the corresponding weighted sum of maxima \(S_L^{\rm ang}\).

Use here the degree-\(<p\) Taylor polynomial \(P\) of \(G_N\) at the middle of the cell. The same derivative bound and factorial give uniform error at most \(L^{-4}\), regardless of sampling. Let \(M=\sup|P|\) on the cell. The trigonometric polynomial \(T(\theta)=P(u+(w-1)(1+\cos\theta)/2)\) has degree at most \(p\) and supremum \(M\). A direct derivative estimate is \(|T'|\le7pM\). Indeed \(U(z)=z^pT(\arg z)\) on the unit circle extends as a polynomial of degree at most \(2p\). Inside the unit circle \(|U|\le M\); outside, the reciprocal polynomial gives \(|U|\le M|z|^{2p}\). Cauchy's derivative estimate at \(|z|=1\) on a circle of radius \(1/(2p)\) gives \(|U'|\le2epM\). Differentiating \(e^{-ip\theta}U(e^{i\theta})\) gives the claimed constant.

For \(\theta,\phi\in[0,\pi]\), the cosine difference satisfies \(|\cos\theta-\cos\phi|\ge2(|\theta-\phi|/\pi)^2\), by the product-to-sum formula and the concavity bound for sine. Thus rounding to the nearest integer changes the angular location by at most \(\pi/\sqrt{2(w-1)}\). In a large cell this is at most \(1/(56p)\); the nearest unrounded mesh point is also within \(1/(56p)\). At the rounded sample nearest an angular maximizer, \(|P|\ge3M/4\). The sampled maximum of \(|G_N|\) is consequently at least \(3M/4-L^{-4}\). The full cell sum is at most \(w(M+L^{-4})\).

Conversely, an angular interval of length \(1/(14p)\) extending from a maximizer into \([0,\pi]\) has \(|P|\ge M/2\) everywhere. Its length in the native coordinate is at least \((w-1)/(196\pi^2p^2)\). In a large cell this interval contains \(\gg w/p^2\) integer sites. If \(M\ge4L^{-4}\), those sites all have \(|G_N|\ge M/4\); if \(M<4L^{-4}\), the entire cell is controlled by the error. For cells below the threshold, all their sites are sampled, so the reverse estimate costs at most \(O(p^2)\) there too. After weighting,
\[
 H_L\ll S_L^{\rm ang}+O_C(L^{-6}),\qquad
 S_L^{\rm ang}\ll p^2 H_L+O_C(p^2L^{-6}).
\]
For all sufficiently large \(L\) every full-width cell exceeds the threshold. There is at most one shorter last cell per block, adding \(O(p^2\log L)\) samples in total. All other cells have \(O(p)\) samples, so the total remains \(O(L^{1/4}\log^2 L/\log\log L)\). This proves the same cofinal closure criterion with constant upper loss, using only integer observations of the original signed frequencies. The values of those observations still require an independent arithmetic estimate.

## Reconstructing the weighted mass with additive error

A second option uses the same \(p\) equally spaced integer samples per cell and their full values. In each cell replace \(G_N(n)\) by its Lagrange interpolant \(P(n)\) and sum \(n^{-3}|P(n)|\) over its native sites; in any short cell sampled in full, use the exact values. Call this sum \(I_L\). Since \(||v|-|w||\le |v-w|\), the proved uniform interpolation error gives the absolute guarantee
\[
 |I_L-H_L|\le L^{-4}\sum_{n>L}n^{-3}=O(L^{-6}).
\]
This comparison retains the signs within every observation. It also avoids the multiplicative loss from replacing all values on a cell by their maximum. Under the rational calibration the exact integer observations are real algebraic numbers, since rational-angle roots of unity are algebraic and the denominators \(\sin^2(\pi h/q)\) are nonzero on the selected frequencies. The interpolant thus has real algebraic coefficients. A nonzero \(P\) has at most \(p-1\) real roots, so the polynomial contribution can alternatively be evaluated on constant-sign runs by summing its coefficients against integer powers and, for powers \(-1,-2,-3\), harmonic sums. A zero polynomial contributes zero. Exact algebraic arithmetic at large cutoffs may be expensive; polynomial sample count alone says nothing about that cost. Certified numerical intervals can instead bound the statistic using the same interpolation remainder. In either formulation, proving an independent cofinal critical upper for these samples is the mathematical step still missing.
