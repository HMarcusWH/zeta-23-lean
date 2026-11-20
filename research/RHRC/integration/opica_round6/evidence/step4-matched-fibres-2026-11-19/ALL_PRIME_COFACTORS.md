# Paying every prime cofactor in both observations of the actual prime area

19 November 2026. **DERIVED on paper. Step 4 OPEN.** In each of the two disjoint outer-prime sums for the centered ordinary-prime area, every nonzero label with a prime cofactor can be grouped with positive labels whose cofactors are products of two or three distinct primes. The signed mass of the resulting group is between zero and \(2x\log x\). In most of the outer-prime range this holds at every prefix of the range simultaneously. The choice uses only actual finite prime and divisor data. It leaves a specific composite/composite signed estimate open.

## Same source, same horizon

Write \(F(x)=\int_2^x(\vartheta(u)-u)\,du+\tfrac23x^{3/2}\). Use the factorial and eta observations with \(L_i=\lfloor x^{\lambda_i}\rfloor\), \((\lambda_1,\lambda_2)=(.11,.37)\). An outer prime \(q\) has upper endpoint \(x/(L_i+1)\). The lower endpoints are \(x^{3/4}/(L_1\log^2(2L_1))\) and \(x^{.025}\), respectively. Write \(U_1=.36,\ U_2=.975\). The possible values of \(\log(x/q)/\log x\) range between \(\lambda_i+o(1)\) and \(U_i+o(1)\). The two observations each reconstruct \(F\) at the same real \(x\) to \(o(x^{3/2})\). The fixed-power factorial representation uses the project's [pinned external ceiling](https://github.com/GTimG/QuasiRiemannTracker/blob/42cf5415cfaa4205caaa25ab11160724606cdc33/submissions/2026-11-13-continuum-exact-contact/src/Candidate/Main.lean). The combinatorial payment below uses ordinary PNT.

For each filter average its existing four moment solutions over \(2L<R\le3L\) with \(9\mid R\). There are \(L/9+O(1)\) centres. Every matrix estimate in the earlier distributed construction is uniform for \(R\asymp L\). Each position \(4^kR\) has bounded multiplicity, so \(m|a_m^{\rm correction}|=O(\log^2(2L))\) after averaging. The real moment equations, all source terms, the original disjoint outer intervals and both reconstruction precisions persist. The same averaging proves the absolute label majorants of the earlier distributed construction. [Factorial source](../step4-area-runs-2026-11-19/OLD_PRIME_LOCALIZATION.md) · [Eta source](../step4-area-runs-2026-11-19/ETA_FILTERED_PRIME_LOCALIZATION.md) · [Distributed bounds](../step4-area-runs-2026-11-19/BOTH_ROW_ENERGIES.md)

The exact label weight in \(S_i\) is \(g_i(q,j)=(x-qj)(\log q)r_i(j)\) for \(j\le x/q\). Both filters vanish through \(L_i\), including \(j=1\) in the residual. On every squarefree \(j>1\), each divisor has underlying coefficient 1 and inverse coefficient \(\mu\) in both filters. Every correction position is divisible by 9. Consequently the actual coefficient is
\[
 r_i(j)=-\sum_{d\mid j,\ d\le L_i}\mu(d).
\]
For a prime \(j>L_i\) this equals \(-1\). On a product of two distinct primes exceeding \(L_i\) **in product**, it is \(+1\) if both factors are at most \(L_i\). On a product of three distinct primes \(j>L_i\) it equals the number of single factors at most \(L_i\), minus 1, minus the number of two-factor divisors at most \(L_i\). All positive candidates have coefficient at most 2. An outer prime may divide its own cofactor. Different labels representing the same product remain separate throughout.

## Measure the entire negative sector

Let \(M_i\) be the absolute mass of all prime-cofactor labels in observation \(i\). Put \(Y=x/q,\ L=L_i\). Uniformly over eligible \(q\), ordinary PNT with partial summation gives
\[
 \sum_{j\le Y,\ j\ {\rm prime}}(x-qj)=(1+o(1))\,\frac{xY}{2\log Y}.
\]
The contribution being subtracted for primes \(j\le L\) is at most \(x\pi(L)\vartheta(x/L)=O(x^2/\log L)\) after summing outer weights. Applying partial summation once more to \(\sum_q(\log q)/(q\log(x/q))\), whose entire support stays in fixed polynomial ranges, gives
\[
 M_i=\left[\tfrac12\log(U_i/\lambda_i)+o(1)\right]x^2.
\]
Thus the positive subtotal with a prime cofactor on **both** sides of the covariance is \(M_1M_2\sim \frac14\log(.36/.11)\log(.975/.37)x^4\). [Ordinary prime number theorem](https://dlmf.nist.gov/27.12.E5)

## A uniform lower sum from positive composite labels

For \(Y\ge100L\), set \(\alpha=\log L/\log Y\). For both outer intervals, \(0.30\le\alpha<1\) for all sufficiently large \(x\), since \(.11/.36>.30\) and \(.37/.975>.30\). We count actual squarefree cofactors in \(.01Y<j\le .99Y\), hence \(j>L\). Write \(K=400\). Place \(\alpha\) in a closed bin \([h/K,(h+2)/K]\) with \(h=120,122,\ldots,398\). Use distinct increasing prime factors and half-open log cells \((i/K,(i+1)/K]\) for their exponents relative to \(Y\).

* For two factors the smaller is in cell \(i\ge4\). Keep \(2i+3<K,\ \max(i+1,K-i)\le h\). These inequalities guarantee increasing factors and coefficient \(+1\). The last factor is counted by PNT between \(.01Y/p\) and \(.99Y/p\).
* For three factors put the first two in cells \(i,k\) with \(4\le i<k<(K-i-4)\mathbin{//}2\), where the last bound uses integer division. The upper exponents in units of \(1/K\) for all single factors are \(i+1,k+1,K-i-k\). Lower bounds for the three pair exponents are \(i+k,K-k-2,K-i-2\). Indeed writing \(t=j/Y\) gives \(\log t/\log Y>-1/K\) uniformly for large \(x\). These margins enforce distinct increasing factors. Count the singles with upper bound at most \(h\); subtract 1 and subtract the number of pairs whose lower bound is at most \(h+2\). A positive result \(w\) is a lower bound on the **actual** coefficient for every label in that cell.

For fixed first factor(s), the last prime ranges over \(tZ\), \(.01<t\le.99\), for \(Z=Y/\prod p\) bounded below by a fixed positive power of \(Y\). Its weighted sum is \(xZ(\int_{.01}^{.99}(1-t)dt+o(1))/\log Z\), uniformly on every retained cell. The reciprocal prime mass in cell \(i\) tends to \(\log((i+1)/i)\ge1/(i+1)\). Bounding \(\log Z\) from above gives the dimensionless lower contributions
\[
 \frac{K}{(i+1)(K-i)},\qquad
 \frac{wK}{(i+1)(k+1)(K-i-k)}
\]
for two and three factors, respectively. Each is multiplied by \(xY\int_{.01}^{.99}(1-t)dt/\log Y\) before the common outer \(\log q\). Unique ordered factorization makes the cells disjoint. There are finitely many, so the remainders are uniform in the outer prime and the bin, including both bin boundaries.

Rounding **each** positive rational down to billionths before addition, the minimum sum over all 140 bins is 1.088335060, attained on \([.300,.305]\). In particular the lower bound \(1.08\) holds without relying on the last digits. Since \(2\int_{.01}^{.99}(1-t)\,dt=.98\), the supply exceeds \(1.05\,xY/(2\log Y)\) for all sufficiently large \(x\), uniformly when \(Y\ge100L\). This comparison also upper-bounds the target prime mass using the PNT estimate above, with room in the constant. [Exact integer calculation](check_full_prime_cofactor_supply.py) · [Results for all bins](FULL_PRIME_COFACTOR_SUPPLY.json)

## Pay in each outer fibre up to a fixed terminal interval

Fix \(B=2^{256}\), independent of every horizon. Order outer primes increasingly. For each with \(Y\ge BL\), first charge *all* its negative prime-cofactor labels. If the cumulative signed balance is negative, add positive two- or three-prime labels from the same outer prime, in increasing cofactor order, stopping at the first nonnegative balance. The available supply exceeds the current prime mass. By induction every completed outer-prime prefix in this range has a balance in \([0,2x\log x]\). This works even when a previous balance already exceeds the next prime mass.

Treat the one remaining interval \(L<Y<BL\) as a single group. For clarity, the contribution \((\log q)xY/(2\log Y)\) summed over \(aL<Y<bL\) is asymptotic to \(x^2\log(b/a)/(2\log L)\) for fixed \(1\le a<b\). This follows by ordinary PNT on the fixed-ratio outer interval and \(\log Y=\log L+O_B(1)\). The true endpoint \(Y>L+1\) changes the equivalent by lower order. All terminal negative prime mass is therefore at most \((\log B+o(1))x^2/(2\log L)\). Terminal positive supply using only \(100L\le Y<BL\) is at least \((1.05\log(B/100)+o(1))x^2/(2\log L)\). The strict inequality \(1.05\log(B/100)>\log B\) gives a surplus. Charge all terminal prime labels, then select positive labels exclusively in \(100L\le Y<BL\) using the same stopping rule and lexicographic order. Endpoints with zero ramp have no effect. This proves the claimed full bound. No prime or composite label has moved to another observation.

The earlier prefix bound gives a coupled echo. On the prefix range \(Y\ge BL\), weighting the complete matched group by \(q^{it}\) costs \(O(x\log x(1+|t|\log x))\) uniformly on every interval of outer primes there, by summation by parts. Constants do not grow with the number of fibres. The construction makes no analogous prefix assertion inside its terminal group.

## Why full resolution at the endpoint would fail

There is an explicit counterexample to a proposed uniform small bound for every outer-prime interval. On the factorial side choose \(x=(\ell-1)^{100/11}\) for any sufficiently large prime \(\ell\), so \(L_1=\ell-1\). In the last cell \(x/(\ell+1)<q<x/\ell\) the **only** nonzero cofactor is \(\ell\), with weight \(-1\). Its actual mass is
\[
 -\sum_{x/(\ell+1)<q<x/\ell}(x-\ell q)\log q
 =-(1+o(1))\frac{x^2}{2\ell(\ell+1)^2}.
\]
Indeed the continuum is the triangle of height \(\ell h\) and width \(h=x/[\ell(\ell+1)]\). Integrating the pinned prime discrepancy \(\vartheta(u)-u=O(u^{.874})\) against the ramp gives error \(O(\ell h(x/\ell)^{.874})\), which is \(o(\ell h^2)\) since \(0.89\cdot.874<.78\). Changing an endpoint convention costs at most one label, also lower order. The last cell therefore has magnitude asymptotic to \(x^{1.67}/2\), above the target for a single observation. Replacing \(\ell\) by \(2p\) for growing odd primes \(p\) gives the opposite sign with the same equivalent, since both prime factors lie below \(L_1=2p-1\). These are cofinal choices of real horizons, with signs on different sequences. They demonstrate on the true arithmetic why a cross-fibre compensation at the endpoint is necessary for this matching.

## Remaining signed rows

Let \(D_i\) be the signed sum of all the matched labels and \(T_i\) the original sum of **all** remaining labels. Every remaining nonzero cofactor is composite, square factors and exceptional calibration positions included. We proved \(0\le D_i\le2x\log x,\ S_i=D_i+T_i\). The complete labelwise absolute row bounds give \(|S_i|+|T_i|\le x^{2+o(1)}\), hence
\[
 |S_1S_2-T_1T_2|\le x^{3+o(1)},\qquad T_i=F+o(x^{3/2}).
\]
The difference is exactly the union of cross pairs that have at least one matched label. This is a signed estimate for their total, including mixed pairs with the complement. Using the external estimate \(F=O(x^{1+r})\), \(r=.873346\), even gives \(O(x^{2+r}\log x)\) for this difference via \(D_1 S_2+D_2 S_1-D_1 D_2\). On a subset of labels the same absolute majorants pay all pairs with either \(|n-m|\le H\) or \({\rm lcm}(n,m)\le xH\), for \(H=\exp(\sqrt{\log x})\) and products \(n=qj,\ m=q'j'\). The proofs sum absolute divisor and prime-label weights before grouping equal products. Thus their application survives this selection. A different signed bound proved with a separate calibration requires its own intersection argument. [Original covariance and transfer](../step4-area-runs-2026-11-19/SHARED_PRODUCT_COVARIANCE.md)

For any remaining squarefree composite \(j\) and *each* prime factor \(\ell\mid j\),
\[
 r_i(j)=-\sum_{\substack{d\mid j/\ell\\L_i/\ell<d\le L_i}}\mu(d).
\]
This follows by pairing divisors \(d,\ell d\). A nonzero surviving squarefree label therefore has an actual divisor in this interval for every choice of \(\ell\). Repeated-prime cofactors and the calibration corrections still appear in the full sum.

There is a falsification test *after* the matching. In observation \(i\) take outer primes \(.75x/L_i\le q\le.76x/L_i\). In the first take cofactors \(j=2p\) with \(1.08L_1\le j\le1.10L_1\); in the second take \(j'=2p'\) with \(1.20L_2\le j'\le1.22L_2\). All labels survive because \(Y<2L_i\) and their coefficients are \(+1\). The two products are separated by at least \(.064x\). The four variable odd primes belong to disjoint exponent ranges, so the products have gcd 2 and least common multiple of order \(x^2\). The two positive sums on these rectangles each have size comparable to \(x^2/\log L_i\), by ordinary PNT and the positive lower ramp bound. Their product is positive of order \(x^4/(\log x)^2\). Replace only the second cofactor by \(6p'\) in the same product interval. It has coefficient \(-1\) since all its proper divisors are at most \(L_2\), and the analogous negative subtotal has the same order. Both families have least cofactor prime 2 on both sides and product gcd exactly 2. Splitting by these arithmetic data still requires cancellation *within* a single class.

**OPEN.** On arbitrarily late complete windows \([X,X\log X]\), prove a one-sided \(x^{3+o(1)}\) upper for the signed sum over the remaining composite/composite labels with **both** large separation and large least common multiple, uniformly in \(x\) in the window. The matched groups and already-paid rows would then give \(S_1S_2\le x^{3+o(1)}\). The two simultaneous reconstructions give \(|F|\le x^{3/2+o(1)}\) there, contradicting the earlier genuine-source isolation lower under any off-line zero. Even with the new matching, the available external upper for that remaining signed total is only \(O(x^{3.746692})\). No new Lean closing theorem has been produced.
