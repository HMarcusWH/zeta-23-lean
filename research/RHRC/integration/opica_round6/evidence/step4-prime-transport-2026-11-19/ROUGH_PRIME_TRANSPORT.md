# The same signed obstruction survives fixing every small-prime allocation

**DERIVED on paper · 19 November 2026.** The dyadic-tree criterion still detects the full zero exponent after deleting every label divisible by a prime up to \(y=\lceil\log_2 X\rceil^2\). More generally the proof works for \(y=(\log X)^{2+o(1)}\). The resulting labels have density tending to zero. A single prescribed pattern of small-prime factors of subpower product works as well. These restrictions shrink the arithmetic target. The bound on the remaining signs is open.

## The actual tree and the statement

Write \(B=\sup_\rho\Re\rho\), \(b=B-\tfrac12\). Let \(P=\prod_{5\le p\le y}p\). Choose either \(a=1\), or any squarefree \(a=a(X)\mid P\) with \(\log a=o(\log X)\). Construct the existing dyadic tree at the original integer cutoff \(X\), with its actual terminal interval, shell, aligned base cells, clipping, depth and weights. On the same grid retain \(\mu_6(q)\mathbf1_{(q,P)=a}\). Keep only distinct pairs with \(\gcd(q,r)^{100}<X\) and, optionally, only the coarse levels. Denote the resulting signed sum by \(C_a(X)\). Then
\[
 \frac{\log(1+\max(0,C_a(X)))}{\log X}\longrightarrow 2B-1.
 \tag{1}
\]
In particular a cofinal subpower one-sided upper on the all-rough primitive pairs alone suffices. This compares the obstruction exponents of different graphs. A bound on their pointwise difference is neither required nor obtained. The original tree's proof and fixed-band source identity are paper deductions at the pinned repository baseline c867a8f15320ad6ac69177e0a498de4cb9d744f9. [Dyadic tree](../step4-harmonic-recovery-2026-11-19/DYADIC_TREE.md) · [Fixed-band zero detector](../step4-harmonic-recovery-2026-11-19/FIXED_BAND_THEOREM.md)

## The centered inverse pays for a growing prime mask

Freeze \(X\) and its \(P\) throughout each finite source identity, including its application at \(X/2\). The rough input \(\mu_P(n)=\mu_6(n)\mathbf1_{(n,P)=1}\) has Dirichlet-convolution inverse \(u_P(n)=\mathbf1_{(n,6P)=1}\). Indeed both Euler factors are exact formal identities. With \(u_6(n)=\mathbf1_{(n,6)=1}\),
\[
 u_P(n)=\sum_{\substack{d\mid n\\d\mid P}}\mu(d)\,u_6(n/d).
\]
For a fixed actual zero \(\rho=\frac12+\delta+i\gamma\), let \(K_6(z)=z^\rho\{\sum_{n\le z}u_6(n)n^{-\rho}-2^{1-\rho}\sum_{n\le z/2}u_6(n)n^{-\rho}\}\). This kernel is zero for \(z<1\) and bounded by a constant depending on \(\rho\). The latter follows from the bounded counting discrepancy of \(u_6\), partial summation, and its Dirichlet series vanishing at \(\rho\). Substitution into the finite centered sum gives exactly
\[
 K_P(z)=\sum_{d\mid P}\mu(d)K_6(z/d).
\]
The norm used in the finite Cauchy inequality is with respect to ordinary \(du\). The support eliminates all \(d>X\). Minkowski gives
\[
 \left(\int_1^X |K_P(X/u)|^2\,du\right)^{1/2}
 \le C_\rho\sqrt X\, A(X,y),\qquad
 A(X,y)=\sum_{\substack{d\mid P\\d\le X}}d^{-1/2}.                    \tag{2}
\]
For every fixed \(0<\xi<1/2\),
\[
 A(X,y)\le X^\xi\prod_{p\le y}(1+p^{-1/2-\xi})
 \le X^\xi\exp(O_\xi(y^{1/2-\xi}))=X^{\xi+o(1)}.
\]
The middle bound already follows by summing over ordinary integers. Since \(\xi\) is arbitrary and \(A\ge1\), the cost is \(X^{o(1)}\).

The source profile and compact filter in the existing fixed-band proof are kept intact. That identity reads
\[
 X^\rho(1-2^{1-\rho})G_k(\rho)
     =\int_1^X v_{P,k}(u)K_P(X/u)\,\frac{du}{u},\qquad
 v_{P,k}(u)=\sum_{n\le u}\mu_P(n)g_k(u/n).
\]
It follows by finite integration of \(u_P*v_{P,k}=g_k\) when the compact kernel fits below \(X/2\). The factor \(G_k(\rho)=G(\rho)\int e^{-(\rho-1/2)t}dk(t)\) is unchanged, with \(G(\rho)\ne0\). Thus the squared \(L^2(du/u^2)\) lower for the rough response costs at most \(A(X,y)^2=X^{o(1)}\) relative to the original lower. This preserves the same cutoff on both sides without a choice among prime-divided endpoints.

For clarity, all upper estimates used to isolate the fixed band are also uniform for these changing masks. For \(z\le 2X,\ l\le2X\) and any fixed \(\eta>0\), Euler-factor removal from the standard \(M(z)\ll_\eta z^{B+\eta}\) bound gives
\[
 \left|\sum_{\substack{n\le z\\(n,6Pl)=1}}\mu(n)\right|
 \ll_\eta z^{B+\eta}\, l^\eta X^{o_\eta(1)}.                          \tag{3}
\]
For \(B=1\), trivial counting suffices. Otherwise convolve \(\mu\) with the positive indicator of integers supported on the excluded primes. The extra factor from \(P\) is at most \(\prod_{p\le y}(1-p^{-B-\eta})^{-1}=\exp(o_\eta(\log X))\). This uses \(B+\eta\ge1/2+\eta\). The ordinary remaining primes dividing \(6l\) cost \(O_\eta(l^\eta)\) by bounding each sufficiently large prime's factor by \(p^\eta\). Equation (3) also holds on intervals by subtraction. The compact original profile and its partial-summation variation therefore bound the entire unfiltered rough response energy, including the output beyond the last input, by \(X^{2b+O(\eta)+o_\eta(1)}\).

When \(b>0\), use \(N=\lfloor\kappa\log X\rfloor\) modulated unit boxes at the ordinate of a fixed zero. The centered lower is \(\gg_\rho X^{2\delta-\kappa\delta-o(1)}\) by (2); outside the band of half-width four the integral costs \(O(X^{2b-2\kappa\log2+O(\eta)+o_\eta(1)})\) by (3). For any small prescribed exponent loss, choose \(\kappa>0\) small, then a fixed zero with \(\delta\) sufficiently close to \(b\), then \(\eta>0\) small enough. At \(\delta=b\) the separation of exponents is \(\kappa(2\log2-b)>0\). The genuine rough polynomial at every sufficiently large \(X\) therefore has squared energy \(\gg X^{2b-\text{loss}}\) in that fixed band. This argument does not require a rightmost zero.

## Prescribed factors, node complements and gcd weights

If the required prime pattern is \(a\), each nonzero original \(q\) in it is uniquely \(ar\) with \((r,6P)=1\), and \(\mu_6(q)=\mu(a)\mu(r)\). At every real frequency its exact prefix therefore equals
\[
 \mu(a)a^{-1/2-it} D^{\rm rough}_{X/a}(t;P).
\]
Use the same \(P\), fixed for this observation, at \(X/a\). Since \(a=X^{o(1)}\), the roughness condition on \(y\) is unchanged in log scale and the prefactor costs \(X^{o(1)}\) in squared magnitude. The lower above survives with arbitrarily small loss. The early labels \(q\le X^{.99}\) have norm \(O(X^{.99(b+O(\eta))+o_\eta(1)})\) on every fixed band by (3) and partial summation with the genuine dilation. They are smaller by a power when \(b>0\) and the loss and \(\eta\) are chosen sufficiently small.

The dyadic telescoping test now applies to the exact pattern on the original grid. It uses only the literal location of each atom and its sign. The positive tree form \(\sum_J2^{-j-k}|\sum_{q\in J}\mu_6(q)\mathbf1_{(q,P)=a}|^2\) retains lower exponent \(2b\), and (3) supplies upper exponent \(2b\). Neither a projected bin nor the change \(q=ar\) replaces the boundaries of the nodes.

In a shell \(U=2^j\), a pair from the pattern has gcd \(a f\) where \((f,6P)=1\). Put \(q=afu,\ r=afv,\ (u,v)=1\), and expand this last coprimality by full Möbius inversion over \(e\). Nonzero labels require \(f,e\) squarefree and \((e,6Pf)=1\). The two factor signs from \(a\) and from \(f\) square to one. The resulting inner sum is over \(h\) with \(afeh\) in the original node and \((h,6Pfe)=1\). By (3), after multiplication by \(U^{-1}\), the absolute value of the resulting \((f,e)\) summand is at most
\[
 X^{o_\eta(1)} O_\eta\!\left(
 U^{2b+2\eta} a^{-2B-2\eta}(fe)^{-1-2b}\right).
\]
This bounds a complete signed sum via its squared inner factor. With \(D=X^{.01}\), the original large-gcd condition is exactly \(f\ge D/a\). For \(b>0\) sum the displayed bound over \(f\ge D/a,e\ge1\); its order is \(X^{2b+O(\eta)+o_\eta(1)}D^{-2b}\), using \(a^{2b-2B}=a^{-1}\). Each node carries its further \(2^{-k}\) factor; their weighted count is \(X^{o(1)}\) by the tree proof. For \(b=0\) both harmonic sums are truncated below \(2U\) and cost \(O(\log^2(2X))\). The diagonal costs \(O(\log X)\) at all masks, and the absolute fine-level estimate \(O(\log X)\) survives deleting any subset of labels or pairs. These are all complements needed for (1).

For the all-rough case the source is genuinely sparse. In any interval of length \(H\), delete even just the primes up to \(z=\sqrt{\log X}\). Exact inclusion and exclusion gives at most \(H\prod_{p\le z}(1-1/p)+O(2^{\pi(z)})\) surviving integers. The product is \(O(1/\log z)\), since its reciprocal dominates \(\sum_{n\le z}1/n\). The interval count is therefore \(O(H/\log\log X+X^{o(1)})\). A finite allocation pattern has its own arithmetic and equality (1); the signs of different patterns can still compensate in the unrestricted sum. Simultaneously toggling a prime in both labels preserves their sign product and multiplies their gcd, and toggling in only one label generally leaves the narrow native cell.

## The critical cost of this proof and a finite control

For fixed \(A>2\), \(y=(\log X)^A\), the positive triangular majorant in (2) has actual exponent
\[
 A(X,y)=X^{1/2-1/A+o(1)} .
\]
For the upper apply the Rankin bound in (2) with \(\xi>1/2-1/A\) and let \(\xi\) decrease to its endpoint. For the lower put \(m=\lfloor\log X/\log y\rfloor\) and choose \(m\) distinct primes in \([y/2,y]\). By the ordinary prime number theorem there are \(\gg y/\log y\) choices before taking subsets. The binomial lower bound yields \(X^{1-1/A-o(1)}\) different products, all divisors of \(P\) at most \(X\). Each contributes at least \(X^{-1/2}\). Thus controlling larger cutoffs by this specific positive majorant would lose a power. The signed kernel in (2) could permit a stronger estimate.

At \(X=2^{20}\), \(y=400\), the rough sector contained 9,800 primes and 2,515 semiprimes, with no other labels. Its full primitive covariance was \(4284298445/268435456\). The nonrough sector gave \(1121339241/67108864\), and the mixed term was \(-35088235265/1073741824\). Their sum is the published unmasked value \(-9613629/1073741824\). The exact pattern \(a=5\) has zero primitive covariance at this cutoff: every pair shares 5, but the native gcd cap is 1. For a fixed nontrivial \(a\), any surviving primitive pair requires \(X>a^{100}\). This illustrates why finite samples cannot certify the eventual law. The smaller \(X=4103\) run also checked each sector by direct pair enumeration. [Exact receipt](ROUGH_TREE_CHECK.json) · [Reproducible calculation](check_rough_tree.py)
