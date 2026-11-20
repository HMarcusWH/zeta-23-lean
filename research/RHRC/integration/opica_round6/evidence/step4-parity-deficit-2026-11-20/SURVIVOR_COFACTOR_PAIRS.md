# Cancellation across largest-prime cofactors on genuine survivor intervals

**DERIVED on paper.** On the PR 303 arithmetic graph, exchanging a label's largest prime while keeping its cofactor fixed preserves its Möbius sign. In every sufficiently long interval this family of positive signed edges has a sharp, independently determined size after matching. The remaining edges must cancel it to quantified precision. For the earlier subpower selector this holds unconditionally on every sufficiently late aligned horizon, on the complete tree of each specified shell and on all sufficiently long translated subintervals. Step 4 remains **OPEN**.

Use the research branch at [adc9c6ce](https://github.com/HMarcusWH/zeta-23-lean/tree/adc9c6ce04f73dc276513b81ae4a316a0a8367eb). Work in a complete terminal dyadic shell $[U,2U)$ with $X/4\le U\le X/2$, hence $U\asymp X$. At sufficiently large $X$ such a shell lies entirely inside the native terminal range. Set $y=\lceil\log_2 X\rceil^2$, $V(y)=\prod_{p\le y}(1-1/p)$, $D=X^{.01}$ and $H_0=U2^{-s_X}$. For the earlier aligned construction take $X=2^{100t}$. A surviving squarefree rough label has the unique form $n=mp$, $p=P^+(n)$, $p\nmid m$, and has coefficient $-\mu(m)$. All counts below are of actual integer labels.

## The positive pair count

For $J\subset[U,2U)$ of length $H$ let $t_m(J)$ count the surviving labels $mp\in J$. Let
$$S(J)=\sum_m t_m(J)(t_m(J)-1).$$
This is the signed sum over ordered, distinct, equal-cofactor pairs. The two signs multiply to $+1$. For different primes $p,q$ we have $\gcd(mp,mq)=m$, including the case of a composite cofactor. Denote by $S_D(J)$ the same sum restricted to $m<D$. Thus $S_D$ is exactly the corresponding family surviving the native primitive-pair test.

For the fixed-power path selector put $Z=X^\kappa$ with its admissible fixed small $\kappa<.001$. Under the constant choices below, uniformly for all $H\ge U^\lambda$ with fixed $\lambda>17/30+(13/30)\kappa$, $\lambda<1$,
$$
 S_D(J)\asymp S(J)\asymp \frac{H^2V(y)}{Z(\log U)^2}. \tag{1}
$$
For the earlier aligned all-rough selector use $Z=\lfloor 2^{s_X/200}\rfloor$ and any fixed $\lambda>17/30$, $\lambda<1$. The same formula holds. The constants can depend on the fixed selection parameters and $\lambda$. The intervals in (1) can be arbitrary subintervals of the complete matched shell. Equality of the total surviving and original signed charges is invoked below only on aligned nodes where the matching proves it. [Fixed-power path selector](../step4-one-sided-sieve-2026-11-19/PRIME_FACTOR_PATHS.md) · [Earlier subpower selector and its all-rough variant](../step4-prime-transport-2026-11-19/PRIME_SPLIT.md)

**Upper.** Every survivor has $m>Z$. Write $a_0=17/30$ and choose $\theta>\kappa$ (or $\theta>0$ for subpower $Z$), with $\lambda-\theta>a_0(1-\theta)$. We may also take $\theta<1/2$. For $m\le U^\theta$ the true prime interval $J/m$ exceeds a fixed power margin above $(U/m)^{a_0}$. Guth–Maynard yields $t_m(J)\ll H/(m\log U)$, irrespective of any further deletion. If the interval exceeds the upper length in their stated form, split it into equal pieces of a permitted fixed smaller power length. The same argument supplies a matching lower bound for the **unselected primes** in each $J/m$. For squarefree rough $m>Z$, dyadic partial summation of the elementary upper $\#\{T\le m<2T:P^-(m)>y\}\ll TV(y)$ uniformly in $T\ge Z$ gives $\sum_{m>Z,\ {\rm rough}}m^{-2}\ll V(y)/Z$. For $m>U^\theta$ integer spacing gives $t_m(J)-1\le H/m$ when $t_m(J)>0$. Since there are at most $H+1$ labels in total, that tail costs $O(H^2/U^\theta)$, absorbed in (1). The rough count follows by truncating inclusion and exclusion at $O(1+\sum_{p\le y}1/p)$ with a large fixed constant. The floor error $y^{O(1+\sum_{p\le y}1/p)}$ is $o(ZV(y))$ even for the subpower choice. [Guth–Maynard, Corollary 1.3](https://arxiv.org/abs/2405.20552)

**A protected dyad.** Put $M=2Z$. In $[M,2M)$ at least $c_0 MV(y)$ squarefree rough cofactors have exactly two prime factors in $(y,y^2]$, for an absolute $c_0>0$. Write $m=\ell_1\ell_2 d$, $y<\ell_1<\ell_2\le y^2$, with $d$ squarefree and $y^2$-rough. The rough count above and square removal give $(1+o(1))MV(y^2)/(\ell_1\ell_2)$ possibilities uniformly. Indeed $M/y^4$ still exceeds every fixed power of $y$, and the direct square-divisor bound on a full dyad of order $T$ costs $O(T/y^2+\sqrt T)$. These representations are unique. The reciprocal sum tends to $(\log 2)^2/2$, and $V(y^2)/V(y)\to1/2$. Both actual partner pools contain only cofactors with zero or one prime in $(y,y^2]$. No label with one of these two-prime cofactors can be spent as a donor. Also $m>Z$, so it is never a small-cofactor target. For the subpower selector this already proves protection.

For the fixed-power path selector we must also meet its genuine target conditions. On the cofactor dyad $M\asymp X^\kappa$ the same maximal fourth-moment proof for the rough population gives
$$\#\{m\in[M,2M):P^-(m)>y,\ D_m(m)>K\sqrt L/2\}\ll K^{-4} MV(y),$$
where $L=1+\sum_{y<q\le2U}1/q$ (primes $q$), and $D_m$ is the supremum of the original centered prime-factor count through $2M$. The proof applies on the full cofactor dyad since its length is $M$, $y\asymp_\kappa(\log M)^2$, its sieve floor errors are $M^{o(1)}$, and even fourth moments of primes through $M^{1/40}$ use only $M^{1/10+o(1)}$ floors. For all primes $p$ with $mp\in J$ we have $p>2M$. Above $2M$ inserting that one prime costs at most one in the count, and the extra centering harmonic mass through $2U$ is $\log(1/\kappa)+O(1)$. Choose $K$ sufficiently large compared with $c_0^{-1/4}$ as well as the existing donor budget, then $X$ sufficiently large at these fixed constants. At least a fixed fraction of the protected dyad survives the path test for **every** such $p$.

The optional fixed-$k$ and moving-split refinements in the [stronger selector](../step4-one-sided-sieve-2026-11-19/SMALL_PART_LARGE_PART.md) also work if their permitted constants are chosen for this dyad. For prescribed $\delta,k$ fix $u>80/\kappa$. The harmonic mass of $(U^{1/u},M^{1/40}]$ tends to $\log(\kappa u/40)$. Make this much larger than $k$. The cofactor dyad's fourth moment bounds the fraction with fewer than $k$ such factors by $O((1+\log(\kappa u/40))^{-2})$. Markov for $\log\prod_{y<q\le U^{1/u},\,q\mid m}q$ costs $O(1/(u\delta))$ at $\delta\log U$. Make the sum smaller than $c_0/8$. At the moving thresholds $z_0=\exp(\sqrt{\log U})$, $z_1=\exp(\log U/(\log\log U)^2)$, both are eventually below $M^{1/40}$. Apply the same fourth moments separately to the first two bands and the last band through $M^{1/40}$. The remaining primes of $m$ add $O(1)$ factors, their centering mass through $2U$ is $O_\kappa(1)$, and the largest prime $p$ adds just one. The harmonic center in the last band tends to infinity. After enlarging the fixed count constants, these bounded shifts fit inside each allowed tolerance. Markov at $z_0$ costs $O(1/C)$ for the moving small-product allowance $\exp(C\sqrt{\log U})$. Choose constants so the sum of all exception proportions on this dyad is below $c_0/2$, and retain the earlier whole-cell target budgets by making the same constants sufficiently large. No independence between exception lists is used. The largest prime cannot itself supply the prescribed many large factors. The cofactor estimate explicitly supplies them. This strengthening concerns these permissible choices for the fixed-power selector, not an arbitrary later selection.

For the resulting $\gg MV(y)$ cofactors, all primes in $J/m$ occur in the selected **survivor** graph. Each contributes $t_m(J)\gg H/(M\log U)\to\infty$. Every such $m<4Z<D$ for large $X$, so all these ordered pairs pass the GCD test. This proves (1) pointwise. In the full or coarse tree on this shell every within-base pair gets between $1/U$ and $2/U$ in summed ancestor weights (counting the base alone gives the lower bound). Summing (1) over all $2^{s_X}$ roots gives total weighted equal-cofactor mass $\asymp H_0 V(y)/(Z\log^2 U)$. For fixed-power $Z$ its exponent is exactly $1-\kappa$.

## The entire signed complement

On a base node let $r_J$ be the actual surviving charge, and $N_J$ the number of survivors. The earlier opposite-sign matches all finish within each such node, giving exactly $r_J=f_J$, the complete rough Möbius charge. For ordered distinct pairs with unequal cofactors the unrestricted signed total $C_{\ne}(J)$ satisfies
$$ C_{\ne}(J)+S(J)=r_J^2-N_J. \tag{2} $$
The corresponding primitive total satisfies
$$ |C_{\ne,D}(J)+S_D(J)|\le r_J^2+O\big(H+H^2/D+H\log(2H)\big). \tag{3} $$
Indeed rejected distinct pairs with a common divisor $d\ge D$ have a nonzero difference of magnitude at most $H$, so $d\le H$. Union bounding them over integers $D\le d\le H$ costs at most $2\sum (H/d+1)H/d$. This is only a bound at the large scale of (1). It supplies no critical bound for deleted GCD incidence.

For fixed-power $Z$ the established rough Mertens estimate gives $|f_J|\ll_\varepsilon U^{B+\varepsilon}$, $B=\sup_\rho\Re\rho$. On each base node (1)–(3) give
$$
 \left|1+\frac{C_{\ne,D}(J)}{S_D(J)}\right|
 \ll X^{2B-2+\kappa+o(1)}+X^{\kappa-.01+o(1)}.
$$
The first exponent must be negative to force relative cancellation. Without the primitive test the second term drops. The conclusion uses the predecessor upper for the genuine source and keeps its dependence on $B$. [Rough-source estimate](../step4-prime-transport-2026-11-19/ROUGH_PRIME_TRANSPORT.md)

**Unconditional signed estimate for subpower $Z$.** Write $F(U)=(\log U)^{3/5}(\log\log U)^{-1/5}$. The unconditional Mertens bound is $|M(t)|\ll t\exp(-cF(t))$. The exact identity $\mu_y=\mu*\mathbf1_{\{y\text{-smooth}\}}$ includes all prime powers in the smooth factor. For $t\asymp U$ sum $M(t/d)$ over smooth $d\le\sqrt t$ using $\sum_{\rm smooth}1/d=1/V(y)$ and $F(\sqrt t)\asymp F(t)$. For the tail use its trivial absolute bound and
$$
 \sum_{d>\sqrt t,\ {\rm smooth}}1/d
 \le e^{-\log(t)/(2\log y)}\prod_{p\le y}(1-p^{-1+1/\log y})^{-1}
 \ll e^{-\log(t)/(2\log y)}(\log y)^{O(1)} .
$$
The product bound follows by separating the harmonic first powers using $p^{1/\log y}\le e$ and bounding higher powers absolutely for large $y$. The two prefixes at the actual integer endpoints thus give $|f_J|\ll Ue^{-c_1 F(U)}$. On the aligned base cells $\log(U/H_0)+\log Z=O(\sqrt{\log U})=o(F(U))$. Applying (1)–(3), including every primitive pair, yields uniformly
$$
 \boxed{\displaystyle
  C_{\ne,D}(J)=-S_D(J)\big(1+O(e^{-c_2 F(U)})\big) .}
$$
The same estimate holds without the GCD mask. This is a constraint on the actual post-matching signs. It uses no fixed zero ceiling. It controls a relative error against an exponentially large family. After normalizing and summing base nodes, the permitted **absolute** error can still have size $X^{1-o(1)}$. The independent subpower bound needed for Step 4 has not been derived. [Lee–Leong, unconditional Mertens estimate](https://arxiv.org/abs/2208.06141)

## All tree depths and translated intervals

Let $Z$ be the aligned subpower cutoff and fix $0<a<c_1/4$. Put $H_*=U\exp(-aF(U))$. Eventually $H_3<H_*<H_0$, where $H_3=2^{\lfloor .58\log_2 U\rfloor}$. On every translated $J$ in the complete shell, the only stages that can change its total signed charge lie in its two partially intersected $H_3$-cells. Their combined discrepancy is at most $2H_3+2$ since each label participates in at most one matched pair. Thus $|r_J|\ll U\exp(-c_1 F(U))+2H_3+2$. For all $H\ge H_*$, (1) is applicable and $Z\log^2 U/V(y)=\exp(o(F(U)))$. Dividing (3) by the lower bound in (1) gives the same $\exp(-c_3 F(U))$ relative error, with a fixed $c_3>0$, on *every* such interval inside the complete shell. This includes all native aligned nodes at those lengths. A clipped shell boundary at which the matching itself changes is outside this result.

In fact, if $\mathcal T$ is the entire native tree on the complete shell, or any subset of its nodes that retains every base cell, then
$$
 \sum_{J\in\mathcal T}w_J\,|C_{\ne,D}(J)+S_D(J)|
 \ \ll\ \exp(-c_4 F(U))\sum_{J\in\mathcal T}w_J\,S_D(J).
 \tag{4}
$$
The same conclusion holds for the unrestricted pair family. For $H\ge H_*$ this follows termwise. For $H<H_*$ the absolute value at a node is bounded by its number of distinct ordered pairs, at most $H^2$. At each native length the number of nodes is $U/H$ and the weight is $H/(UH_0)$. Summing the geometric progression, the contribution from all smaller lengths is $O(H_*^2/H_0)$. The base cells alone contribute $\gg H_0V(y)/(Z\log^2U)$ on the right before its exponential factor. The ratio is bounded by $\exp(-2aF(U)+o(F(U)))$. This proves (4) with absolute residuals *inside* the sum and no cancellation between different nodes.

For fixed-power $Z$ the whole-shell relative upper is instead $X^{2B-2+\kappa+o(1)}+X^{\kappa-.01+o(1)}$, as on the base cells. Indeed $\sum_J w_J f_J^2\ll X^{2B-1+o(1)}$ by applying the complete-prefix bound at both endpoints and summing the native weights, which total $1/H_0$ per level. The two signed one-polarity transfers in the path-selector theorem give $\sum_J w_J r_J^2\le\sum_J w_J f_J^2+O(1)$. The remaining terms in (3) cost $O(H_0/D+\log U)$ in total. Divide by the base denominator $H_0V(y)/(Z\log^2U)$. This retains the earlier condition on $B$ for fixed-power relative decay.

The positive mass (1) also localizes in cofactor size. In the proof of its upper bound one can start the rough reciprocal-square sum at $RZ$. For $1\le R\le U^\theta/Z$, the contribution from $m>RZ$ is
$$
 O\left(\frac{H^2V(y)}{RZ\log^2U}+\frac{H^2}{U^\theta}\right).
$$
This localization concerns an unweighted counting sum over actual signed-positive edges. A fixed multiple of $Z$ captures any prescribed fixed fraction for sufficiently large $U$ and sufficiently large fixed $R$.

## Finite graph cross-check

The [exact calculation](check_survivor_cofactor_pairs.py) imports the maintained PR 303 vertex generator, independently factors each retained label, and compares direct ordered signed counts against the cofactor formula and divisor inversion on two complete native base cells. Together they contain 10,729,770 ordered distinct pairs on the genuine rough source. At $X=1{,}656{,}575$ the larger base has $5{,}323{,}298$ signed units on equal cofactors and $-2{,}507{,}192$ on the different cofactors before the GCD test. The strict native mask retains $5{,}319{,}942$ and $-2{,}508{,}320$ respectively. Independent group and edge counts agree exactly. Removing all primes without matching changes the sign of the different-cofactor total to positive. Every surviving composite in this finite cell has exactly two prime factors, and $1<D<2$ excludes every equal composite cofactor. This is a preselection diagnostic and illustrates why these finite horizons cannot measure the asymptotic postselection estimate. [Exact input hashes, cells and signed outputs](SURVIVOR_COFACTOR_PAIRS_CHECK.json)

**Consequence.** Prime substitutions inside one largest-prime cofactor fibre cannot produce the missing cancellation. Their entire signed contribution is positive and has the size in (1). The interactions between different cofactors compensate this positive contribution at every length in the weighted sense of (4). The residual allowed by (4) still has order up to $X^{1-o(1)}$. Step 4 needs a bound by $X^\varepsilon$ for every $\varepsilon>0$ on the required horizons, after the complete source transfer. This is a paper deduction. It entails no new Lean theorem, CI qualification, or proof of RH.
