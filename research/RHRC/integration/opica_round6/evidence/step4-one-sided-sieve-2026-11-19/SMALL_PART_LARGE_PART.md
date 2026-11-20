# The size and parity of the two factors of a surviving rough integer

**DERIVED on paper.** Fix any \(0<\delta<1\) and any positive integer \(k\). There is a fixed integer \(u=u(\delta,k)\) for which the complete-shell node comparison of [Prime-factor histories](PRIME_FACTOR_PATHS.md) can require every surviving label to factor as
\[
 n=d m,\qquad d=\prod_{\substack{p\mid n\\p\le U^{1/u}}}p\le U^\delta,
 \qquad k\le\omega(m)\le u+1.                                      \tag{1}
\]
All factors of \(d\) exceed the genuine threshold \(y=\lceil\log_2X\rceil^2\). Every factor of \(m\) exceeds \(U^{1/u}\). This is the unique split at the specified threshold. The same survivor set can satisfy the moving-threshold bounds below and the earlier running-count and cofactor conditions. The constants can depend on the requested restrictions. They are fixed before the cutoff or a hypothetical zero is selected.

There is also a directly measurable parity constraint before selection. Two disjoint ranges, each containing about half the usual number of prime divisors, have asymptotically independent parity bits on **every** sufficiently long cell of the actual squarefree rough source. The parity of a third range still multiplies their product in the exact Möbius sign.

## Local counts used in both deductions

Work in whole terminal shells \([U,2U)\subset(X^{.99},X]\), with the harmless convention at zero-weight power-of-two endpoints. All logarithms below are natural. Put \(V=\prod_{p\le y}(1-1/p)\), \(L=\log\log U\), and take a cell \(J\) of length \(H\ge U^{.48}\) inside the shell. For **every** squarefree \(a\) whose primes exceed \(y\), uniformly in the cell and \(a\),
\[
 N_a:=\#\{n\in J:a\mid n,\ P^-(n)>y\}
   ={H\over a}\big(V+O_A((\log U)^{-A})\big)+O_A(U^{o(1)}).     \tag{2}
\]
Indeed the multiples of each \(a e\), with \(e\) supported on primes through \(y\), have count \(H/(ae)+O(1)\). Bonferroni at adjacent orders \(C_A L+O(1)\) leaves relative-to-\(H/a\) error bounded by \((\sum_{p\le y}1/p)^j/j!\ll_A(\log U)^{-A}\). At most \(y^{j+1}=U^{o(1)}\) distinct floor errors occur. In particular \(N_1\sim HV\). For all prime ranges \(I\subset(y,U^{1/40}]\), write \(M_I=\sum_{p\in I}1/p\) and \(R_I(n)=\sum_{p\in I}\mathbf1_{p\mid n}\). Expanding the fourth power as in [the original cell moment proof](PRIME_FACTOR_PATHS.md), (2) yields
\[
 {1\over HV}\sum_{n\in J,\,P^-(n)>y}(R_I(n)-M_I)^4
     \le 3M_I^2+M_I+o(1).                                          \tag{3}
\]
The \(o(1)\) is uniform in \(I\). Four selected primes give at most \(U^{1/10+o(1)}\) floor error. The independent Bernoulli variables of means \(1/p\) evaluate only the expanded main terms. Their fourth centered moment is bounded by \(3M_I^2+M_I\).

The target upper bounds may count all rough integers. When a normalized distribution on squarefree labels is asserted, the rough nonsquarefree count is at most
\[
 O(H/y+U^{1/3}) .                                                   \tag{4}
\]
For \(y<p\le U^{1/3}\) sum \(H/p^2+1\). For \(p>U^{1/3}\) write \(n=j p^2\), where \(j\le2U^{1/3}\). For each \(j\) the interval for \(p\) contains at most \(1+O(H/\sqrt{Uj})\) integers. This gives \(O(U^{1/3}+HU^{-1/3})\) for that range. Thus the squarefree rough population has size \(HV(1+o(1))\).

## A fixed power threshold and a prescribed minimum number of large factors

For \(y<t\le U^{1/40}\), let \(D_t(n)=\prod_{y<p\le t,\ p\mid n}p\), using each prime once. Summing (2) with weights \(\log p\) gives, uniformly for the fixed and moving choices below,
\[
 {1\over HV}\sum_{n\in J,\,P^-(n)>y}\log D_t(n)
      \le (1+o(1))\log t .                                          \tag{5}
\]
Here \(\sum_{p\le t}\log p/p=\log t+O(1)\), and the summed floor error is \(O(U^{1/40+o(1)})\). Take \(t=U^{1/u}\), with \(u>40\) fixed. The proportion relative to \(HV\) for which \(D_t>U^\delta\) is at most \((1+o(1))/(u\delta)\).

For \(I=(U^{1/u},U^{1/40}]\), Mertens' prime harmonic estimate gives \(M_I=\log(u/40)+o(1)\) **for each fixed \(u\)**. If a squarefree label has fewer than \(k\) factors above \(U^{1/u}\), then \(R_I<k\). As long as \(M_I>k\), (3) bounds the fraction of such rows by
\[
                 {3M_I^2+M_I+o(1)\over (M_I-k)^4}.                \tag{6}
\]
For any prescribed fraction \(b_0>0\), choose a fixed \(u\) so large that \(1/(u\delta)<b_0/4\), \(\log(u/40)>2k+2\), and the limiting right side in (6) is below \(b_0/4\). All sufficiently late cells then have at most \(b_0 HV\) rows violating either condition. An upper of \(u+1\) follows directly from \(n<2U\) and the size of every factor. This proves the local target estimate behind (1). The potentially very large fixed \(u\) makes (1) an asymptotic assertion.

## A moving split with subpower small part

Put
\[
 z_0=\exp(\sqrt{\log U}),\qquad z_1=\exp(\log U/L^2).
\]
Eventually \(y<z_0<z_1<U^{1/40}\). Fix three disjoint factor ranges \(I_0=(y,z_0]\), \(I_1=(z_0,z_1]\), and \(I_2=(z_1,2U]\), with counts \(r_i=R_{I_i}(n)\) and harmonic centers \(M_i\). Explicitly,
\[
 M_0=\tfrac12L-\log\log y+o(1),\qquad
 M_1=\tfrac12 L-2\log L+o(1),\qquad
 M_2=2\log L+o(1).
\]
For an arbitrarily small fixed fraction of targets, (5) and Markov allow the requirement \(D_{z_0}\le\exp(C\sqrt{\log U})=U^{o(1)}\) with fixed \(C\). Formula (3) and the union bound allow simultaneous requirements
\[
 |r_0-M_0|\le K\sqrt{1+M_0},\quad |r_1-M_1|\le K\sqrt{1+M_1},
 \quad |r_2-M_2|\le K\sqrt{1+M_2}.                                 \tag{7}
\]
For the last range apply (3) just through \(U^{1/40}\). At most 41 additional distinct factors occur and their harmonic mass is bounded, so their error fits the right side of (7) for all sufficiently late \(U\), after increasing \(K\). The three fractions can be made jointly as small as needed by choosing \(K\) first. In particular both parts of the two-way split at \(z_0\) have factor counts within \(O_K(\sqrt L)\) of their own half-loglog centers. Conditions (1) and (7) use different thresholds and hold together by adding their target lists.

## A finite Fourier calculation on the actual squarefree source

Write \(b_i=(-1)^{r_i}\). Uniformly on the same complete cells, for \(I=I_0,I_1\), or \(I_0\cup I_1\), the **unselected** actual squarefree rough population satisfies
\[
 \mathbb E_{J,\mathrm{sf,rough}} (-1)^{R_I}
    =(1+o(1))\prod_{p\in I}(1-2/p).                                \tag{8}
\]
Here is the absolute error calculation. For an integer \(r\ge0\), Taylor's formula on \(0\le t\le1\) for \((1-2t)^r\) gives
\[
 \left|(-1)^r-\sum_{j<D}(-2)^j{r\choose j}\right|
                        \le 2^D {r\choose D}.
\]
If \(r<D\) the remainder vanishes. Otherwise the integral remainder uses \(|1-2t|^{r-D}\le1\). Choose \(D=\lceil C_A L\rceil\). Every squarefree product in these divisor sums has size at most \(z_1^D=U^{O_A(1/L)}\). The total floor error in the rough expectation from (2) is at most \(2^{D+1} z_1^D U^{o(1)}/(HV)=U^{-.48+o(1)}\). For the main terms the sum of absolute coefficients weighted by reciprocals is at most \(\prod_{p\in I}(1+2/p)\le e^{2M_I}\ll(\log U)^2\). Take a larger precision exponent in (2) to absorb this and normalization by \(V\). The expected Taylor remainder of the corresponding independent Bernoulli variables is bounded by \((2M_I)^D/D!\ll_A(\log U)^{-A}\), after enlarging \(C_A\). The same majorant and (2) bound the actual remainder. Consequently the characteristic expectation over the unrestricted rough population differs from the product by \(O_A((\log U)^{-A})\). Passing to squarefrees costs
\[
 O\big(1/(yV)+U^{1/3}/(HV)\big).
\]
The three products in (8) have respective sizes asymptotic to
\[
 { (\log y)^2\over \log U},\qquad
 {L^4\over\log U},\qquad
 {(\log y)^2L^4\over(\log U)^2}.
\]
Indeed \((1-2/p)/(1-1/p)^2=1+O(p^{-2})\) and the smallest prime here exceeds \(y\to\infty\). Mertens' product theorem gives each ratio with relative \(o(1)\). Even the smallest displayed scale dominates the squarefree adjustment, since \(y\asymp(\log U)^2\) on the terminal shells. This verifies (8) at its actual sign and scale. For \(e_0,e_1\in\{-1,1\}\),
\[
 \Pr(b_0=e_0,b_1=e_1)
  ={1+e_0\mathbb E b_0+e_1\mathbb E b_1+e_0e_1\mathbb E(b_0 b_1)\over4}
  =\tfrac14+o(1).
\]
This calculation measures two parities in the complete original population. The selection depends on signs, so it does not automatically preserve those biases.

## Signed cost and remaining estimate

Use the nested opposite-sign matching of [Prime-factor histories](PRIME_FACTOR_PATHS.md) once, with the **union** of its prescribed targets and all new exceptional rows. In that construction each good cell has spare capacity \(\gg\kappa HV\) in both genuine donor signs, including at the final scale. Choose the earlier path constant and the new constants so that the sum of the new target budgets is a sufficiently small fraction of this margin. Remove every target from the donor lists before matching. Each addition both requires at most one donor and can disqualify at most one offer, which fits the fixed slack. The additions satisfy their upper estimates on every cell at all three matching scales. Hence the same two exceptional-volume estimates and the all-cell final stage give, for each polarity \(e=\pm1\),
\[
 \sum_{J\ \mathrm{in\ one\ complete\ shell}}w_J
       \left|[e f_J]_+^2-[e r_J^{\rm surv}]_+^2\right|=O(1).         \tag{9}
\]
Here \(r_J^{\rm surv}\) is the charge of the exact complement of the selected targets **and the donors actually spent**. For the smaller nodes the geometric absolute bound is \(O(H_1^2/H_0)\), for intermediate nodes the unmatched target counts control the signed cross terms, and above the last matching scale the removed charge is zero. The proof of (9) applies before any GCD test between individual rows. Its original implication for Step 4 comes from applying the full-source theorem first. No incidence estimate after imposing the primitive pair mask on the new selection is asserted.

On every surviving row the signed coefficient is exactly \(\mu(d)\mu(m)=b_0 b_1 b_2\), where \(b_2=(-1)^{r_2}\). Equations (1) and (7) constrain factor sizes and counts, and (8) identifies two genuine Fourier coefficients and their product before selection. A bound for the correlation with the third sign in the actual cells at the precision required by (9) remains **OPEN**. Even perfectly fair independent first and second bits can have a third bit equal to their product. That abstract example tests the logical inference from the two marginals and their product. It makes no claim about the actual primes. No new Lean or CI qualification accompanies this paper deduction.
