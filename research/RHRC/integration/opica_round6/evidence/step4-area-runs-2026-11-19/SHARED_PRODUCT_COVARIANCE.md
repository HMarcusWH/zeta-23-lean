# An independent bound for equal and nearby product rows

**DERIVED on paper.** Two prime sums over disjoint ranges recover \(F(x)=A_\vartheta(x)+\tfrac23x^{3/2}\) to error \(o(x^{3/2})\) at the same real \(x\). One uses the [factorial projections](OLD_PRIME_LOCALIZATION.md) with the supplied zero ceiling. The other uses the [eta filters](ETA_FILTERED_PRIME_LOCALIZATION.md) with unconditional contour bounds. Expanding the genuine arithmetic coefficients assigns a row to every integer product. For the choices below, the entire absolute contribution of equal rows to the cross product is \(O_\epsilon(x^{3+\epsilon})\) for every \(\epsilon>0\). The same holds for all pairs of rows separated by at most \(\exp(\sqrt{\log x})\), together. Genuine semiprimes alone give a positive matched-row subtotal asymptotic to a specified constant times \(x^3\). The bound for the complete signed contribution of more widely separated rows is **OPEN**.

## Putting both calculations on the same integers

Take \(L_1=\lfloor x^{0.11}\rfloor,\ L_2=\lfloor x^{0.37}\rfloor\). Use the factorial outer-prime support above \(x^{3/4}/[L_1\log^2(2L_1)]\) and below \(x/(L_1+1)\), and the eta support above \(x^{0.025}\) and below \(x/(L_2+1)\). The intervals are disjoint for sufficiently large \(x\). For the first four coefficient corrections keep \(R_1=2L_1+1\); for the second four use \(R_2=1+2R_1\lceil L_2/R_1\rceil\), with correction indices \(4^iR_j,\ 0\le i\le3\). This mild choice makes the odd bases coprime. It satisfies \(2L_2<R_2\le2L_2+2R_1+1\). The fixed four-by-four inverse, coefficient estimates, cancellation of residues, and matching through \(L_2\) in the eta proof use only \(R_2\asymp L_2\) and \(R_2>2L_2\). They hold for this choice. Both systems still use their exact, fixed, source-derived coefficients at the same \(x\).

Write \(w_i(j)\) for the coefficient of the ramp \((y-j)_+\) in the combined filter, \(r_i(j)=\mathbf 1_{j=1}-w_i(j)\), and \(\mathcal P_i(x)\) for the respective outer-prime intervals. The surviving observations are **exactly**
\[
 S_i(x)=\sum_{n\le x}(x-n)b_i(n;x),\qquad
 b_i(n;x)=\sum_{\substack{p\mid n\\p\in\mathcal P_i(x)}}(\log p)\,r_i(n/p).
\]
By the two localization proofs \(S_i(x)=F(x)+o(x^{3/2})\). The primary summation primes differ. Their divisor rows, Möbius coefficients, calibrations and observation horizon are coupled.

## Absolute accounting for every fixed shift

Put \(V(n)=2^{v_2(n)/2}\). All factors \(x^{o(1)}\) below are uniform in positive integers up to \(x\), using the usual divisor bound. Let \(\mathcal D=\{4^iR_1:0\le i\le3\}\), \(\mathcal E=\{4^iR_2:0\le i\le3\}\). The elementary majorants are
\[
 |b_1(n;x)|\le x^{o(1)}
       \left(1+\sum_{d\in\mathcal D,\ d\mid n}d\right),\qquad
 |b_2(n;x)|\le x^{o(1)} V(n)
       \left(1+\sum_{e\in\mathcal E,\ e\mid n}e\right).
\]
For the first, the low inverse coefficients have absolute value at most 1. Summing over divisors and allowable prime labels, and paying each logarithm and the four \(O(\log^2 x)\) coefficients, gives the bound. For the second, the coefficients of \(H(s)=\zeta(s)\eta(2s)\eta(3s)\) count signed factorizations \(ab^2c^3=n\), of absolute size at most a fixed divisor power. In \(1/H(s)\), the two inverse geometric factors have weights \(2^{i+j}\) on \(2^{2i+3j}\). These weights are at most \(V(n)\); all other inverse factors have Möbius coefficients of absolute value at most 1. The number of representations again costs only a fixed divisor power. Divisor convolution, prime labels, deletions and exact matching cost at most another \(x^{o(1)}\). These majorants include every surviving index and correction.

For any integer shift \(k\) with \(|k|\le x\), consider \(n,m=n+k\) both in \([1,x]\). Expand the two majorants, allowing \(d=1\) or \(e=1\) for the unmarked terms. If \(d\mid n,\ e\mid m\) are compatible then \(m\) lies in one class modulo \(M=\operatorname{lcm}(d,e)\). The identical argument holds for negative \(k\). Since \(R_1,R_2\) are odd and coprime, \(\gcd(d,e)\le64,\ v_2(M)\le6\). Uniformly in the class \(c\),
\[
 \sum_{\substack{1\le m\le x\\m\equiv c\bmod M}}V(m)
 \le \sum_{0\le j\le\log_2x}2^{j/2}
         \left(\frac{x}{\operatorname{lcm}(2^j,M)}+1\right)
 \ll x/M+\sqrt{x}.
\]
Indeed \(V(m)\le\sum_{2^j\mid m}2^{j/2}\) and each compatible pair of congruences is a single class. Multiplying by \(de\) costs \(O(x+de\sqrt{x})=O(x)\), since \(de=O(x^{0.48})\). With the two ramps bounded by \(x^2\), this proves uniformly in \(k\)
\[
 \sum_{\substack{1\le n,m\le x\\m-n=k}}
 |(x-n)(x-m)b_1(n;x)b_2(m;x)|\le x^{3+o(1)}. \tag{1}
\]
Thus one may pay every row with equal product and every shift \(|k|\le H(x)\) for **any** fixed choice \(H(x)=x^{o(1)}\). One cannot sum this estimate by absolute values over \(O(x)\) shifts at the same cost.

## A positive true-prime diagonal of exactly the critical size

Let \(a=13/25,\ b=3/5,\ c=11/10,\ d=13/10\). Take genuine primes \(p\in[a x/L_1,b x/L_1]\) and \(q\in[cL_1,dL_1]\). For all large \(x\), only \(p\) lies in \(\mathcal P_1\) and only \(q\) in \(\mathcal P_2\). Also \(q>L_1\) is below all first calibration nodes and \(p\) exceeds every second calibration node and \(L_2\). At a prime index \(j\) above its matching range and different from every correction node, both filters have coefficient \(w_i(j)=1\): the coefficient of \(H\) at a prime is 1, and the only possible nonunit divisor is \(j\) itself. Thus at \(n=pq\), \(b_1=-\log p\) and \(b_2=-\log q\) exactly. Unique factorization gives distinct rows for all these pairs. Since \(bd<1\), their products are within the cut. On this rectangle ordinary PNT and partial summation give
\[
 x^{-3}\sum_{p,q}(x-pq)^2\log p\log q
 \ \longrightarrow\int_a^b\!\int_c^d(1-uv)^2\,dv\,du
 =\frac{61537}{35156250}>0.
\]
For example, expand the polynomial into three terms and apply PNT separately to each of the six scaled log moments. This is a positive subtotal; the remainder of the signed cross product can have either sign. The complete absolute diagonal thus has exponent exactly three. The finite controls verified 126 distinct examples across four scales with certified integer primality and exact rational arithmetic. [Code](check_shared_semiprimes.py) · [Receipt](SHARED_SEMIPRIMES_CHECK.json)

## Pairs sharing a small common multiple

A different family can also be paid in absolute value. Set \(U=x\exp(\sqrt{\log x})\). Assign \((n,m)\) to \(w=\operatorname{lcm}(n,m)\). For fixed \(w\le U\) there are at most \(\tau(w)^2=x^{o(1)}\) eligible ordered pairs. The divisibility indicators in the two majorants are each bounded by their value at \(w\), and \(V(m)\le V(w)\). Summing the resulting double majorant over \(w\le U\) is the preceding \(k=0\) calculation with input length \(U\) and the same fixed correction nodes from \(x\). It costs \(U^{1+o(1)}\), since \(de\ll x^{0.48}\le U^{0.48}\). The original ramp weights are still at most \(x\) each. Thus all pairs with \(\operatorname{lcm}(n,m)\le U\), including unequal, widely separated indices, cost \(x^{3+o(1)}\) in total. The union of this family and the near-diagonal band obeys the same absolute bound. One may even pay all pairs with the additional weight \(\min(1,x/\operatorname{lcm}(n,m))\) by summing dyadic ranges in \(w\le x^2\); no such attenuation is part of the actual unweighted cross product.


## The remaining source-specific upper

Fix \(H(x)=\exp(\sqrt{\log x})\). After the two absolute bounds, an independent one-sided upper \(x^{3+o(1)}\) for the **signed** sum over pairs satisfying **both** \(|n-m|>H(x)\) and \(\operatorname{lcm}(n,m)>xH(x)\) would imply \(S_1(x)S_2(x)\le x^{3+o(1)}\). It suffices that this hold uniformly for actual \(x\) in arbitrarily late complete windows \([X,X\log X]\). Since each \(S_i=F+o(x^{3/2})\), it implies \(|F(x)|\le x^{3/2+o(1)}\) on those same windows: if \(|F|\) exceeds twice both absolute errors then the two factors have its sign and magnitude at least \(|F|/2\); otherwise the same upper is immediate. The [positive isolation argument](DENSITY_ISOLATOR.md) forces \(|F(x)|\gg_b x^{1+b}\) somewhere in every sufficiently late fixed-multiple interval if there is a zero with \(b>1/2\). This gives the closing contradiction, conditional on the long-shift upper. Under RH the integrated explicit formula gives \(F=O(x^{3/2})\), so that upper would hold after paying both absolute bounds. This comparison accounts for all rows, the insertion weights and both source errors. The critical-scale upper for those remaining rows is open.

The external exponent \(r=0.873346\) gives a present upper for that exact residual. Absolute convergence of the integrated zero expansion and \(\psi-\vartheta\ll \sqrt x\log^2(2x)\) yield \(A_\vartheta(x)=O(x^{1+r})\). Hence \(S_1S_2=O(x^{2+2r})\), and deleting the fully paid families leaves a signed remainder \(O(x^{3.746692})\). If \(B>1/2\), every actual zero real part \(b>1/2\) forces positive remainder \(\gg_b x^{2+2b}\) somewhere in every sufficiently late fixed-multiple window. Indeed \(F\) there has absolute size \(\gg_b x^{1+b}\), both recovery errors are lower order, and both paid families are \(O_\epsilon(x^{3+\epsilon})\) with \(\epsilon<2b-1\). Consequently the remaining arithmetic task is a fixed-power saving on these **jointly long-shift and large-lcm rows**; an exponent \(3+o(1)\) would rule out every such \(b\).

## A forced cancellation among the remaining rows

Use the same semiprime rectangle, denoting its set of products by \(\mathcal T_x\). Now take **all** ordered pairs \(n,m\in\mathcal T_x\) in the cross product. Each contribution is positive. By separation into the two sums and ordinary PNT,
\[
 \sum_{n,m\in\mathcal T_x}f_1(n)f_2(m)
 \sim \frac{x^4}{\log L_1\,\log(x/L_1)}
           \left[\int_a^b\!\int_c^d(1-uv)\,dv\,du\right]^2
 \sim \frac{107584}{382421875}\frac{x^4}{(\log x)^2}.
\]
Here \(f_i(n)=(x-n)b_i(n;x)\). In the first factor only \(p\) carries a log, and in the second only \(q\) carries one. PNT replaces each missing log by \(1/\log L_1\) or \(1/\log(x/L_1)\) at leading order on these fixed-ratio intervals. The double integral is \(82/15625\); \(\log L_1\sim0.11\log x\). Membership in the product rectangle is unique by factorization. The same statements hold with the distributed coefficient lists from the companion row-energy note.

By the two absolute bounds, removing the near-shift and small-lcm pairs changes this subtotal by at most \(x^{3+o(1)}\). Therefore even restricting to the remaining pairs leaves the displayed positive equivalent. The signed sum over *all other remaining pairs* must equal its negative up to \(O(x^{3.746692})\), using the supplied external ceiling. In particular the positive and negative contributions are already known to cancel at leading order on genuine arithmetic data. Bounding that whole sector by absolute values at scale \(x^{3+o(1)}\) is impossible, even if RH holds. The further signed saving needed to reach \(x^{3+o(1)}\) is still unproved.
