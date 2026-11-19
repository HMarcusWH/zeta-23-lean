# Localizing both signed observations to one short interval of integer products

19 November 2026. **DERIVED on paper. Step 4 OPEN.** This construction keeps the two native four-moment filters, their outer-prime cutoffs and their common real horizon. For each filter one can select actual labels, each with its original weight, whose sum agrees with the *complete* signed source to \(O(x^{0.9932}\log x)\). Every selected product lies in the same interval
\[
 \mathcal I_x=[x-2x^{0.9932},\,x-x^{0.9932}].
\]
Every selected cofactor is squarefree with two, three, four or five prime factors. In the two-factor case the smaller is below \(j^{.485}\). Every pair of selected products at distance at most \(x^{.053}\) is paid in absolute value at the critical covariance scale. This strengthens the earlier subpower distance cutoff. The selector reads the actual signed fibre sums. Its output is a representation of those sums and keeps the missing arithmetic dependence.

## Sign and size of the available labels

Use the same distribution over centres divisible by 9 as in [the prime-cofactor matching proof](ALL_PRIME_COFACTORS.md), and the uniform estimate in [the full variation proof](FULL_OUTER_VARIATION.md). For either \(i\), abbreviate \(L=L_i,\ Y=x/q,\ \alpha=\log L/\log Y,\ d=.0068,\ w=x^{1-d}\). Let \(G_q=K_{i,x}(q)\log q\) denote the full signed fibre. With \(s=.874\) from the [pinned external ceiling](https://github.com/GTimG/QuasiRiemannTracker/blob/42cf5415cfaa4205caaa25ab11160724606cdc33/submissions/2026-11-13-continuum-exact-contact/src/Candidate/Main.lean),
\[
 |G_q|\ll xY L^{s-1}\log^2 x\,\log q.
\]
For \(Y\ge4L\) one has \(.30\le\alpha<1\) for all sufficiently large \(x\). The requirement \(qj\in\mathcal I_x\) gives \(j/Y\in[1-2x^{-d},1-x^{-d}]\), so \(j>L\).

| Desired sign | Range of \(\alpha\) | Number \(k\) of distinct cofactor primes | Highest order \(m\) of a proper factor product at most \(L\) | Actual \(r_i(j)\) |
|---|---:|---:|---:|---:|
| Positive | \([.30,.45]\) | 4 | 1 | 3 |
| Positive | \([.45,.60]\) | 3 | 1 | 2 |
| Positive | \([.60,1]\) | 2 | 1 | 1 |
| Negative | \([.30,.44]\) | 2 | 0 | −1 |
| Negative | \([.44,.56]\) | 5 | 2 | −6 |
| Negative | \([.56,.72]\) | 4 | 2 | −3 |
| Negative | \([.72,1]\) | 3 | 2 | −1 |

At shared endpoints either adjacent construction works. For two primes require \(.46<\log p_1/\log Y<.47\). For \(k\ge3\) fix \(\epsilon_0=.001\) and put the exponents of the first \(k-1\) primes in the open intervals
\[
 (1/k-(k-a)\epsilon_0,\ 1/k-(k-a)\epsilon_0+\epsilon_0/4),
 \qquad a=1,\ldots,k-1 .
\]
The final prime is the largest, with exponent \(1-\sum_{a<k}\log p_a/\log Y+o(1)\). For \(k\ge3\) every exponent lies between \(1/k-.0041\) and \(1/k+.0101\). Checking the displayed intervals shows that all subsets of at most \(m\) primes have product \(\le L\) and all larger subsets have product \(>L\). In the last and third lines one uses \(j>L\) for the complete subset. Thus the actual coefficient is \(-\sum_{e=0}^m(-1)^e\binom{k}{e}=(-1)^{m+1}\binom{k-1}{m}\) as displayed. The ordering prevents multiple counting. A repeated prime between the outer prime and its cofactor is allowed.

For each choice of the first \(k-1\) primes, set \(Z=Y/\prod_{a<k}p_a\). Since \(k\alpha\le3\) in every table row and the preceding exponents sum to less than \(1-1/k\), one has \(Z\ge Y^{1/k}\ge L^{1/3}\). The interval for the final prime has length \(Zx^{-d}\) at height \(\asymp Z\). As \(Z\ge x^{.11/3-o(1)}\), this length exceeds \(Z^{.80}\) for all large \(x\). The Guth–Maynard short-interval estimate yields \(\gg Zx^{-d}/\log Z\) true primes uniformly. If the interval is longer than the stated upper range of their corollary, partition it into comparable lengths \(\asymp Z^{.9}\), all inside that range. [Guth and Maynard, Corollary 1.3](https://ora.ox.ac.uk/objects/uuid%3Aad11b8bf-ad2b-4ebf-a627-647f023c378f/files/s73666708v)

The reciprocal prime mass in each of the fixed preceding exponent intervals tends to a positive constant by ordinary PNT. Hence for either sign there are \(\gg Yx^{-d}/\log Y\) genuine eligible labels at every such \(q\). Each has ramp at least \(w\). Their total absolute mass, including the outer log, is at least \(c xY x^{-2d}\log q/\log Y\) for one fixed \(c>0\). This exceeds \(|G_q|\) for all sufficiently large \(x\) because \(2d=.0136<.11(1-.874)=.01386\). Every label has absolute mass at most \(W=12w\log x\), allowing the largest ramp \(2w\) and coefficient 6.

## Signed rounding with the complete source

Process all \(q\) with \(Y\ge8L\) in increasing order. Keep the difference between the selected sum and the complete original sum, denoted \(E\), in \([0,W]\). At a new prime first subtract \(G_q\) from \(E\). If the result is negative, add positive eligible labels, in increasing cofactor order, until it reaches zero or becomes positive. If it exceeds \(W\), add negative eligible labels in the same order until it is at most \(W\). Each demand is at most \(|G_q|\), and each step has magnitude at most \(W\). This proves the invariant, uses at most one sign per fibre, and never splits an arithmetic coefficient.

Pool all remaining outer primes \(L<Y<8L\) into a single group, including the original upper cutoff \(Y>L+1\). Its total full signed mass has magnitude \(O(x^2 L^{s-1}\log^2 x)\) by the per-fibre estimate and \(\sum_{q:\,L<Y<8L}\log q/q=O(1)\). Within this same group use eligible labels **only** at \(4L\le Y<8L\). Each sign supplies \(\gg x^{2-2d}/\log x\) by summing the lower bound on the fixed-ratio outer-prime interval. The preceding strict exponent comparison pays the full group. The same rounding rule with lexicographic label order completes the construction. All original labels with \(Y<4L\), including the complete first dyadic band, have been accounted for.

Writing \(T_i\) for the selected sum and \(S_i\) for the original, \(0\le T_i-S_i\le W\). On every earlier outer prefix the same bound holds. The discarded sum and its mixed pairs are retained in the exact identity \(S_1S_2=T_1T_2+(S_1-T_1)S_2+T_1(S_2-T_2)\). Its last two terms together cost \(O(x^{3-d+o(1)})\) even with only the original \(x^{2+o(1)}\) absolute label bounds. In particular, the earlier large positive terminal-composite subtotal poses no contradiction. Its compensation is part of this different, explicit selection.

## A fixed power of product shifts is paid

For each fibre or terminal group \(g\) the absolute mass selected is at most \(|G_g|+W\), because all selected labels there have one sign and the input and output balances differ by at most \(W\). With \(\mathcal T_2\) the full selected eta list, this gives
\[
 \sum_{\ell\in\mathcal T_2}|g_2(\ell)|
 \le V_2(x)+O\big(W(1+x/L_2)\big)
 \le x^{2-.37(1-.874)+o(1)}.
\]
There are at most \(\tau(n)\) possible outer labels at product \(n\), each of magnitude \(O(w\log x)\). Thus the total absolute factorial label mass at any particular product is at most \(x^{1-d+o(1)}\). For \(H=x^{.053}\), the entire absolute selected covariance with \(|n-m|\le H\), counting all overlaps and repeated products, is at most
\[
 (2H+1)x^{1-d+o(1)}x^{2-.37(1-.874)+o(1)}
 =x^{2.99958+o(1)}.
\]
For the complementary shifts there is also a stronger small-lcm payment. For \(u=\operatorname{lcm}(n,m)\) there are at most \(\tau(u)^2\) ordered product pairs. Multiplying by the two absolute labelwise product bounds yields at most \(x^{2-2d+o(1)}\) at each \(u\le x^2\). Consequently the complete absolute selected covariance with \(\operatorname{lcm}(n,m)\le x^{1+2d}\) costs at most \(x^{3+o(1)}\). Both estimates survive on arbitrary intersections.

**OPEN.** The only pairs left by this construction have
\[
 n,m\in\mathcal I_x,\qquad
 x^{.053}<|n-m|\le x^{.9932},\qquad
 \operatorname{lcm}(n,m)>x^{1.0136}.
\]
They use the specified adaptive labels, both sets at the same horizon. A one-sided \(x^{3+o(1)}\) upper on their signed sum on arbitrarily late complete windows would give the original contradiction by the two simultaneous reconstructions. The support calculation alone does not control that signed sum. The existing external upper on it is \(O(x^{3.746692})\). [Closing transfer](../step4-area-runs-2026-11-19/SHARED_PRODUCT_COVARIANCE.md)
