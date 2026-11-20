# Two-sided prime-gap restrictions at a high primorial score

**DERIVED on paper.** To test the missing upper one can discard even some of the stopped vertices of the prime graph. It suffices to keep only the primes whose cumulative mass \(z=\vartheta(p)\) obeys both
\[
 p+\tfrac12\log p\ \le z\ \le p^+-\tfrac12\log p^+ .                 \tag{1}
\]
In particular a gap shorter than the average of the logarithms of its two endpoint primes can be discarded. This deduction uses real changes of the squarefree integer, including their effect on its log mass.

Write \(D(P)=(\log P)^2/2-\sum_{q\mid P}q\log q+2\) and let \(P=\prod_{q\le p}q\). Write \(z=\log P\). Removing \(p\) or adjoining \(p^+\) gives the exact increments
\[
 D(P/p)-D(P)=\log p\,(p-z+\tfrac12\log p),\qquad
 D(Pp^+)-D(P)=\log p^+\,(z-p^++\tfrac12\log p^+).
\]
Thus every interior maximum in the graph of successive primorial scores satisfies (1).

## Existence on the relevant scales

Suppose a nontrivial zero has \(\Re\rho=b>1/2\). Use [the fixed-multiplier isolator](DENSITY_ISOLATOR.md) to choose **five** successive points with area signs \(+,-,+,-,+\), one in each of five consecutive multiplicative windows beginning at \(2X\). Their absolute areas are \(\gg_b X^{1+b}\). Minimize the actual continuous area on the interval from point 1 to point 3, and again on the interval from point 3 to point 5. Both minima are interior and very negative. Inside an open prime gap the area is strictly concave, so each minimum is located at a prime \(q\). Its one-sided derivatives imply
\[
 0\le\vartheta(q)-q\le\log q .
\]
Completing the square gives \(D(\prod_{\ell\le q}\ell)=A(q)+(\vartheta(q)-q)^2/2\), so the primorial scores at both minima remain strictly negative. This step controls the discrete scores at the ends even when the supremum of zero real parts equals 1.

At the middle positive point \(x\), the primorial through \(x\) has score \(A(x)+(x-\vartheta(x))^2/2\ge A(x)\). Its prefix is strictly between the two negative-score prefixes (equality with either contradicts the score signs). The maximal primorial score between those two bounding primes is therefore interior and \(\gg_b X^{1+b}\). Select one maximizer \(P\). Its prime \(p\) obeys (1) and remains in \([X,C_bX]\) for a fixed \(C_b\). The sign-window constants were fixed before \(X\). No zero attaining the supremum was assumed.

Consequently the limit in [the stopped-prime criterion](STOPPED_PRIME_GRAPH.md) is unchanged if only vertices satisfying (1) are used. Under RH every such score is negative by the actual prime-area criterion. For the opposite case, the preceding construction gives the lower estimate for every actual \(b>1/2\); the upper follows from the original stopped-vertex bound.

## Longer prime-factor exchanges

Let \(T\) consist of the last several consecutive prime factors of \(P\) or the next several primes above its largest prime. If removing or adjoining all of \(T\) stays inside the two bounding primorials, maximality gives
\[
 \sum_{q\in T}|q-z|\log q\ \ge\
        \tfrac12\left(\sum_{q\in T}\log q\right)^2.                   \tag{2}
\]
For removals, expand \(D(P/\prod_{q\in T}q)-D(P)\) as in the [squarefree calculation](SQUAREFREE_COST.md). For additions use \(D(P\prod_{q\in T}q)-D(P)=
 -\sum_{q\in T}(q-z)\log q+\tfrac12(\sum_{q\in T}\log q)^2\). The signs inside the absolute values follow from (1). The inequalities retain all individual prime factors, the quadratic terms and both sides of the gap. A high-score counterexample must satisfy these restrictions simultaneously through both bounding minima. Their derivation supplies no upper on the prior cumulative signed first moment. A mere gap-size estimate leaves that quantity open.
