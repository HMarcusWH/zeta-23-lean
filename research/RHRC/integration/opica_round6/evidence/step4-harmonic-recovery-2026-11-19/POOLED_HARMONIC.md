# The pooled energy of the literal residue-graph row

**DERIVED on paper.** For integer \(X\ge100\), let \(S_X=\sum_{100\le L\le X}T_L^2/L^4\) with every prescribed sine, cosine, integer part and Möbius coefficient of the literal graph row. If \(B=\sup_\rho\Re\rho\), then
\[
 1+S_X=X^{2B-1+o(1)}
\]
at every integer horizon tending to infinity. In particular, a subpower upper at arbitrarily large horizons (separately for every positive exponent) would suffice. This is a weaker cutoff requirement than an eventual pointwise upper on the scalar row.

To verify the transfer, uniformly on \(L\le y<L+1\) the difference between \(v(y)/y\) and \(2\pi^2 T_L/L^2\) is \(O(1/L)\), by the comparison in POWER_DELAY.md and \(|T_L|=O(L^2)\). The squared discrepancies sum to a bounded number. Apply the triangle inequality for the square-integral norm in both directions. DELAYED_GAIN.md gives \(\int_1^X |v(y)|^2dy/y^2\gg_\rho X^{2\beta-1}(\log X)^{2l-2}\) for every fixed zero of real part \(\beta\) and multiplicity \(l\). Its pointwise upper gives an upper exponent \(2B-1\). The added one deals with the critical case. The nonnegative energy includes both orders of every pair of distinct labels in each row.

## Contributions one can already pay

The complete diagonal of \(S_X\) is \(\kappa\log X+O(1)\), where
\[
 \kappa=\frac{3}{4\pi^6}\int_{24/25}^1 t^2\cos^2(2\pi c/t)\,dt,\qquad c=21/20 .
\]
The squarefree labels coprime to six have counting function \((3/\pi^2)y+O(\sqrt y)\). Indeed, expand \(\mu^2(n)=\sum_{d^2\mid n}\mu(d)\), restrict both \(d\) and its cofactor to integers coprime to six, and use their count \(u/3+O(1)\). The convergent density product is \(\tfrac13\prod_{p>3}(1-p^{-2})=3/\pi^2\). Uniformly in a row, \(W_L(q)=q\cos(2\pi cL/q)/(2\pi^2)+O(1)\). Partial summation against the smooth weight on \([24/25,1]\) gives the diagonal in a single unnormalized square as \(\kappa L^3+O(L^{5/2})\). Division by \(L^4\) and summation give the formula.

Throwing away signs in all pairs with \(0<|q-r|\le H\) costs \(O(H\log(2X))\), since each of \(O(L)\) labels has \(O(H)\) such neighbors, and each product of weights is \(O(L^2)\). One can also pay every primitive ratio with \(\max(q,r)/(q,r)\le U\) at cost \(O(U\log(2X))\). In fact write \(q=du,\ r=dv,\ u<v,\ (u,v)=1\). For each pair, the \(O(dv)\) possible literal cutoffs in which it occurs contribute \(O(1/(dv))\) in total. Summing \(d\le X/v\) and then \(u<v\le U\) proves the estimate. These absolute bounds already meet the cofinal target for subpower \(H,U\). The remaining term is the **signed** sum of long-gap, high-primitive pairs. An eventual or cofinal upper for that sum at every positive exponent on the appropriate horizons is still missing.

## Finite calculation

At \(100\le L\le8192\), the pooled energy was \(0.0000951503891653366892\). The diagonal was \(0.000110571574114076662\), the signed short-gap contribution through gap 16 was \(-0.000008947623552674946\), and the signed long-gap contribution was \(-0.000006473561396065027\). Taking absolute values in the long sector gave \(0.001692587213736206\), over 260 times the magnitude of its signed contribution. A prefix-sum calculation and subtraction from the whole square agreed at every cutoff in 128-bit ball arithmetic. The receipt covers all 409,596 active labels and 13,455,968 unordered pairs across 8,093 cutoffs. These are moderate cutoffs of the exact formula. They precede the later regime in which the selected site lies beyond the already controlled prefix. POOL_CHECK.json records integer counts, enclosures and the precise input.
