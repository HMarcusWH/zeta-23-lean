# Removing all prime and balanced squarefree semiprime cofactors

**DERIVED on paper.** In each original outer-prime observation one can keep every prime-cofactor label **and** every label with cofactor \(j=uv>L\), \(u<v\) primes, \(u\ge j^{97/200}\). Additional positive squarefree two- and three-factor labels pay their joint signed mass to accuracy \(2x\log x\). This is a new selection; it must be used consistently on both sides. Step 4 remains open.

Use the same native factorial and eta sums, true cutoffs \(L=\lfloor x^{.11}\rfloor\) or \(\lfloor x^{.37}\rfloor\), and averaging over calibration bases divisible by 9 as in [the prime-only proof](ALL_PRIME_COFACTORS.md). At a given real \(x\), outer prime \(q\) and \(Y=x/q\), the label weight is \((x-qj)\log(q)\,r(j)\) for \(j\le Y\). It vanishes for \(j\le L\). On squarefree \(j>L\) each filter has the exact coefficient
\[
 r(j)=-\sum_{d\mid j,\ d\le L}\mu(d)
      =-\sum_{\substack{d\mid j/\ell\\L/\ell<d\le L}}\mu(d)
\]
for each prime \(\ell\mid j\), by pairing the divisors \(d\) and \(\ell d\). In particular \(r(uv)=\mathbf1_{u\le L}+\mathbf1_{v\le L}-1\). The balanced semiprimes in the assertion therefore have coefficient \(-1,0,\) or \(+1\); every sign is mandatory. Equal products with different outer labels are counted separately.

## How much the added labels can cost

Write \(\theta=97/200\) and \(\kappa=\log((1-\theta)/\theta)=\log(103/97)<0.061\). The number \(N(z)\) of products of distinct primes \(u<v\) with \(uv\le z,\ u\ge(uv)^\theta\) satisfies
\[
 N(z)\sim\kappa\,\frac z{\log z}.
\]
Indeed \(v\le\min(z/u,u^{(1-\theta)/\theta})\). Primes \(u<z^\theta\) contribute \(O(z/\log^2 z)\) by summing the prime counting upper bound \(O(u^{(1-\theta)/\theta}/\log u)\) over primes and using partial summation. On \(z^\theta\le u\le\sqrt z\), removing the cases \(v\le u\) costs \(O(z/\log^2 z)\) by the same argument. Ordinary PNT applies uniformly to the remaining upper endpoint \(z/u\ge\sqrt z\). Partial summation in the first prime gives the logarithmic integral \(\int_\theta^{1/2}dt/[t(1-t)]=\kappa\). This argument retains all product scales including the bottom of the ramp. [Ordinary prime number theorem](https://dlmf.nist.gov/25.16.E3)

Integrating \(N(z)\) from 0 to \(Y\) and multiplying by \(q=x/Y\) gives the actual linear-ramp mass of every balanced semiprime before \(r(j)\) and before the outer log. It is \((\kappa+o(1))A_q\), where \(A_q=xY/(2\log Y)\). The error is uniform on the native outer set since its minimum \(Y\) tends to infinity. Thus **each** of its positive and negative mandatory masses, including the cut \(j>L\), is less than \(0.061A_q\) for all sufficiently large \(x\). The full prime mass before that cut is \((1+o(1))A_q\). All per-fibre quantities here and below are multiplied by the same positive factor \(\log q\).

## Spend the strict composite surplus

For \(Y\ge100L\) the exact 400-cell-grid lower bound for the full positive two-/three-factor candidate population in \(.01Y<j\le.99Y\) is \(1.088335060\) before the ramp endpoint loss. The retained first moment has factor \(2\int_{.01}^{.99}(1-t)dt=.98\). Thus the supply is at least \(1.0665A_q\) eventually, uniformly in the native fibres. All available positive two-/three-prime labels can be used, including balanced semiprimes. [Integer calculation](check_full_prime_cofactor_supply.py) · [Grid results](FULL_PRIME_COFACTOR_SUPPLY.json)

Let \(P_q^-\) denote the true prime deficit, \(B_q^\pm\) the mandatory balanced masses with their respective signs, and \(C_q\) the supply of **all** positive two-/three-factor candidates. In an eligible bulk fibre \(C_q\ge1.0665A_q\), while \(P_q^-+B_q^-\le1.061A_q\) eventually, using the strict inequality \(\kappa<.061\) to absorb PNT errors. The outstanding debt after including mandatory positives is \(P_q^-+B_q^--B_q^+\). The available optional supply is \(C_q-B_q^+\). The comparison above proves that the latter covers the former without double-counting a label. This arithmetic uses the full \(1.088335060\) lower sum.

Fix \(B=e^{4000}\). For \(Y\ge BL\) the missing prime prefix \(j\le L\) costs at most \(x\pi(L)\le(7/B)A_q\) eventually, since \(\log Y/\log L\le1/.30\). Consequently \(P_q^-+B_q^--B_q^+>0\) at every such \(q\). For a practical finite selector, charge all mandatory labels in each such fibre in ascending outer-prime order. While the running signed sum is negative, add optional positive labels in ascending cofactor order through its first nonnegative value. Each candidate weighs at most \(2x\log x\). The nonnegative outstanding debt prevents an already-positive prefix balance from increasing when mandatory labels alone are charged; the surplus ensures the required correction exists. At each completed bulk prefix the balance lies in \([0,2x\log x]\).

Group the terminal fibres \(L<Y<BL\) together. If \(a,b\) are fixed, \(1\le a<b\), summing \(A_q\log q\) over \(aL<Y<bL\) gives \((\log(b/a)+o(1))x^2/(2\log L)\) by PNT on the true outer interval. The open upper cutoff \(Y>L+1\) affects only lower order terms. In these units the full terminal prime and mandatory negative debt is at most \(1.061\log B+o(1)\). The positive supply from \(100L\le Y<BL\) alone is at least \(1.0665\log(B/100)+o(1)\), strictly larger:
\[
 (1.0665-1.061)4000-1.0665\log100>17 .
\]
If a forced positive lies outside this supply, it increases the available total. Inside the supply it is counted once, as above. The terminal outstanding debt is also positive: on \(100L\le Y<BL\) the prime prefix estimate, now with \(7/100\) in place of \(7/B\), leaves \(P_q^->0.92A_q\) for large \(x\); mandatory positive mass throughout the entire terminal range is bounded by \(0.061\log B+o(1)\) in these units. In particular \(0.92\log(B/100)>0.061\log B\). Apply the stopping rule to this one terminal group, using the lexicographic order of the optional labels from \(100L\le Y<BL\). No uniform terminal per-fibre payment is required.

## Resulting signed remainder and numerical controls

Write \(D_i\) for the complete signed charge in observation \(i\), and \(T_i\) for its other labels. Then \(0\le D_i\le2x\log x,\ S_i=D_i+T_i,\ T_i=F+o(x^{3/2})\) at the same real \(x\). Here \(F=\int_2^x(\vartheta(t)-t)\,dt+(2/3)x^{3/2}\) with the same external ceiling needed by the original factorial source. The covariance difference \(S_1S_2-T_1T_2\) is \(O(x^{3+o(1)})\) by the existing absolute label-sum bounds, or \(O(x^{2+r}\log x)\) using \(F=O(x^{1+r}),\,r=.873346\). The proved absolute near-shift and small-lcm estimates continue to hold on the remaining labels. All remaining nonzero cofactors are composite; each remaining squarefree two-prime cofactor has a prime factor below \(j^{97/200}\). Repeated prime powers and calibration nodes remain. The true unequal-factor examples \(2p\) and \(6p\) from the prime-only analysis still test the remaining range. A signed upper on the remaining long-shift and large-lcm covariance is open.

The [finite checker](check_true_cofactor_removal.py) uses the exact source's open outer intervals and distributed calibration bases at explicitly selected finite cutoffs. On every squarefree cofactor it computes \(r(j)\) directly by signed divisor enumeration. All negative prime labels are counted. The second check includes every active balanced semiprime of either sign and removes its positive contribution from the optional pool. For two passing configurations the respective total nonzero prime-label counts in the factorial and eta lists are \(28{,}682\) and \(49{,}359\) at \(x=200003,(L_1,L_2)=(31,121)\), and \(47{,}291\) and \(71{,}995\) at \(x=300007,(89,160)\). The corresponding additional balanced-label counts, including zero coefficients, are \(498,1883\) and \(1396,2883\). The two insufficient factorial pools at \(x=100003,L_1=20\) and \(x=300007,L_1=41\) are preserved. The horizon-dependent power laws and eventual thresholds in the paper theorem are separate from these finite fixtures. All row masses before log weights are exact integers; the actual log sums use outward enclosures. [Finite results](TRUE_COFACTOR_REMOVAL_CHECK.json)

No Lean compilation or new proof-validation gate is claimed.
