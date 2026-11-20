# Matching opposite prime-factor parities in the actual harmonic row

**DERIVED on paper, 19 November 2026.** For every large integer cutoff \(L\), all but \(O_A(L/\log^A L)\) of the actual nonzero denominators of the one-harmonic row can be put into disjoint opposite-sign pairs whose **total absolute weighted error** is \(O_\eta(L^{4/3+\eta})\), for any fixed \(0<\eta<1/6\). Each pair agrees on divisibility by every prime up to \(\log\log L\). A second construction puts all but \(O(L/(\log\log L)^{1/400})\) into such pairs at a total error \(O(L\log^6 L)\). Both constructions include the unmatched denominators, with their original weights and signs, in the exact identity for the complete row. The sign of their aggregate remains the unresolved arithmetic issue.

## Source, signs and transfer cost

Put \(a=24/25,\ c=21/20,\ n=\lfloor cL\rfloor,\ I=(aL,L]\). On real \(u\in[aL,L]\) set

\[
 W_L(u)=\frac{\cos(2\pi n/u)}{2u\sin^2(\pi/u)}.
\]

The [native row and its zero-detection proof](../step4-native-residual-2026-11-19/ONE_HARMONIC_ZERO_DETECTOR.md) give \(T_L=\sum_{q\in I,(q,6)=1}\mu(q)W_L(q)\). Every \(q\) is counted once, with both conjugate numerators absorbed into \(W_L\). For large \(L\), \(1<n/u<9/8\) throughout the band. Thus \(W_L\asymp L\) and \(\sup_I |W_L'|\ll 1\) uniformly. Indeed \(1/(2u\sin^2(\pi/u))=u\,b(\pi/u)/(2\pi^2)\) with \(b(t)=(t/\sin t)^2\) smooth at 0, while the derivative of the cosine is \(O(n/u^2)=O(L^{-1})\). An opposite-sign pair \(q_+,q_-\) within distance \(H\) therefore contributes an exact difference \(W_L(q_+)-W_L(q_-)\) of magnitude \(O(H)\).

The number of eligible nonzero labels is \(((1-a)/(2\zeta(2))+o(1))L\). The squarefree identity \(\mu^2(q)=\sum_{j^2\mid q}\mu(j)\) and the restriction \((q,6)=1\) give density \((1/3)\prod_{p\ge5}(1-p^{-2})=1/(2\zeta(2))\). All zero coefficients vanish exactly.

Set \(z=\log\log L,\ P=\prod_{5\le p\le z}p,\ Q=6P\), where all products indexed by \(p\) are over primes. By the ordinary prime number theorem \(Q\ll(\log L)^2\) for large \(L\). Matching two nonzero coefficients which have the same \(d=(q,P)\) preserves all their small-prime divisors. Their opposite Möbius signs then arise from opposite parities among their remaining prime factors.

## A fixed grid leaving fewer than every fixed logarithmic fraction

Fix \(H=\lfloor L^{1/3+\eta}\rfloor\) and partition the number line into the fixed cells \((jH,(j+1)H]\). Intersect each cell with \(I\). In each cell and each of the residue classes modulo \(Q\) coprime to 6, match the positive labels in increasing order to the negative labels in increasing order until one list is exhausted. This prescription is fixed before any estimate. The number left in a class is the absolute value of the unweighted Möbius sum on that arithmetic progression. The number of eligible classes is at most \(Q\).

Use Theorem 1.1(i) of Matomäki, Radziwiłł, Shao, Tao and Teräväinen with constant phase and fixed complexity. For windows \((x,x+2H]\) and \(X=L/2,\ x\in[X,2X]\), the maximum absolute Möbius sum over **all arithmetic progressions contained in the window** is \(O_{A'}(H/\log^{A'} L)\), outside a set of measure \(O_{A',\eta}(L/\log^{A'} L)\). Its length hypothesis holds with, for example, half the chosen \(\eta\) as slack above \(1/3\). [Theorem 1.1(i) and the maximal norm, equations (1.4)–(1.5)](https://arxiv.org/html/2411.05770v2#S1.Thmtheorem1)

For each cell meeting \(I\), every \(x\in(jH-H,jH]\) gives a window containing the entire cell. These preceding intervals are disjoint, and lie inside \([L/2,L]\) for large \(L\). If a cell contains any progression violating the stated bound, its entire preceding interval belongs to the exceptional set. Hence there are \(O_{A',\eta}(L/(H\log^{A'}L))\) such cells, with at most \(H\) unmatched integers each. A good cell leaves at most \(O_{A'}(QH/\log^{A'}L)\). Clipping the endpoint cells to \(I\) preserves the progression property. Summing and choosing \(A'>A+3\) yields

\[
  \#U_L\ll_{A,\eta} L/\log^A L\qquad\text{for every fixed } A>0.       \tag{1}
\]

The same grid and matching work for all fixed \(A\). Opposite labels in a matched pair are at distance less than \(H\), and there are at most \(L\) pairs. Writing \(D_L\) for the exact signed sum of their weight differences gives

\[
 |D_L|\le\sum_{\rm pairs}|W_L(q_+)-W_L(q_-)|\ll_\eta L^{4/3+\eta},
 \qquad
 T_L=D_L+\sum_{q\in U_L}\mu(q) W_L(q).                                  \tag{2}
\]

In particular almost all of the order-\(L^2\) absolute mass is in the paired part, and its signed error is smaller by a fixed power than \(L^{3/2}\). The logarithmic exceptional-set estimate was used on a short grid inside **every** native cutoff.

## A polylogarithmic matching distance

For a shorter matching distance take \(H_0=\lfloor\log^6 L\rfloor\) and allow a separate internal grid for each \(d\mid P\). On eligible squarefree labels with \((q,P)=d\) write \(q=dm\). Their full signed indicator in \(m\) is \(\mu(d) f_P(m)\), where

\[
 f_P(m)=\mu(m)\mathbf1_{(m,6P)=1}.
\]

This is a real multiplicative function with values in \([-1,1]\). Its long mean is uniformly smaller than every inverse power of \(\log L\) on the scales \(x\asymp L/d,\ d\mid P\). To check uniformity, the exact Dirichlet coefficient identity gives

\[
 \sum_{m\le x} f_P(m)=\sum_{\substack{k\le x\\p\mid k\,\Rightarrow\,p\mid 6P}} M(x/k),
 \qquad M(y)=\sum_{n\le y}\mu(n).
\]

Use the classical PNT bound \(M(y)\ll_A y/\log^A(2y)\) for \(k\le\sqrt x\). Its cost is bounded by \(O_A(x\log^{-A}x\prod_{p\mid6P}(1-p^{-1})^{-1})\). The product is \(O(\log(2z))\) by Mertens' product theorem. For \(k>\sqrt x\) use \(|M(x/k)|\le x/k\) and \(1/k\le x^{-1/4}k^{-1/2}\); the cost is \(O(x^{3/4}\prod_{p\mid6P}(1-p^{-1/2})^{-1})=O(x^{3/4}\exp(O(\sqrt z)))\). Since \(d\le P\ll\log^2L\), these bounds give the claimed uniform long mean.

Let \(h_d=\lfloor H_0/d\rfloor\). We have \(\log h_d\asymp\log\log L\) uniformly. Apply Theorem 1 of Matomäki and Radziwiłł with \(X=L/(2d)\) (rounding \(X\) down if needed and changing an endpoint by at most one). Their constants are uniform in the real multiplicative function. With \(\delta=(\log h_d)^{-1/200}\), all but \(O(X(\log h_d)^{-1/100})\) integer starting points have their normalized \(h_d\)-term sum within \(O((\log h_d)^{-1/200})\) of the long mean. A half-open window changes the sum by at most one. Using the trivial bound on exceptional shifts and the long mean bound gives

\[
  \sum_{X\le s\le 2X}
  \left|\sum_{s<m\le s+h_d} f_P(m)\right|
  \ll Xh_d(\log h_d)^{-1/200}.                                        \tag{3}
\]

This applies even though the long sum varies with \(P\). [Matomäki–Radziwiłł, Theorem 1 and its explicit parameter choice, pp. 1015–1016](https://annals.math.princeton.edu/wp-content/uploads/annals-v183-n3-p06-p.pdf)

Partition \(I/d\) into \(h_d\)-site cells, selecting the least offset modulo \(h_d\) minimizing the total unpaired count. Within a cell use the same increasing-list matching for \(f_P\). For the full cells, average their absolute unweighted imbalances over all \(h_d\) offsets. Each admissible starting point occurs once in the numerator of this average, so (3) bounds the average by \(O((L/d)(\log h_d)^{-1/200})\). Each offset has at most two clipped cells, costing at most \(2h_d\) additional labels. The minimizing offset obeys this bound, with a harmless endpoint cost if \(L/d\) is nonintegral. This chooses only a finite grouping of source terms. All cutoff values and all labels are retained.

Over the disjoint classes \(d\mid P\), use \(\sum_{d\mid P}1/d\le\prod_{p\le z}(1+1/p)\ll\log(2z)\). Absorbing that factor and the two boundary cells in the logarithmic saving gives

\[
  \#U_L^{\rm short}\ll L/(\log\log L)^{1/400},
  \qquad \sum_{\rm short\ pairs}|W_L(q_+)-W_L(q_-)|\ll L\log^6 L .       \tag{4}
\]

The distance in the original denominator is at most \(d h_d\le H_0\). Each matched pair has the identical complete small-prime pattern \(d\). In (1), pairs actually agree modulo the entire \(Q\).

## Why a fixed prime-factor pattern retains the zero obstruction

Here keep the squarefree product \(P\) of primes at least 5 fixed and keep one exact small-prime divisor pattern \(d\mid P\). For the homogeneous row with indicator \((q,6)=1,\ (q,P)=d\), write \(q=dm\) as above. If \(m(s)=\int_1^{1/a}\cos(2\pi c v)v^{-s-1}dv\), its Mellin transform on \(\Re s>2\) is exactly

\[
 \frac{\mu(d)d^{\,1-s}m(s)}
 {\zeta(s-1)\displaystyle\prod_{p\mid6P}(1-p^{\,1-s})}.                 \tag{5}
\]

This follows from the original row transform by replacing the coefficient Dirichlet series by \(\mu(d)d^{1-s}\sum_{(m,6P)=1}\mu(m)m^{1-s}\). Each removed Euler factor is nonzero on \(\Re s>1\). The [strictly decreasing kernel proof](../step4-native-residual-2026-11-19/ONE_HARMONIC_ZERO_DETECTOR.md) shows \(m(1+\rho)\ne0\) for every nontrivial zeta zero. The floor and exact sine normalization contribute the same \(O(L)\) comparison as for the full row. Thus **every fixed complete pattern individually** has both sign limsup exponents \(1+B\), where \(B=\sup_\rho\Re\rho\). The upper follows by the same finite-prime inverse convolution, the lower for each sign by the real-axis Landau argument of the linked note. This fixed-\(P\) conclusion does not require any uniformity as \(P\) grows.

Equations (1)–(2) give a further explicit constraint. For the deterministic unmatched weighted sum in (2), each sign still has limsup exponent \(1+B\), because \(4/3+\eta<3/2\le 1+B\). The same holds for the alternative unmatched sum in (4). In particular, along some unbounded cutoffs the number of unmatched positive labels is at least \(L^{B-o(1)}\), and along some unbounded cutoffs so is the number of unmatched negative labels, since each label weighs \(O(L)\). The two sequences need not coincide.

An eventual one-sided \(O_\epsilon(L^{3/2+\epsilon})\) upper for the **signed weighted unmatched sum** suffices for Step 4 along this detector. Taking absolute values of all unmatched terms pays at most \(O_A(L^2/\log^A L)\) by (1), which still exceeds the required power. Keeping small-prime allocations and pairing almost all true terms has isolated the remaining signed discrepancy. Its critical estimate, Step 4 and RH remain **OPEN**.
