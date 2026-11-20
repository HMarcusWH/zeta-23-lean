# Optimal recovery and ordered sign transport for the physical first harmonic

19 November 2026. **DERIVED on paper, with a finite arithmetic check.** The actual Möbius row admits an exact realization of OPICA's joint observation theorem. Complete history inside short cells costs \(O(LH)\) on the true source. What remains is the projection of the cells' signed counts in one explicit unit direction. Step 4 remains open.

The repository baseline is c867a8f15320ad6ac69177e0a498de4cb9d744f9, tree 573cda1f06d2d7a0e61349a53183311e4ba621fc. The one-harmonic sign-exponent theorem used here is a paper result. This pass adds no Lean declaration. Genuine signed harmonic · Actual sign densities

## The two channels and their costs

Let \(n=\lfloor21L/20\rfloor\), \(Q=\{24L/25<q\le L:(q,6)=1,\ \mu(q)\ne0\}\), \(v_q=\mu(q)\), and
\[
 w(q)=\frac{\cos(2\pi n/q)}{2q\sin^2(\pi/q)},\qquad T_L=\sum_{q\in Q}w(q)v_q.
\]
Every selected denominator retains the complete coefficient, including the proved absence of calibration multiples. With \(t=2\pi n/q\),
\[
 w(q)=q\cos(t)/(2\pi^2)+O(q^{-1}),\qquad
 w'(q)=(\cos t+t\sin t)/(2\pi^2)+O(q^{-2}).
\]
Differentiate the analytic factor \(((\pi/q)/\sin(\pi/q))^2=1+O(q^{-2})\), whose derivative is \(O(q^{-3})\). For large \(L\), \(2\pi<t<9\pi/4\) with fixed clearance from the upper endpoint. Hence \(c\le w'\le C\) for absolute positive constants and \(w\asymp L\).

Fix an integer \(H\to\infty\), \(H=o(L)\). Split the interval into successive cells of \(H\) integer sites, shortening the last cell. In each occupied cell let \(q_1<\cdots<q_m\) be its actual squarefree sites, \(\Delta_i=q_{i+1}-q_i\), \(d=\sum_jv_{q_j}\), and \(s_i=\sum_{j\le i}v_{q_j}\), \(1\le i<m\). On the real coordinate space of all selected sites observe \(D=(d_b)_b\), the raw cell sums, and \(C=(\sqrt{\Delta_i}s_i)_{b,i}\), the complete weighted interior prefixes. These are linear observations on any input, specialized below to \(v=\mu\).

The joint observation is bijective by differencing prefixes, including the last prefix \(d\). Finite summation by parts gives its **unique** recovery with the Euclidean measurement norms
\[
 T_L=\langle W,D\rangle+\langle V,C\rangle,\quad
 W_b=w(q_m),\qquad V_{b,i}=-\frac{w(q_{i+1})-w(q_i)}{\sqrt{\Delta_i}}.       \tag{1}
\]
Its optimal operator norm is \(\sqrt{\|W\|_2^2+\|V\|_2^2}\). This instantiates the pinned joint_recovery_iff and joint_recovery_optimal_norm theorems. The counts and square-root gap weights specify the norms in this claim. [JointObservation.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/JointObservation.lean)

Squarefree density gives \(|Q|\asymp L\). There are \(\asymp L/H\) occupied cells since each contains at most \(H\) sites. The sum of interior gaps is bounded above by the length of the slice and below by \(|Q|\) minus the number of occupied cells. Consequently
\[
 \|W\|_2\asymp L^{3/2}/\sqrt H,\qquad \|V\|_2\asymp\sqrt L,\qquad
 \|C(\mu)\|_2\ll H\sqrt L .
\]
The last bound uses \(|s_i|\le H\). In particular \(|T_L-\langle W,D\rangle|\ll LH\). For \(H\le\sqrt L\) set \(u_L=W/\|W\|_2\). For each \(\epsilon>0\), the eventual one-sided upper \(T_L\le C_\epsilon L^{3/2+\epsilon}\) is equivalent to an eventual upper
\[
 \langle u_L,D(\mu)\rangle\le C'_\epsilon \sqrt H\,L^\epsilon.                 \tag{2}
\]
Apply (1) in each direction with the genuine norms. The opposite sign gives its own criterion. For \(H=\lfloor L^\theta\rfloor\), \(0<\theta<1/2\), each sign of the *normalized projection* has upper logarithmic exponent (limsup with \(1+\) the sign part) exactly \(B-1/2+\theta/2\), by the paper sign-exponent theorem for \(T_L\) and \(1+\theta<3/2\le1+B\). The eventual directional inequality (2) remains open.

## What counts alone lose

For any two different sites in one cell the vector \(e_i-e_j\) has zero counts and row value \(w(q_i)-w(q_j)\ne0\). The minimax absolute error from observing only counts on the Euclidean unit ball equals
\[
 \left(\sum_b\sum_{q\in b}(w(q)-\bar w_b)^2\right)^{1/2}\asymp H\sqrt L,
 \qquad \bar w_b=|Q\cap b|^{-1}\sum_{q\in Q\cap b}w(q).
\]
The cell-mean reconstruction attains this error. Two antipodal unit vectors along the component of \(w\) orthogonal to cell constants give its lower bound for every rule. For \(m\) points in a cell, its sum of squared deviations is \((1/m)\sum_{i<j}(w(q_j)-w(q_i))^2\ge c^2m(m^2-1)/12\) since \(q_j-q_i\ge j-i\). Sum over cells and use convexity with \(\sum_bm\asymp L\) and \(O(L/H)\) cells. Lipschitz continuity gives the upper bound. These arbitrary unit witnesses test the observation operator; (2) concerns the actual arithmetic vector.

## Ordered transport on real labels

In each cell, list the true positive and negative atoms in increasing order. Append \(|d|\) copies of the last occupied location to the list of the missing sign; these endpoint entries represent the count observation. Match by rank. Exactly \(|s_i|\) pairs cross the \(i\)th gap: the two cumulative list lengths differ by \(s_i\) and ordered matching crosses a cut in only one direction. Total displacement, including endpoints, is therefore precisely \(\sum_{b,i}\Delta_i|s_i|\). In the increasing physical coordinate \(w\), the same identity gives \(\sum_{b,i}(w(q_{i+1})-w(q_i))|s_i|\). For every pairing cumulative discrepancy gives a lower bound on crossings, so both costs are minimal. The latter bounds the absolute value of the signed history in (1).

At \(L=2^{26}\), \(n=70{,}464{,}307\), \(H=\lfloor L^{2/5}\rfloor=1351\), the 1,987 occupied cells contained 815,927 real labels. The 391,705 opposite-sign pairs had median distance 52, 99th percentile 252 and maximum 408. Their signed contribution was \(+1234.8353925393737\). The remaining 16,135 positive and 16,382 negative labels contributed \(-941237150.16647626\), for a full row of \(-941235915.33108372\). Displayed decimals are rounded; the receipt stores enclosures.

The real-pair and endpoint displacement totals were 26,577,410 and 2,549,610. Their sum **exactly** equals the independently computed cumulative-discrepancy cost 29,127,020. Formula (1) gave \(-941239094.60796734\) from the counts and \(+3179.27688362314\) from all prefix histories. The history-channel norm was approximately \(319.207\); the count-channel norm was approximately \(133562611.0954\). The total overlapped the previously computed direct full-row interval. This comparison covers one native cutoff. [Reproduce the calculation](check_ground_transport.py) · [128-bit Arb receipt](GROUND_TRANSPORT_CHECK.json) · Earlier independent row calculation

The same two computations enclose the physical absolute transport cost at 5,642,031.516762118, of which 5,147,480.547752068 came from real pairs. The much smaller signed history above measures cancellation across these oriented displacements.

## Ground and source-contract comparison

The pinned nativeSignedPrimeDiscrepancy sums the prime-power source against correctedSourceTest and subtracts its continuum integral. The strict-even conclusion evaluates the corrected functional on the specified shifted eigenray. In the strict-odd branch nativeOddReciprocalInput carries the arithmetic, its distinct eigenray carries absolute energy, and the tied branch retains kernel and complement terms. These declarations supply no identification of \(u_L,D(\mu)\) with those vectors. A bridge would need the actual source map, its measurement norms, and a quantitative bound on the signed projection (2). [GroundArithmetic.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICARound4/GroundArithmetic.lean) · [JointGroundConstraints.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICARound4/JointGroundConstraints.lean)

The Drive source-contract review specifies the full physical weighted upper U, the actual-core relative loading F at centered horizon \(L/2\), and the selected-predecessor complement E at translated horizon \(L-2c_0\). Each retains an independent arithmetic premise. In particular, a cofinal scalar bound from U does not give the eventual one-sided estimate for this row by direct identification. Equation (1) supplies an optimal recovery for the specified two data channels in their actual norms. Its all-late directional estimate is the missing arithmetic. Source contracts for U, F and E · Merged results and remaining obligations
