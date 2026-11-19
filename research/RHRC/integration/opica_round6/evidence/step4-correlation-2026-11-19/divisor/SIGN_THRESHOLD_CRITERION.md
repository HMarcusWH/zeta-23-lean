# A sign test at the sharp sieve threshold

**Paper consequence of the [sharp rough-core energy calculation](ROUGH_CORE_PHASE_TRANSITION.md).** This gives a criterion for Step 4 involving only the sign of a complete, genuine covariance at selected cutoffs. For \(A=8\) that sign already follows unconditionally at arbitrarily late windows. The same sign near the quadratic sieve threshold remains open.

On the literal positive native terminal array define
\[
 Q_n=\sum_iw_i P(t_i)^2,\qquad
 \mathcal E_{y,n}=\sum_iw_i\sum_r c_{r,y}(t_i)^2,\qquad
 \mathcal R_{y,n}=\sum_iw_i\sum_{r\ne r'} c_{r,y}(t_i)c_{r',y}(t_i).
\]
The \(c_{r,y}\) are grouped by their large-prime parts, using the true divisor identity and the complete one-copy integer drive. All sums are finite, \(Q_n=\mathcal E_{y,n}+\mathcal R_{y,n}\), and the sum in \(\mathcal R\) counts both orientations. There are no twists or comparison coefficients in this definition.

For each fixed \(A>2\), write \(C(A)\) for the following sign property:
\[
 \forall N\quad \exists n\in\mathbb N,\ n\ge N,\quad
 \exists\, 2\le y\le n^A:\quad \mathcal R_{y,n}\le0 .
\]
Each \(n\) and \(y\) applies to the entire native quadrature and its complete source history. This requirement does not select different cutoffs at different observation nodes.

Let \(d\) be the actual zero-displacement supremum. The native theorem gives the full energy rate \(d\), and the already certified external bound gives \(d\le b<1/2\). Then
\[
 \boxed{\ \inf\{A>2:C(A)\}=\frac1{1/2-d}\ } . \tag{1}
\]

**Proof.** If \(2<A<1/(1/2-d)\), the uniform upper for \(\mathcal E_{y,n}\), \(y\le n^A\), has energy exponent \(1-2/A<2d\). This case forces \(d>0\). Thus \(Q_n\) eventually strictly exceeds every admissible \(\mathcal E_{y,n}\), and \(\mathcal R_{y,n}>0\) for every such cutoff at every later integer. If \(A>1/(1/2-d)\), the proved lower at cofinal horizons has \(\mathcal E_{y,n}\ge \exp((1-2/A-o(1))n)\) at some \(y\le n^A\). Since \(1-2/A>2d\), \(\mathcal R_{y,n}/\mathcal E_{y,n}\to-1\) there. These two statements establish the infimum. When \(d=0\), the lower-side interval \(2<A<2\) is empty and the same upper-side argument proves \(C(A)\) for every \(A>2\). No claim about attainment of the critical endpoint is needed.

The full Step 4 conclusion follows if one proves \(C(2+1/k)\) independently from the actual arithmetic for each \(k\ge1\). Conversely if the genuine zero-displacement supremum vanishes then all those sign properties hold. Even a sign proof whose exponent \(A\) stays fixed has a quantifiable payoff:
\[
 C(A)\Longrightarrow d\le\tfrac12-\frac1A .
\]
For example \(C(7)\) would give \(d\le5/14\), \(C(4)\) would give \(d\le1/4\), and \(C(3)\) would give \(d\le1/6\). These are conditional values. The available external \(b\) proves \(C(A)\) for every \(A>1/(1/2-b)\), including \(A=8\). A cofinal sign already at \(y\le n^2\) is sufficient directly by the paid subexponential bound, though necessity at that exact endpoint has not been shown.

This criterion needs no additional accuracy in the cancellation once the cutoffs approach \(n^{2+o(1)}\). At these indices it is sufficient that the complete different-core covariance be nonpositive. A sign that holds only after twisting the prime factors, restricting the frequency range or dropping pairs is a different condition. An unconditional proof of the sign for cutoffs approaching exponent two still requires genuine arithmetic input. The congruence-filtered sufficient condition in the companion note can impose further conditions on nonprincipal twists. Equation (1) uses the untwisted complete source throughout.
