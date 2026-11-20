# Deterministic prime cutoffs give an eventual covariance sign

**Paper result.** Let \(c>0\) and \(A>0\) be fixed; set \(y=c n^A\) at every node of the genuine native terminal array. The [limsup over cutoffs](ROUGH_CORE_PHASE_TRANSITION.md) strengthens to an actual limit for this *single prescribed cutoff at every horizon*. In particular with \(y=n^8\) the entire signed covariance between distinct rough cores is eventually negative at every integer, with exponential rate \(3/4\) for its magnitude.

Write \(E_y(t)=\sum_{(r,P_y)=1}\mu(r)^2r^{-1}V_y(t-\log r)^2\). Uniformly for \(n-2\log n\le t\le n\),
\[
 \frac{\log(1+E_{c n^A}(t))}{2n}
 \longrightarrow\max(0,\tfrac12-1/A).                          \tag{1}
\]
The positive terminal quadrature or continuous integral satisfies the same limit because its total weight is \(2\log n\). The upper is already proved for arbitrary \(y\le c n^A\) by the pointwise Rankin estimate. We establish the lower throughout the terminal window by sampling a slightly earlier part of the positive filter energy.

## Sampling a tilted earlier filter

Suppose \(A>2\), put \(\sigma=1/2-1/A>0\), and fix \(0<\epsilon<1/4\). Let \(a=\log(Ac^{1/A}/(1-\epsilon))\) and \(\sigma_y=\sigma+a/\log y\). By [the Euler-product Plancherel estimate and exponential tilting](ROUGH_CORE_PHASE_TRANSITION.md), the probability measure proportional to \(e^{-2\sigma_y v}V_y(v)^2dv\) concentrates at
\[
 v\sim e^{-a}A y^{1/A}=(1-\epsilon)n .
\]
Indeed its logarithmic normalizer is \((2e^{-a}+o(1))A y^{1/A}/\log y\). Moving the tilt again by \(\pm b/\log y\) gives the relative-tail estimates by the same exponential moment argument. In particular for every small fixed \(\eta>0\), on the band \(J=[(1-\epsilon-\eta)n,(1-\epsilon+\eta)n]\),
\[
 \int_J V_y^2\,dv\ge \exp(2\sigma(1-\epsilon-\eta)n+o(n)).       \tag{2}
\]

The elementary Bonferroni proof in [the rough-density audit](FIXED_SIEVE_RECURRENCE_AUDIT.md) applies also to \(y=c n^A\) with \(A\) fixed above two. At even order \(K\sim \xi n/\log n\), for all \(x\ge1\) it gives
\[
 |N_y(x)-c_y x|\ll_A x e^{-\xi n/2}+\sqrt x\, e^{(A+2)\xi n}.
\]
Here \(c_y=\zeta(2)^{-1}\prod_{p\le y}(1+1/p)^{-1}\). The main-series coefficient sum is \(O_A(\log n)\) before taking the factorial tail, and the finite error multiplier is bounded by \(3(K+1)(2c n^A)^K\). At \(x=e^{t-v}\) for \(v\in J\), \(\eta<\epsilon/4,\ t\ge n-2\log n\), the lower endpoint satisfies \(x\ge e^{\epsilon n/2}\) eventually. Take \(\xi=\epsilon/(16(A+2))\). Consequently throughout this entire integration range the relative Stieltjes discrepancy is bounded by \(O(e^{-\delta n})\) with a fixed \(\delta>0\) depending on \(A,\epsilon\), independently of any further decrease of \(\eta\).

On \(J\) the tilted absolute Euler filter gives
\[
 |V_y(v)|+|V_y'(v)|\ll_{\sigma,j}e^{\sigma_y v}
 \prod_{p\le y}(1+p^{-1/2-\sigma_y})
 \le\exp(\sigma(1-\epsilon+\eta)n+o(n)).
\]
The final error is \(o(n)\) since the product log costs \(O_{A,c,a}(n/\log n)\). Partial summation of \(x^{-1}V_y(t-\log x)^2\) on the endpoints of \(J\), including both boundary errors, now compares the corresponding subsum of \(E_y(t)\) to \(c_y\int_J V_y^2dv\) with error
\[
 O\!\left(\exp\big((2\sigma(1-\epsilon+\eta)-\delta)n+o(n)\big)\right).
\]
Indeed the endpoint plus total variation costs at most \(O(n)\) times the squared supremum of the preceding derivative bound. Since \(c_y\ge1/(y+1)\), its log is \(o(n)\). Choose \(4\sigma\eta<\delta/2\). Equation (2) then dominates the error exponentially. The subsum is positive and the rest of \(E_y\) is positive. This gives \(\liminf (\log E_y)/(2n)\ge\sigma(1-\epsilon-\eta)\) uniformly for all \(t\) in the required window. Send \(\epsilon\) and then its allowed \(\eta\) to zero. This proves (1). All concentrations and estimates used here hold for every sufficiently large \(n\), and the cutoff is fixed from \(n\) alone.

## At and below the quadratic boundary

For \(0<A<2\) the sharper [uniform sampling theorem](FIXED_SIEVE_RECURRENCE_AUDIT.md) gives \(E_y(t)=L_y+O_{A,c}(e^{-c' n})\) and \(\log L_y\sim4\sqrt y/\log y\). At \(A=2\) one obtains the following complete profile, again uniform at the original terminal times:
\[
 \frac{\log E_{c n^2}(t)}{n/\log n}\longrightarrow
 \begin{cases}
   2\sqrt c,&0<c\le1/4,\\
   1+\log(2\sqrt c),&c\ge1/4.
 \end{cases}                                                       \tag{3}
\]
If \(c<1/4\), apply the near-quadratic relative sampling theorem in the audit. For \(c\ge1/4\) and the lower bound, take \(\sigma_y=a/\log y\), now \(a=\log(2\sqrt c/(1-\epsilon))>0\). The mass of the tilted filter is centered at \(2e^{-a}\sqrt y=(1-\epsilon)n\). On \(J\) equation (2) sharpens in this case to
\[
 \log\int_J V_y^2dv
 \ge [a(1-\epsilon-\eta)+(1-\epsilon)+o(1)]\,n/\log n .
\]
This is the sum of the minimum reverse tilt \(2a(1-\epsilon-\eta)n/\log y\) and the normalizer \((4e^{-a}+o(1))\sqrt y/\log y\). All sampling errors \(e^{-\delta n}\exp(o(n))\) are negligible. The factor \(c_y\ge1/(y+1)\) costs just \(O(\log n)=o(n/\log n)\). Sending \(\epsilon,\eta\) to zero gives the second lower bound in (3), including \(c=1/4\). For \(c>1/4\) use the absolute Rankin bound with \(a_*=\log(2\sqrt c)\), \(\sigma'_y=a_*/\log y>0\). The time tilt contributes \((a_*+o(1))n/\log n\) and the squared product contributes \((2e^{-a_*}\sqrt c+o(1))n/\log n\). Their sum gives the asserted upper. At \(c=1/4\) use the zero-tilt elementary uniform bound (1) of the original phase-transition note, retaining the prime number theorem's leading constant in the positive Euler product. Quadrature introduces only \(O(\log\log n)\) into the logarithm, so (3) holds for the terminal energy as well.

## What sign this establishes for the genuine source

Let \(Q_n=\sum_iw_iP(t_i)^2\), \(\mathcal E_{y,n}=\sum_iw_i E_y(t_i)\), \(\mathcal R_{y,n}=Q_n-\mathcal E_{y,n}\), with the same finite histories and full signed pair expansion as before. The continuous terminal window can be used throughout. For \(A>2\):
- If \(d>1/2-1/A\), then \(\mathcal R_{c n^A,n}/Q_n\to1\).
- If \(d<1/2-1/A\), then \(\mathcal R_{c n^A,n}/\mathcal E_{c n^A,n}\to-1\).

The merged theorem gives \(\log(1+Q_n)/(2n)\to d\) and (1) prices the complete same-core energy. Both implications are therefore statements about every late integer. At equality no sign claim follows. The known \(b<3/8\) proves unconditionally for every fixed \(c>0\) that
\[
 \mathcal R_{c n^8,n}=-\exp((3/4+o(1))n),
 \qquad \left|1+\mathcal R_{c n^8,n}/\mathcal E_{c n^8,n}\right|
 \le \exp(-(3/4-2b-o(1))n).
\]
Likewise \(d=0\) is equivalent to the cofinal sign at each prescribed cutoff \(y=n^{2+1/k}\) for every \(k\ge1\). Sufficiency uses the independent uniform upper. The converse follows from (1). For the fixed cutoff \(Y=10^7\), the subquadratic and quadratic positive translation sectors in the audit have a different behavior. In the critical cofinal comparison at \(y=n^2\), (3) gives \(\log\mathcal E_{n^2,n}\sim (1+\log2)n/\log n\) at **all** large integers. If \(d=0\) the fixed-source critical-line bound makes \(Q_n=O_j(\log n)\); if \(d>0\) its energy grows exponentially. Consequently a single prescribed sign also suffices at \(y=n^2\), and RH implies that this sign is eventually negative. This proof still provides no unconditional recurrence of negativity at the quadratic cutoff or at fixed \(Y=10^7\).
