# Duration of a negative signed prime-field integral

**19 November 2026. Paper deductions.** Use the complete one-copy field \(P\), including all prime powers, \(Y=10^7\), and \(H=P^2-E_Y\) from the fixed-sieve decomposition. Write \(L=L_Y=\lim E_Y>1.1\cdot10^{73}\), \(d=\sup_\rho(\Re\rho-1/2)_+\), and \(p=\rho-1/2\). The following deductions use the merged native explicit formula, the independently bounded original sinc weights, and a classical zero-density estimate. They give conditional restrictions on the actual zero configuration and a sufficient arithmetic test. Step 4 remains open. [Native explicit formula](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeExplicitFormula.lean) · [One-copy weights and diagonal](../../step4-correlation-2026-11-19/FIXED_SIEVE_SIGN.md) · [Pointwise diagonal bounds](../../step4-correlation-2026-11-19/divisor/FIXED_SIEVE_RECURRENCE_AUDIT.md)

## The exact critical length for one attained rightmost pair

Suppose \(d>0\) and exactly one conjugate pair \(d\pm i\gamma\), \(\gamma>0\), attains \(d\). Other displacements may approach \(d\). With \(A=m_\rho J(d+i\gamma)\ne0\), let \(F(t)=-2\Re(Ae^{i\gamma t})\), \(B(t)=e^{-dt}P(t)\). For every fixed \(k\),
\[
 B^{(k)}(t)=F^{(k)}(t)+o(1).
\]
Indeed the normalized contribution of each other zero has factor \(e^{(\Re p-d)t}\to0\). The complete derivative sum is dominated by \(\sum_p(1+|p|)^k m_\rho |J(p)|<\infty\). The differentiated trivial-zero term decays. This proves convergence on the whole late tail and needs no gap below \(d\).

Fix small disjoint neighborhoods about the simple cosine zeros on which \(|F'|\) is bounded below and its sign fixed. On their complement \(|F|\) is bounded below. Consequently each sufficiently late neighborhood contains exactly one actual source zero \(\tau_k\), there are no other late zeros, and \(\tau_{k+1}-\tau_k=\pi/\gamma+o(1)\). At these zeros,
\[
 e^{-d\tau_k}|P'(\tau_k)|\longrightarrow v,\qquad v=2\gamma |A|.
\]
For every fixed bounded \(x\)-range, the absolute value \(|P(\tau_k+xe^{-d\tau_k})|\) converges uniformly to \(v|x|\). This follows by Taylor expansion of \(B\) with bounded second derivative and multiplication by \(e^{d(\tau_k+xe^{-d\tau_k})}\).

Set \(D=0\) or \(10^{73}\) and \(h(t)=\sqrt{E_Y(t)-D}\), eventually positive with limit \(h_*=\sqrt{L-D}\). The derivative \(E_Y'\) is bounded. In fact \(E_Y\) samples \(V_Y^2\) with weights \(1/r\); on differentiating the locally finite sum, the new profile \(2V_YV_Y'\) is compact on its lower end and exponentially decreasing on its upper end. The sum of \(1/r\) in each unit log interval is uniformly bounded, also over this subset of integers. This proves the derivative bound even without differentiating a limit. Thus \(h'\) is bounded at late times. On each selected phase neighborhood the graphs \(B(t)\) and \(\pm e^{-dt}h(t)\) cross exactly once per sign, since their derivative differences have strict fixed sign. These are the endpoints of the connected component of \(H<-D\) containing \(\tau_k\). The endpoints equal
\[
 \tau_k\ \pm\ (h_*/v+o(1))e^{-d\tau_k}.
\]
To see the scale before taking the limit, the derivative lower bound for \(|B'|\) shows both endpoints lie \(O(e^{-d\tau_k})\) from \(\tau_k\). There are no other late components. In particular their lengths are asymptotic to \(\sqrt{L-D}\,e^{-d\tau_k}/(\gamma|A|)\).

There is a different threshold for the *integrated* sign. For any fixed \(c>0\) take \(I_k\) centered at \(\tau_k\) of length \(ce^{-d\tau_k}\). Then
\[
 \lim_{k\to\infty}e^{d\tau_k}\int_{I_k}(H+D)
     = v^2c^3/12-(L-D)c.
\]
The integral is eventually negative for \(c<\sqrt{12(L-D)}/v\) and positive for \(c\) strictly above that threshold. Equality requires a finer term. Thus even uniformly recurring sign-balanced zeros of the actual source can give precisely the exponential duration in the [prior bounded-gap result](../../step4-correlation-2026-11-19/NEGATIVE_INTERVAL_DURATION.md), under the stated possible zero configuration.

## The complementary case of a supremum that is never attained

If \(d>0\) and no zero attains it, then \(e^{-dt}|P'(t)|\to0\) by the same absolute derivative summation, with no leading terms. Let \(B_1\) be the fixed window length of the bounded-gap zero theorem, increased by two so there is an interior zero with a unit of margin at each end. For any fixed \(K>0\), all sufficiently late \([t-B_1,t]\) contain an interval of length \(K e^{-dt}\) throughout which \(H<-10^{73}\). Indeed the supremum of \(|P'|\) on the window is \(o(e^{dt})\); the variation from its interior zero on such a segment is \(o(K)\), and the diagonal has the fixed strictly larger lower bound. Thus the guaranteed ratio of the negative duration to \(e^{-dt}\) tends to infinity in the nonattainment case. Absolute summability provides no power of \(t\) in that ratio.

## Finite derivative detection on a rightmost line

Suppose \(d>0\) is attained and that **either** it is attained at finitely many distinct ordinates, **or** \(d>3/10\). Then some integer \(m\ge1\) and \(c_0>0\), fixed from the source and its actual zero configuration, satisfy
\[
 \max_{0\le k\le m}|B^{(k)}(t)|\ge c_0
 \quad\text{at every sufficiently late }t .
\]
For \(N<\infty\) rightmost ordinates one can take \(m=N-1\). Indeed the first \(N\) derivatives of \(F(t)=-\sum_{\Re p=d} A_pe^{i\Im(p)t}\) have the Vandermonde matrix on the distinct frequencies, acting on a vector one of whose coordinates has fixed nonzero absolute value. The differentiated dominated convergence above still gives \(B^{(k)}-F^{(k)}\to0\).

For the second alternative, Ingham gives \(O(R^\kappa)\) such ordinates in \([-R,R]\) with some \(\kappa<1/2\), since \(3(1/2-d)/(3/2-d)<1/2\). The actual single sinc source gives
\[
 |J(p)|\ll(1+|\Im p|)^C e^{-\sqrt{|\Im p|}/32}.
\]
Choose one extremal ordinate \(\gamma_0\). For the remaining distinct offsets \(s=\gamma-\gamma_0\) define \(Q_R(x)=\prod_{0<|s|\le R}(1-x/s)\). Uniformly in \(R\), \(|Q_R(x)|\le\exp(C_1(1+|x|^\kappa))\). Indeed sum \(\log(1+|x|/|s|)\) using partial summation against \(O(u^\kappa)\) offsets of size at most \(u\), starting at their positive minimum distance from zero. This bound is dominated after multiplication by the sinc decay above, including multiplicities using ordinary zero counting. [Ingham](https://doi.org/10.1093/qmath/os-11.1.201) · [Explicit density exponent, (1.2)](https://arxiv.org/html/2405.20552#S1)

Allow arbitrary unit phases on the leading coefficients. No such series with coefficients \(-A_\gamma\omega_\gamma\) can vanish with all its derivatives at a point. Otherwise the same holds after modulation by \(e^{-i\gamma_0 t}\), so its derivative combination \(Q_R(D/i)\) vanishes there. As \(R\to\infty\) dominated convergence kills every offset other than zero and leaves the nonzero \(\gamma_0\) coefficient times a phase. Finally, if the asserted uniform finite-jet statement failed for \(F\), one could choose phases from translations with derivatives of orders up to \(j\) smaller than \(1/j\), then extract a subsequence converging at every ordinate. Uniform absolute derivative convergence would give a flat phase series. Transfer back from \(F\) to \(B\) with the fixed finite number of derivatives.

Here is the quantitative implication for **measurable** sets, which permits positive excursions inside a negative-average window. Uniform bounds on the first \(m+1\) derivatives allow every late unit interval to be covered by a fixed number of short pieces, on each of which some derivative of order \(0\le k\le m\) has fixed sign and absolute value at least \(c_0/2\). If \(k=0\), sufficiently small sublevels are empty. If \(k>0\), a sublevel set of measure \(s>0\) supplies \(k+1\) points separated by at least \(s/(2k+2)\), by selecting successive measure quantiles (arbitrarily small endpoint approximations suffice). The formula for their divided difference bounds it by \(C_k y/s^k\) when \(|B|\le y\) at these points. The real mean-value theorem identifies it with \(B^{(k)}(\xi)/k!\). Summing the resulting estimates gives
\[
 |\{u\in[t,t+1]:|B(u)|\le y\}|\ll y^{1/m}
 \qquad(0<y\le1).
\]
For every subinterval \(I\subset[t,t+1]\) of length \(W>0\) set \(y=c W^m\) with \(c>0\) sufficiently small. This gives
\[
 \int_I P^2\gg e^{2dt}W^{2m+1},\qquad
       \int_I H\le0\ \Longrightarrow\ W\ll e^{-dt/m}.
\]
In particular a cofinal nonpositive average at *any* subexponential width \(e^{-o(t)}\) excludes an attained positive \(d\) of either kind above. This leaves open nonattainment and the possible infinite attained spectra with \(d\le3/10\).

## Shrinking windows without attaining the supremum

There is an unconditional implication for \(d>3/10\) even if no zero attains \(d\). Put \(\kappa_0(d)=3(1/2-d)/(3/2-d)\). For every fixed \(0<\nu<1-2\kappa_0(d)\) and \(W(t)=e^{-t^\nu}\),
\[
 \lim_{t\to\infty}\frac{\log(1+\int_{t-W(t)}^tP(u)^2du)}{2t}=d.
\]
To verify this, choose an actual \(p_0\) with displacement \(\delta\) near enough to \(d\), then \(0<\alpha<\delta\) and \(\kappa>\kappa_0(\alpha)\) with \(2\kappa+\nu<1\). At time \(t\), take absolute ordinate cutoff \(R=K t^2\) with fixed large \(K\). Among the distinct zeros \(p\ne p_0\) with \(\Re p\ge\alpha\) and \(|\Im p|\le R\) are \(M=O(R^\kappa)=O(t^{2\kappa})\) offsets \(z_j=p-p_0\); their moduli are bounded below by a fixed positive number by discreteness. Form the convolution \(\eta\) of \(M+2\) uniform probability densities on \([0,w]\), \(w=W/(M+2)\), and put \(f(u)=e^{p_0u}\prod_j(1-D/z_j)\eta(u)\). Its Laplace transform is one at \(p_0\) and zero at the \(M\) listed zeros. Each of up to \(M\) derivatives can be taken on a different factor at cost \(2/w\) in total variation, leaving an \(L^2\) density of norm at most \(w^{-1/2}\). Thus
\[
 \log(2+\|f\|_1+\|f\|_2)\ll(M+1)(\log(2+M)+t^\nu)=o(t).
\]
In the actual filtered explicit formula all low-real-part terms cost \(O(\|f\|_1e^{\alpha t})\), and the bounded trivial-zero term costs \(O(\|f\|_1)\). The high-ordinate remainder costs \(O(\|f\|_1 e^{dt}e^{-\sqrt R/64})\) by the original sinc bound and ordinary zero counting. Choose \(K\) with \(\sqrt K/64>d+1\). The output has modulus at least \(|A_{p_0}|e^{\delta t}/2\) eventually. Cauchy–Schwarz, followed by taking the supremum of all such \(\delta\), proves the lower; \(|P|\ll e^{dt}\) proves the upper. This modifies the [existing infinite-filter construction](../../step4-correlation-2026-11-19/cuts/FIXED_WINDOW_ZERO_ISOLATION.md) by spending the actual source's high-frequency attenuation after a finite filter. As a consequence, a cofinal nonpositive signed average measured on these prescribed widths \(e^{-t^\nu}\), for any fixed \(0<\nu<1\), would force \(d\le 3(1+\nu)/(10+2\nu)\). This observation does not prove the recurrence.

### A stronger numerical threshold from Guth and Maynard

In each of the two preceding sections the sole use of the Ingham exponent is the count of distinct ordinates in a right half-plane, with multiplicities harmless. Guth and Maynard, Theorem 1.2, give the admissible exponent (with arbitrarily small fixed positive slack)
\[
 \kappa_G(\alpha)=\frac{15(1/2-\alpha)}{11/2+5\alpha}.
\]
Thus the uniform finite-jet and sublevel theorem for an infinite **attained** maximal line already holds when \(d>19/70\), because \(\kappa_G(d)<1/2\) there. Without any attainment, the stretched-exponential energy rate holds for \(0<\nu<(70d-19)/(11+10d)\). Consequently, if a nonpositive covariance average occurs cofinally at width \(e^{-t^\nu}\), then
\[
 d\le\frac{19+11\nu}{70-10\nu}\qquad(0<\nu<1).
\]
For example \(\nu=1/10\) gives \(d\le67/230\). These are implications under an independently established recurrence. The same substitution in the earlier infinite-filter theorem for \(W=t^{-\lambda}\) shows that nonpositive covariance on cofinal such windows forces \(\kappa_G(d)\ge1/(1+\lambda)\), hence \(d\le(4+15\lambda)/(40+30\lambda)\). At \(\lambda=1\) this is \(19/70\). The minimum with the Ingham restriction applies throughout. [Guth–Maynard, Theorem 1.2](https://arxiv.org/html/2405.20552#S1)

## What actual zero clustering would suffice

Independent of the location of rightmost zeros, \(\sup_{v\in[t,t+1]}|P^{(m)}(v)|\le C e^{d(t+1)} B_0^m(m!)^2\) for fixed \(C,B_0\ge1\) and all \(m\ge0,t\ge1\). The explicit-formula zero sum is bounded by the \(m\)-th moment of the sinc envelope above. Comparing the sum over unit strips with the integral and substituting \(u=\sqrt{|\gamma|}\) costs a fixed constant to the power \(m+1\) times \((2m+C_2)!\); the latter is bounded by \(C_3^{m+1}(m!)^2\) for a fixed integer \(C_2\). For trivial zeros the bound follows from \(|J(-2k-1/2)|\le\|j\|_1e^{(2k+1/2)s}\), \(s=1/4096\), and \(\sum (2k+1/2)^m e^{-(2k+1/2)(t-s)}\ll C_4^{m+1}m!\).

On an interval of length \(w\) with \(m\) distinct actual zeros of \(P\), repeated Rolle or the interpolation remainder gives \(\sup|P|\le C e^{d(t+1)}(B_0 w)^m m!\). Endpoints need not be zeros. For example take \(m=\lceil t\rceil\), \(w\le c/t\), with \(2B_0c\le e^{-2}\). Then throughout such an interval \(|P|<1\) at all sufficiently late \(t\). Covering an inverse-log window cofinally by adjacent cells of lengths at most \(c/t\), each with \(\lceil t\rceil\) distinct actual source zeros (using a common \(t\) for that window), would force the closing covariance sign. This is a checkable sufficient count **with a distribution requirement**. The proved bounded-gap zero theorem gives neither this count nor the distribution. No arithmetic source estimate establishing that many zeros, a subexponential duration, or the closing sign was obtained.
