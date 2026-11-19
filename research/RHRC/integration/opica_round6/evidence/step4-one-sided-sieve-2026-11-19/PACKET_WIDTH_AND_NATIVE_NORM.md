# How narrow a signed packet has to be

**DERIVED on paper.** At log width \(X^{-1/2}\), integration over each native node recovers its sharp signed charge up to a subpower total squared error. A critical upper for those integrated charges is still missing. Bounds on smoother observations cannot be transferred by a universal norm inequality at widths through \(X^{-2/5}\). The counterexample below retains every actual terminal prime, genuine positive semiprimes, and the original GCD test. Its deletion of the other composites is precisely why it does not decide the complete-source problem.

## An upper transfer with an explicit price

Freeze the horizon, source, terminal label mask and original node tree. Given a nonnegative causal log packet \(h\) of total integral 1 supported in \([0,w]\), \(0<w\le1\), set
\[
 Z(t)=\sum_{q\ {\rm terminal}}\mu_y(q)q^{-1/2}h(t-\log q),\qquad
 m_h=\int e^{v/2}h(v)\,dv,\qquad
 A_J=m_h^{-1}\int_{\log J}e^{t/2}Z(t)\,dt .
\]
The integration interval is the log of the physical, unclipped dyadic node. The source has already been clipped exactly once. Complete interior atoms contribute exactly their signed charge, by \(t=\log q+v\). A partial contribution or a spill through an endpoint has magnitude at most one. In a shell \(U\), two endpoint strips contain \(O(1+wU)\) integer labels; hence \(|A_J-f_J|\ll 1+wU\). This includes terminal clipping and either endpoint convention.

For the genuine one-sided masses \(V_\pm=\sum_Jw_J[\pm f_J]_+^2\) and \(\mathcal V_\pm(h)=\sum_Jw_J[\pm A_J]_+^2\), contraction of the positive part and the triangle inequality give
\[
 \left|\sqrt{V_\pm}-\sqrt{\mathcal V_\pm(h)}\right|^2
   \ \ll\ 2^s(1+\log X)^2(1+w^2 X).                                \tag{1}
\]
Indeed a shell-depth with physical width \(H=H_0 2^{-k}\) has at most \(U/H\) nodes of weight \(2^{-k}/U\), so its squared boundary cost is \(O((1+wU)^2/H_0)\). Sum over \(O(\log X)\) levels and terminal shells \(X^{.99}/2<U\le X\), where \(H_0=U2^{-s}\). The estimate works with the coarse-only graph as well. For \(w\le X^{-1/2+o(1)}\) the price is subpower. If the obstruction exponent is \(2b>0\), a power width \(X^{-\xi}\) with \(1-2\xi<2b\) preserves it up to a strict relative power gap. The signed integral *inside each node* is taken before its positive part. The arithmetic of its surviving signed fluctuations has not been bounded independently here.

A compact positive probability cannot indefinitely hide an individual fixed rightward zero as its width shrinks. For \(z=\delta+i\gamma,\ \delta>0\), rotation by \(e^{i\gamma w/2}\) gives \(|\widehat h_L(z)|\ge e^{-\delta w}\cos(|\gamma|w/2)\) when \(|\gamma|w<\pi\). For the complete rough input before terminal clipping, the finite centered identity at any cutoff \(Y\) and \(Y/2\) thus gives
\[
 \int_0^{\log Y}|(\lambda_y*h)(t)|^2dt
    \gg_\rho Y^{2\delta-o(1)}|\widehat h_L(\rho-1/2)|^2
\]
at \(Y\asymp X\), always freezing the family member at both centered cutoffs. This prices every earlier label. Under the strict terminal restriction, fixed-test and subpower-variation kernels are localized by the early-head estimates in [the sign proof](../step4-prime-transport-2026-11-19/SINGLE_PROBE_SCALES.md); no such localization of a sharply spiking density follows merely from its total mass. The compact annihilators of [the local window proof](LOCAL_POLARITY_WINDOWS.md) have a physically meaningful width cost.

## A native signed comparison with every ordinary prime retained

Take all sufficiently large aligned \(X=2^{100t}\) and exactly the original terminal shells. Put \(U_*=X/2\). Fix a smooth function \(\psi\) supported in \((1,2)\), equal to one on \([1.2,1.8]\). On the whole positive axis put
\[
 F(u)=U_*^\theta\psi(u/U_*)\cos(u^\eta),\qquad
           \theta=.58,\quad\eta=.41,\quad\lambda=.575 .
\]
Only this last shell has a nonzero model. In each shell \(V\) partition into physical cells of dyadic integer length \(h_0=2^{\lfloor\lambda\log_2 V\rfloor}\). All terminal shells are complete at these cutoffs. Write \(y=\lceil\log_2 X\rceil^2\).

Keep every actual terminal prime, with its genuine negative Möbius sign. In a cell \([a,a+h_0)\) containing \(N\) such primes, eligible positive labels are all semiprimes \(\ell p\) where both factors are prime and \(y<\ell\le y^{100}\). At these scales \(p\gg y^{100}\), so the smaller factor is unique. For the normalized site coordinate \(z=(n-a)/h_0\in[0,1]\), the prime counting measure divided by \(h_0/\log V\) tends weakly to uniform measure on \([0,1]\). The corresponding semiprime measure tends to \((\log100)\) times uniform measure. Both assertions are uniform over the cells. Indeed for any fixed subinterval of relative positive length, ordinary PNT in all intervals above the exponent \(17/30\) applies after division by each \(\ell\), since \(\lambda>17/30\) and \(\ell\) is polylogarithmic. Also \(\log(V/\ell)=(1+o(1))\log V\). Sum the uniform relative error against \(\sum_{y<\ell\le y^{100}}\ell^{-1}=\log100+o(1)\) over primes. Approximate continuous moments by a finite mesh of fixed subintervals. [Guth and Maynard, Corollary 1.3](https://arxiv.org/html/2405.20552v2)

Within each cell select positive sites to produce the exact integer signed mass
\(\lfloor F(a+h_0)\rfloor-\lfloor F(a)\rfloor\). For \(j=1,\ldots,r\), \(r=40\), also require the signed \(j\)-th moment in the normalized coordinate \(z\) to differ from \(\int_{a}^{a+h_0}z^j\,dF\) by at most \(r+1\). These simultaneous requirements are feasible. The desired *positive* moment vector adds the moments of all \(N\) negative primes, with their signs removed. Since \(F'=O(V^{\theta+\eta-1})=O(V^{-.01})\) on its support, the model's total variation in a cell is \(o(N)\); the same statement is immediate in all other cells. The desired positive moment vector divided by \(N\) consequently tends uniformly to the moments of the uniform probability, including the rounded mass constraint.

Write \(v_i=(1,z_i,\ldots,z_i^r)\) at each eligible positive site, and \(c=\log100>1\). Begin with fractional weight \(1/c\). The moment discrepancy divided by \(N\) is \(o(1)\). The matrix \(N^{-1}\sum_i v_i v_i^{\mathsf T}\) tends to \(c\) times the positive definite moment matrix of uniform measure (the integral of the square of a nonzero polynomial is positive). Correct each weight by \(b\cdot v_i\), solving this linear system for \(b=o(1)\). The corrected weights remain in \([0,1]\), and match every requested moment exactly. At an extreme point of this nonempty finite polytope at most \(r+1\) weights are fractional, since a larger set permits a nontrivial two-sided motion annihilating all \(r+1\) constraints. Round these last weights to zeros and ones, preserving their integer total. The mass is still exact and the error of each normalized higher moment is at most \(r+1\). This proves existence at every cell; ties may be resolved by any fixed ordering.

Denote the resulting signed source by \(\nu_X\) on the integer axis. Its values on retained sites are the original \(\mu_y\). Every retained semiprime has large factor at least \(V/y^{100}>V2^{-s}\) eventually, and its remaining factor is below \(X^{.01}\). Therefore distinct retained neighbors in the same base cannot share the large prime, and every retained pair satisfies the exact original primitive GCD criterion. The other genuine composites are absent. In particular the restricted source does not have the full rough Dirichlet inverse.

## All smooth tests through power width \(X^{-2/5}\)

For any fixed smooth compactly supported profile \(\phi\), let \(\phi_w(t)=w^{-1}\phi(t/w)\). Uniformly in all translates \(t\) and all \(X^{-.4}\le w\le1\), the thinned source obeys
\[
       \left|\int u^{-1/2}\phi_w(t-\log u)\,d\nu_X(u)\right|
               \ll_\phi X^{-c_0}                                    \tag{2}
\]
for a fixed \(c_0>0\). Positivity of \(\phi\) is allowed. For example any sufficiently small \(c_0<.03\) works with the stated exponents.

For the proof compare to \(dF\). In a contributing shell let \(g(u)=u^{-1/2}\phi_w(t-\log u)\); its \(j\)-th derivative is \(O_{\phi,j}(V^{-1/2-j}w^{-1-j})\). Its support intersects \(O_\phi(1+wV/h_0)=O_\phi(wV/h_0)\) cells there, since \(V\ge X^{.99}\) and \(\lambda+.4/.99<1\). Taylor-expand through degree \(r\) about each left endpoint. Per cell the zeroth error is at most two by rounding \(F\) at both endpoints; each higher raw moment error is at most \((r+1)h_0^j\). Summing the polynomial terms therefore costs
\[
 \ll_\phi V^{1/2}h_0^{-1}\sum_{j=0}^{r}(h_0/(Vw))^j
       \ll_\phi V^{-.075}.
\]
Each cell has signed total variation at most \(O(h_0)\) for the difference measure, since no retained site is repeated and the model derivative is bounded. The summed Taylor remainder costs
\[
 \ll_\phi V^{1/2}\bigl(h_0/(Vw)\bigr)^{r+1}.
\]
Here \(1-\lambda-.4/.99>.0209\); multiplying by 41 pays more than the power \(1/2\). The bounded support of the profile uses only a fixed number of comparable shells; even an additional \(O(\log X)\) factor would be harmless.

For the model integral itself, integrate once by parts to move the derivative off \(F\), then put \(u=U_*v\). The fixed phase \(v^\eta\) has derivative bounded away from zero on the support of \(\psi\). Integrating by parts \(N_0\) times against \(e^{iU_*^\eta v^\eta}\) gives
\[
     O_{\phi,N_0}\big(U_*^{\theta-1/2-N_0\eta}w^{-N_0-2}\big).
\]
This is uniform in the translate including those near the support boundary; both \(\psi\) and the profile are smooth with compact support. At \(w\ge X^{-.4}\), taking \(N_0=128\) yields a fixed power saving since \(\theta-.5+.8-128(.41-.4)<0\). These estimates prove (2).

## Both signs of the native sharp charges remain large

In the last shell choose the actual dyadic depth with physical length
\(\tfrac18 U_*^{1-\eta}<H\le\tfrac14 U_*^{1-\eta}\), allowing equality at either rounded endpoint. This is a coarse native level since \(1-\eta=.59>1/2\), its width is below the base width for large \(X\), and \(H>h_0\). All endpoints here coincide with microcell boundaries. Consequently the charge of a complete such node is **exactly** the difference of the two rounded values of \(F\). On \([1.2U_*,1.8U_*]\) a positive proportion of nodes have \(\sin(u^\eta)>1/2\) throughout, and a positive proportion have \(\sin(u^\eta)<-1/2\) throughout. Indeed the phase traverses \(\asymp U_*^\eta\) full periods with derivative comparable to \(U_*^{\eta-1}\); each node covers a phase interval smaller than \(1/8\), and each period has fixed-width internal sectors of both signs. On each such node the increment has magnitude \(\gg U_*^\theta\), including the at-most-two endpoint rounding errors. Thus on the original tree of this same signed subgraph
\[
       V_+(\nu_X),\ V_-(\nu_X)
         \gg \frac{H}{U_*H_0}\frac{U_*}{H} U_*^{2\theta}
         =\frac{U_*^{2\theta}}{H_0}
         \ge X^{.16-o(1)}.                                          \tag{3}
\]
The weights, integer graph, complete prime channel and primality of the inserted positive partners are all exact. Relations (2)–(3) disprove a universal subpower norm comparison for smooth observations at the indicated widths even with these restrictions. No contradiction with actual OPICA follows: crucial composite rows were deliberately deleted.

For unrestricted labels of modulus at most one the distinction is sharp in exponent. For any \(\xi<1/2\) choose \(\xi<\eta<1/2,\ 1/2<\theta<1-\eta\). On a final shell use the integer labels \(\lfloor F(n+1)\rfloor-\lfloor F(n)\rfloor\) with this same compact model. They are \(0,\pm1\) eventually since its derivative is \(o(1)\), and all interval discrepancies from \(dF\) are \(O(1)\). Partial summation costs \(O(U_*^{-1/2}w^{-1})\) for a normalized packet, and arbitrary-order nonstationary integration handles the model because \(\xi<\eta\). Thus all smooth translates stay small down to \(w=X^{-\xi}\) although both native sharp energies grow with exponent at least \(2\theta-1\). This last version assigns new integer signs and makes no prime-support claim. The stronger example above retains the genuine prime signs through \(\xi=.4\).

**OPEN.** A genuine upper for the narrow signed integrals in (1), or a separately paid residual between the smoothed and sharp charges, must use more of the complete arithmetic coupling. Width variation, positivity and a finite verified zero height do not supply it.
