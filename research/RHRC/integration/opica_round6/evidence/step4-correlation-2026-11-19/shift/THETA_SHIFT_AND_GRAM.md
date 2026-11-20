# Two positive theta averages of the unchanged OPICA prime field

**Paper deduction, 19 November 2026. Step 4 OPEN.** One strictly positive observation of the genuine prime field has an independently computable, exponentially decaying signed value at every late time. A fixed exponential tilt of the same observation detects every possible rightward zero. Both observations can be confined to the same native terminal windows with exponentially small error. The tilt has an explicit arithmetic cost.

## The two readouts

Use the native one-copy source \(j=(D^2-1/4)^2q_s,\ s=1/4096\), with transform \(J(z)=\int e^{-zu}j(u)\,du=(z^2-1/4)^2Q(z)\). The literal field is \(P(t)=\sum_{m\ge2}\Lambda(m)m^{-1/2}j(t-\log m)\). It vanishes before \(\log2-s\) and satisfies \(|P(t)|\ll_j e^{t/2}\) by Chebyshev and support. The repository proves the explicit formula with multiplicities and absolute convergence, and the continuous log-window rate for this same field. [Native source](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeSourceFamily.lean) · [Explicit formula](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeExplicitFormula.lean) · [Native rate](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeWindowRate.lean#L1154)

Write \(w=1/2+z\) and \(G(w)=w(w-1)\pi^{-w/2}\Gamma(w/2)/2\), so \(\xi(w)=G(w)\zeta(w)\). Let \(\psi(x)=\sum_{m\ge1}e^{-\pi m^2x}\). The even Riemann kernel in our bilateral Laplace normalization is
\[
 \Phi(u)=(D^2-1/4)\{e^{-u/2}\psi(e^{-2u})\},\qquad
 \int_{\mathbb R}e^{-zu}\Phi(u)\,du=\xi(1/2+z).
\]
Indeed for \(\Re w>1\), the gamma integral after \(x=e^{-2u}\) and two integrations by parts give this equality. Jacobi inversion establishes evenness after \(D^2-1/4\) kills the elementary half exponentials. For \(u\le0\) the sum is \(e^{-u/2}\sum_m(4a_m^2-6a_m)e^{-a_m}\), with \(a_m=\pi m^2 e^{-2u}\ge\pi\). Thus \(\Phi>0\) and \(\Phi(u)\ll\exp(-c e^{2|u|})\) for a fixed \(c>0\). The identity extends to every complex \(z\). [Classical kernel and convention comparison](https://arxiv.org/abs/1801.05914) · [Completed function](https://dlmf.nist.gov/25.4)

For \(\alpha=0,1\) define \(F_\alpha(t)=\int e^{-\alpha u}\Phi(u)P(t-u)\,du\). The positive weights are fixed before the horizon and any zero. Absolute Fubini on \(\Re z>1/2\) gives
\[
 \widehat F_\alpha(z)=-J(z)\xi(w+\alpha)\frac{\zeta'(w)}{\zeta(w)} .                 \tag{1}
\]

### An independently bounded signed echo

At \(\alpha=0\), (1) is \(-J(z)G(w)\zeta'(w)\). The elementary pole at \(w=1\) is removed by \(J(1/2)=J'(1/2)=0\). The apparent point at \(w=0\) is regular. Move the line to \(\Re z=-7/2\). There is one residue, at \(w=-2\), equal to \(-\xi(-2)J(-5/2)\); this follows directly from the simple zero of \(\zeta\) and the finite nonzero value of \(\xi(-2)\). Stirling along vertical lines, rapid decay of the compact source transform, and the polynomial vertical-strip bound for \(\zeta'\) justify this finite contour shift. Thus
\[
 F_0(t)=-\frac{3\zeta(3)}{2\pi}\,J(-5/2)e^{-5t/2}+O_j(e^{-7t/2}).
\]
In particular it eventually has strictly negative sign. Its pairing with the complete field \(P\) is absolutely integrable, with tail \(O_j(e^{-2T})\). This is a fixed positive-weight bilateral average of the genuine field.

### A visible cousin with a smaller spectral window

At \(\alpha=1\) a nontrivial zero \(\rho\) with \(\Re\rho>1/2\) and multiplicity \(m_\rho\) gives the residue \(-m_\rho J(\rho-1/2)\xi(1+\rho)\). The first factor of the multiplier is nonzero by the actual sinc product away from the imaginary axis and the excluded pole shifts. The second is nonzero because \(1+\Re\rho>1\). Multiplicities cause no additional visibility requirement. For \(1/2\le\Re\rho<1\) and \(|\Im\rho|\ge2\), Stirling and the Euler product in \(\Re w\ge3/2\) give
\[
 |\xi(1+\rho)|\asymp (1+|\Im\rho|)^{2+(\Re\rho)/2}e^{-\pi|\Im\rho|/4}
\]
with uniform constants. The explicitly canceled elementary pole leaves the transform regular on the positive real \(z\)-axis.

Shift (1) for \(\alpha=1\) only to \(\Re z=-1\), crossing the nontrivial poles. There are no trivial poles in this strip. On the boundary \(\Re w=-1/2\), the functional equation bounds \(\zeta'/\zeta\) by \(O(\log(2+|\Im w|))\) at large heights. Horizontal sides may be taken a distance \(\gg1/\log(2+H)\) from nearby zero ordinates, using the standard count in a unit interval and the local partial fraction expansion. Polynomial growth on these lines is harmless against gamma decay. Consequently
\[
 F_1(t)=-\sum_{\rho}m_\rho J(\rho-1/2)\xi(1+\rho)e^{(\rho-1/2)t}+O_j(e^{-t}).
\]
The sum is over distinct nontrivial zeros with multiplicities displayed once. This argument never sums the gamma-weighted residues of arbitrarily remote trivial zeros.

Put \(b=\theta-1/2<0.374\), using the separately qualified [external zero ceiling](https://github.com/GTimG/QuasiRiemannTracker/blob/42cf5415cfaa4205caaa25ab11160724606cdc33/submissions/2026-11-13-continuum-exact-contact/src/Candidate/Main.lean). For \(t\ge0\), rightward zeros with \(|\Im\rho|>H\ge2\) cost at most \(C_j e^{bt-0.70H}\). For example \(\sum_\rho m_\rho |J(\rho-1/2)|<\infty\) and the polynomial gamma prefactor is absorbed by the difference \(\pi/4-0.70>0\). All critical and leftward zeros together cost \(O_j(1)\). Thus the *visible* readout needs a spectral window linear in the log-time horizon for an exponentially small remaining tail. Given the verified height \(H_0=3\cdot10^{12}\), for \(0\le t\le5\cdot10^{12}\) the growing-mode tail is bounded by \(C_j e^{-2.3\cdot10^{11}}\); \(C_j\) has not been numerically evaluated. This estimates the tilted readout, whose contribution from the critical line is still \(O_j(1)\). It supplies no new verified zero heights or original-trial bounds. [Platt–Trudgian](https://arxiv.org/abs/2004.09765)

### Both readouts inside the true terminal window

Let \(I_T=[T-C\log T,T]\) with fixed \(C>1\). Given \(A>0\), choose \(r_T=\tfrac12\log T+c_A\) fixed before all centers, with \(c_A\) sufficiently large. For every \(v\in I_T\) at distance at least \(r_T\) from its endpoints,
\[
 \left|F_\alpha(v)-\int_{I_T}e^{-\alpha(v-y)}\Phi(v-y)P(y)dy\right|
 \ll_{j,A}e^{-AT},\qquad\alpha=0,1.
\]
Indeed \(|P(y)|\ll_j e^{y/2}\), so the cost is at most \(C_j e^{T/2}\int_{|u|>r_T}e^{(3/2)|u|}\Phi(u)du\). The double-exponential tail proves the estimate. The interval of valid centers has length \((C-1)\log T-2c_A\) and tends to infinity. Squaring the finite-window average retains every signed prime-power pair that enters the average. Positive weighting, a continuum of centers and very small terminal errors can therefore coexist with full blindness to unstable modes in \(F_0\). The exponentially small tail is explicitly restored for both observations.

### Direct arithmetic gate for the visible tilt

The function \(F_1(t)\) decays faster than any exponential as \(t\to-\infty\), by the lower support of \(P\), the kernel tail and Chebyshev. Its negative-time transform is entire. For \(t\ge0\), a sufficient arithmetic premise is, for every \(\epsilon>0\), an eventual bound \(F_1(t)\le C_\epsilon e^{\epsilon t}\), or the same upper on \(-F_1\). Under that hypothesis the positive-part Laplace transform (for the chosen sign) is holomorphic on \(\Re z>0\). Subtracting (1) and the entire negative-time contribution continues the negative-part transform across every positive real point. The standard singularity theorem for the abscissa of a positive measure then implies holomorphy of that transform throughout \(\Re z>0\). Thus \(F_1\)'s transform has no poles there. Every visible rightward zero would contradict this by its explicit nonzero residue. This is an *eventual* condition; a cofinal pointwise estimate alone does not suffice. Local positive quadrature or local energy upper gates require their own transfer.

In \(\Re w>1\) write (1) as \(J(z)G(w+1)\sum c(n)n^{-w}\) with
\[
 c(n)=\sum_{d\mid n}\frac1d\Lambda(n/d), \qquad
 0\le c(n)\le\log n,\qquad c(p)=\log p .
\]
The Dirichlet \(\zeta(w+1)\) factor acts on the original time histories with coefficients \(d^{-3/2}\); its inverse has coefficients \(\mu(d)d^{-3/2}\), also absolutely summable. The remaining gamma multiplier is an additional smoothing operator. The large-time first absolute majorant obtained by putting \(c(n)\le\log n\) before signed smoothing still has square-root-\(x\) scale. The gap is precisely the cancellation in the weighted \(c(n)\) sum or in the tilted temporal projection. The missing bound does not follow from the exponentially small untilted response. A single pure mode \(e^{pt}\) at a hypothetical rightward zero is suppressed by \(\widehat\Phi(p)=0\) and retained by \(\widehat{e^{-u}\Phi}(p)\ne0\).

## A local common-atom Gram measurement

There is an exact second readout for either attacking or checking amplitude estimates. With \(K_t(u,v)=\sum_{m\ge2}\Lambda(m)m^{-1}j(t+u-\log m)j(t+v-\log m)\), every finite \(K_t\) matrix is positive semidefinite. Put \(R(h)=\int j(v)j(v+h)dv\). The source moments give \(m_2=\int y^2e^{y/2}j(y)dy=2Q(1/2)>0\) with orders zero and one vanishing. At every \(t\),
\[
 \int_{-2s}^{2s}h^2e^{h/2}(K_t(0,h)-R(h))dh
 =m_2 e^{-t/2} P(t).
\]
For each active atom \(v=t-\log m\in[-s,s]\), the integration includes every shift needed for its pulse; substituting \(y=v+h\) gives \(m_2 e^{-v/2}\). The continuum term vanishes by \(\int e^{-v/2}j(v)dv=0\). This identity retains every proper power. Chebyshev bounds the kernels uniformly and the prime number theorem gives the continuum limit. Step 4 on this route needs the signed projection to be exponentially more accurate, to square-root scale up to the requested subexponential allowance. The two positive kernels alone do not price it.

**Qualification.** These are paper consequences for the original arithmetic coefficients. Both the independently bounded untilted observable and the precisely zero-visible tilt use the actual same-window arithmetic field. The all-positive-exponent signed upper for the visible tilt has not been established.
