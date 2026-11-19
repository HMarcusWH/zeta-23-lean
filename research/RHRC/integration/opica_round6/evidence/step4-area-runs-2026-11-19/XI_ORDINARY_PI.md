# Recovering recurrent negative blocks of the unweighted ordinary-prime area

**DERIVED paper result, 19 November 2026.** Let \(A_\pi(x)=\int_2^x(\pi(y)-\operatorname{li}(y))dy\). For every fixed \(N\ge0\), every sufficiently large \(X\) admits an \(x\) in
\[
 [\sqrt X(\log X)^N,\;X\sqrt{C\log X}]
 \quad\text{with}\quad A_\pi(x)\le-\frac{x^{3/2}}{2\log x}.
\]
The constant \(C\) is absolute. Moreover, for every fixed \(J>0\) there are \(\gg_J(\log x)^J\) consecutive negative quartic endpoints on one side of each such witness. A fixed-factor enlargement of the displayed window contains the entire block. No rightmost-zero hypothesis is required. This concerns the unweighted input \(\sum_p 1\), including the exact \(\operatorname{li}(2)\) endpoint. The argument is analytic and has no Lean or CI qualification.

## Exact prime-only change of source

For \(j=\pi,\vartheta\), set \(F_j(v)=e^{-3v/2}A_j(e^v)\) for \(v\ge v_0=\log2\), and set it to zero elsewhere. Use the Laplace transform parameter \(z\), with \(s=z+1/2\). Absolute convergence for \(\Re s>1\) and integration by parts give
\[
 \widehat F_\pi(z)=\frac{D_\pi(s)}{s(s+1)},\qquad
 D_\pi(s)=\sum_p p^{-s}-\operatorname{li}(2)2^{-s}
                       -\int_2^\infty \frac{x^{-s}}{\log x}dx.
\]
Indeed, the Stieltjes derivative of the discrepancy continued by zero below 2 has an atom from its lower endpoint. Likewise
\[
 D_\vartheta(s)=\sum_p(\log p)p^{-s}-2\cdot2^{-s}
                                    -\int_2^\infty x^{-s}dx,
 \qquad \widehat F_\vartheta(z)=D_\vartheta(s)/[s(s+1)].
\]
Thus \(D_\vartheta(s)=-D_\pi'(s)+b\,2^{-s}\) with \(b=\operatorname{li}(2)\log2-2\). Differentiating the full transform and inverting gives
\[
 F_\vartheta(v)=vF_\pi(v)-(g*F_\pi)(v)+B(v),\qquad
 g(u)=\mathbf1_{u\ge0}(e^{-u/2}+e^{-3u/2}),
\]
\[
 B(v)=b\,2^{-1/2}\mathbf1_{v\ge v_0}
   [e^{-(v-v_0)/2}-e^{-3(v-v_0)/2}].
\]
Laplace uniqueness applies to these causal functions of exponential order. The integrated areas are continuous. In particular the term \(g*F_\pi\) carries the full past of the ordinary prime field.

## A positive effective weight for the genuine unweighted area

Use the positive kernel \(K\) in [the weighted-area proof](XI_AREA_ECHO.md), with total mass \(M_K>0\) and \((K*F_\vartheta)(t)\to-2M_K/3\). For each horizon \(t>16\) set
\[
 r=\tfrac12-\frac4t,\qquad l_r(u)=\mathbf1_{u\ge0}e^{-ru},
 \qquad L_t=K*l_r .
\]
All convolutions here use this single fixed \(r\) at the given horizon. There is no differentiation of \(r\). The mass \(M_t=M_K/r\to2M_K\). The function \(K*F_\vartheta\) is bounded globally by its limit, continuity and rapid decay towards negative infinity. Dominated convergence applied against \(e^{-u/4}\mathbf1_{u\ge0}\) gives
\[
 (L_t*F_\vartheta)(t)\longrightarrow-\tfrac43M_K.
\]
Similarly \((L_t*B)(t)\to0\). Since \(g,l_r,K\) are positive and
\[
 (g*l_r)(u)=l_r(u)\left[
 \frac{1-e^{-(1/2-r)u}}{1/2-r}
 +\frac{1-e^{-(3/2-r)u}}{3/2-r}\right]\quad (u\ge0),
\]
we have \(0\le g*L_t\le(t/4+1)L_t\) pointwise. Using the exact prime-only relation above, and absolute Fubini at each fixed horizon, we obtain
\[
 \int_{v_0}^\infty [vL_t(t-v)-(g*L_t)(t-v)]F_\pi(v)\,dv
 \longrightarrow -\tfrac43 M_K .
\]
For \(v\ge t/2\), the bracket divided by \(v\) is between zero and \(L_t(t-v)\).

## Paying both tails

Uniformly for \(t>16\), \(L_t(u)\ll e^{-ru}\) for \(u\ge0\), by the finite tilted \(K\)-moment. For \(u<0\), \(L_t(u)\ll \exp(-c'e^{2|u|})\) by the double-exponential bound on \(K\) and \(r\ge1/4\). Let \(a_t=t/2+N\log t,\ d_t=t+\tfrac12\log(Ct)\) and take \(t\) sufficiently large that \(a_t<t\). The classical prime number theorem with its classical zero-free-region error gives, for every fixed \(D>0\),
\[
 |F_\pi(v)|\ll_D e^{v/2}(1+v)^{-D}\qquad(v\ge v_0).
\]
Alternatively this all-log version follows by summing the all-interval estimate in Guth and Maynard, Corollary 1.3, over dyadic ranges, taking steps of order \(x^{0.9}\) and accounting for \(O(x^{0.9})\) leftover lengths. On a full step of length \(y\), the integral of \(1/\log v\) differs from \(y/\log x\) by \(O(y^2/(x\log^2 x))\), which is absorbed. [Guth and Maynard, Corollary 1.3](https://arxiv.org/pdf/2405.20552#page=3)

For \(v_0\le v\le t/4\), the absolute contribution is \(O_D((1+t)^2e^{-t/5})\) for sufficiently large \(t\), since \(-rt+(r+1/2)t/4=-t/4+3\). For \(t/4\le v\le a_t\), integrate the majorant
\[
 O_D\!\left(t^{1-D}e^{-rt+(r+1/2)v}\right).
\]
The integral is \(O_D(t^{1-D+N})\) since \(-rt+(r+1/2)t/2=2\). This tends to zero for \(D>N+2\). For \(v>d_t\), the double-exponential tail of \(L_t(t-v)\) beats \((v+t)e^{v/2}\) with \(C\) sufficiently large. Thus both tails contribute \(o(1)\) to the full signed integral.

The remaining weight multiplying \(vF_\pi(v)\) is nonnegative and has integral at most \(M_t\). If \(vF_\pi(v)>-1/2\) throughout \([a_t,d_t]\), the full integral is at least \(-M_t/2-o(1)\), in contradiction with its limit \(-4M_K/3\). The witness gives the claimed estimate at \(x=e^v\). Any fixed depth constant \(0<c<2/3\) also works.

For the consecutive quartic points use \(H=x^{3/4}(\log x)^J\). Write \(D_\pi^\ast(x)=\pi(x)-\operatorname{li}(x)\). Corollary 1.3 gives \(|D_\pi^\ast(x+u)-D_\pi^\ast(x)|\ll_D H(\log x)^{-D}+x^{0.65}\) for all \(|u|\le H\): use the all-interval theorem above \(x^{0.65}\) and the elementary count for shorter intervals. Integrate this error and choose the side \(uD_\pi^\ast(x)\le0\). For \(D>2J+3\) the change in area on that side is at most \(o(x^{3/2}/\log x)\). Quartic spacing is \((4+o(1))x^{3/4}\). This proves the run-length assertion with every prime retained.

## What this resolves

There is also an independent check on the conditional power-window result in the [ordinary-prime isolator analysis](ORDINARY_POWER_WINDOWS.md). Reflect its compact positive isolator if necessary to use our convolution convention (or shift its support by a fixed constant). Replace \(K\) above by that measure and take fixed \(r<1/2\). The additional one-sided convolution multiplies the isolated mode \(e^{pt}\) by \(1/(r+p)\ne0\). Both isolated excursions therefore persist on bounded log-time intervals. If \(D=\sup_\rho\Re\rho-1/2>0\) and the target displacement is \(d\), the earlier history \(v\le\alpha t\) costs at most a polynomial times \(\exp((-r+\alpha(r+D))t)\), using \(|F_\pi(v)|\ll e^{Dv}\) from partial summation. For any fixed \(\alpha<1\) choose \(d\) sufficiently near \(D\) that this exponent is strictly smaller than \(d\). The effective weight on the remaining interval is positive, has bounded mass after division by \(v\), and has a fixed latest endpoint because the isolator is compact. Each excursion thus forces a corresponding pointwise signed excursion of \(vF_\pi(v)\) within that power window, with magnitude \(\gg e^{dt}\). This composition requires a hypothetical off-line zero. The unconditional negative-window theorem above uses the nonzero mean from prime squares instead.

This establishes deep negative runs for the actual unweighted prime discrepancy in every displayed broad window, including when the supremum of zero real parts is unattained. The desired upper on the number of consecutive positive quartic endpoints would require a witness in each block of \(O(M^{1-\delta})\) indices. Neither these historical weights nor the positive xi average provide that much localization. Step 4 and RH remain open.
