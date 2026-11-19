# What a single actual prime probe measures

**DERIVED on paper.** The genuine prime probe alone detects every displacement, including the supremum endpoint \(B=1\). The genuine small-cofactor cone probe alone also suffices when \(B<1\). The shorter-scale proof below uses only coordinates of the original tree at \(X\). The prime endpoint uses an independently checked positive-kernel argument, with normalization, full future history, padding, and the original observation grid treated explicitly. The [two-probe result](TWO_ARITHMETIC_PROBES.md) covers that endpoint by a different calculation. The upper needed for Step 4 remains **OPEN**.

Use the real weighted node vectors \(F,P,A\), coarse or complete, from [the two-probe paper](TWO_ARITHMETIC_PROBES.md). Write \(b=B-1/2\) and
\(\Delta(Q,F)=\|Q\|^2\|F\|^2-\langle Q,F\rangle^2\).
The known terminal positive energy gives \(\|F\|\le X^{b+o(1)}\). Each probe \(Q=P,A\) has \(\|Q\|=X^{1/2+o(1)}\) by the whole-shell prime or cone drift and the unsigned node bound. Thus its minimizing real projection coefficient \(c_X=\langle F,Q\rangle/\|Q\|^2\) satisfies
\[
                    |c_X|\le X^{b-1/2+o(1)}.                       \tag{1}
\]

## The smaller observation inside the original array

Fix \(0<\sigma<.01\) and take \(Y=2^{\lfloor(1-\sigma)\log_2 X\rfloor}\). Use the complete source at the frozen roughness cutoff \(y=\lceil\log_2X\rceil^2\) throughout, including when evaluating the source at \(Y\) and \(Y/2\). Since \(y=(\log Y)^{2+o(1)}\), the Rankin cost, restricted Mertens estimates and fixed-band lower of [the rough-source proof](ROUGH_PRIME_TRANSPORT.md) all apply at \(Y\) with this same mask. In particular for every small fixed \(\ell>0\) the full source through \(Y\) has norm \(\gg Y^{b-\ell}\) on a bounded band fixed before \(X\). Its part \(q\le X^{.99}\) has band norm \(O_\eta(X^{.99b+\eta})\) by rough partial summation. As \((1-\sigma)b>.99b\) when \(b>0\), make \(\ell,\eta\) sufficiently small to retain the lower. The endpoint \(Y\) is a power of two with zero label.

Restrict the *actual \(X\)-vector* to its shell coordinates \(U<Y\), preserving its clipped lower terminal shell at \(X^{.99}\). These disjoint shells contain precisely the wanted nonzero input labels \(X^{.99}<q<Y\). Keep \(s=s(X)\), the original aligned bases of width \(U2^{-s}\), and the original weights \(2^{-k}/U\). Telescoping \(q^{-1/2-it}\) down these actual cells gives the bound of equation (3) in [the dyadic tree paper](../step4-harmonic-recovery-2026-11-19/DYADIC_TREE.md). Its proof requires only bounded derivative in \(q/U\) on the fixed band, at most \(O(\log X)\) depths, and \(O(2^{s(X)}\log X)=X^{o(1)}\) bases. The last-half fine levels have positive energy \(O(\log X)\) by the absolute node count, also on a subset of shells. Thus the restricted full or coarse vector satisfies
\[
                  \|F_{\rm inner}\|\ge X^{(1-\sigma)b-o(1)}.       \tag{2}
\]
Here the \(o(1)\) exponent records taking the lower limit first and then \(\ell\) arbitrarily small. No rebinning to \(s(Y)\), nor using the native terminal boundary \(Y^{.99}\), enters the argument.

The restricted probe obeys \(\|Q_{\rm inner}\|\ll Y^{1/2+o(1)}\) by absolute tree counting in shells \(U<Y\). If \(0<b<1/2\), its multiple from (1) is smaller in this inner projection than (2) by the strict factor \(X^{-\sigma(1/2-b)+o(1)}\). Consequently
\[
 \Delta(Q,F)=\|Q\|^2\|F-c_XQ\|^2
       \ \ge\ X^{1+2(1-\sigma)b-o(1)} .
\]
Taking the lower limit, then \(\sigma\downarrow0\), and using the upper \(\|Q\|^2\|F\|^2\), gives exponent \(1+2b\) at every sufficiently large cutoff. For \(b=0\), the ordinary upper and the baseline one give \(1+\Delta(Q,F)/X=X^{o(1)}\). For \(b=1/2\) the scale comparison loses its strict gap.

## A sign test for the endpoint prime probe

This argument concerns the actual prime vector \(P\), whose entries all have one sign. Continue to freeze \(X,y\), and write \(T=\log X\). As an auxiliary observation of these same unchanged arithmetic labels take \(h=\mathbf1_{[0,1]}*\mathbf1_{[0,1]}\), a globally Lipschitz nonnegative triangular function supported in \([0,C]\) with \(C=2\). Its bilateral transform \(H(z)=((1-e^{-z})/z)^2\) is nonzero at every \(z=\rho-1/2\) with \(\Re\rho>1/2\). The finite centered argument in [the fixed-band construction](../step4-harmonic-recovery-2026-11-19/FIXED_BAND_THEOREM.md) uses only the literal finite identity \(u_y*v_h=g_h\), compact support and the displayed nonzero transform. It applies to this triangular test without any change to the prime probe or Möbius coefficients.

Define the **full infinite**, locally finite causal history
\[
 W(t)=\sum_{q\ge1}\mu_y(q)q^{-1/2}h(t-\log q).
\]
It is zero for \(t<0\) and \(|W(t)|\ll e^{t/2}\) for \(t\ge0\). More precisely for \(0\le t\le T\), \(|W(t)|\ll_\epsilon X^\epsilon e^{bt}\) follows from the rough Mertens estimate and partial summation on the fixed interval \(e^{t-C}\le q\le e^t\). At \(B=1\) the elementary upper suffices. All constants of \(h\) are fixed independent of the horizon.

Take \(0<\sigma<.005,\ t_1=(.99+\sigma)T,\ t_2=(1-\sigma)T\). At the shorter horizon \(e^{t_2}\) use the rough centered identity with fixed causal test \(h\) and any fixed rightward zero with \(\delta=\Re\rho-1/2\). For clarity, its normalized integral in this notation is
\[
 \int_0^{t_2}|W(t)|^2dt
  =\int_1^{e^{t_2}} |v_h(u)|^2\,du/u^2
  \gg_\rho e^{2\delta t_2}|H(\rho-1/2)|^2
           \left(\sum_{\substack{d\mid\prod_{5\le p\le y}p\\d\le e^{t_2}}}
                        d^{-1/2}\right)^{-2}.
\]
Here \(g_h(u)=u^{1/2}h(\log u)\) and \(v_h(u)=\sum_{q\le u}\mu_y(q)g_h(u/q)\), so the equality uses \(W(t)=e^{-t/2}v_h(e^t)\). Compact support fits before both centered endpoints eventually. The divisor sum is \(X^{o(1)}\) by the Rankin estimate at \(e^{t_2}\). Taking \(\delta\) arbitrarily close to \(b>0\), then dividing the squared-integral lower by the supremum bound on \([0,t_2]\), shows
\[
             \int_{t_1}^{t_2}|W(t)|dt\ge X^{(1-\sigma)b-o(1)}.     \tag{3}
\]
The omitted early integral costs \(O_\epsilon(X^\epsilon e^{bt_1}T)\), a strict power smaller because \(t_1<t_2\). For each prescribed loss choose \(\rho\) first and keep it fixed.

Use the positive even kernel \(K\) with \(K(t)\ll\exp(-c e^{2|t|})\) and bilateral transform \(\xi(1/2+z)\). Its normalization, positivity and decay are given in [XI_AREA_ECHO.md](../step4-area-runs-2026-11-19/XI_AREA_ECHO.md). On \(\Re z>1/2\) absolute convergence for the infinite history and for the kernel gives the bilateral transform of \(K*W\), with \(s=1/2+z\),
\[
 H(z)\xi(s)\frac{1}{\zeta(s)}
       \prod_{p\le y}(1-p^{-s})^{-1}
 =H(z)\frac{s(s-1)}2\,\pi^{-s/2}\Gamma(s/2)
        \prod_{p\le y}(1-p^{-s})^{-1}.                              \tag{4}
\]
Shift the inverse bilateral transform to \(\Re z=\epsilon_0>0\) for any fixed \(\epsilon_0<1/2\). On the intervening fixed strip the finite Euler product costs \(\exp(O_{\epsilon_0}(y^{1/2-\epsilon_0}))=X^{o_{\epsilon_0}(1)}\); the gamma factor decays exponentially in height and \(H\) is bounded. The right side has no poles in that strip. Inversion holds pointwise by continuity and absolute integrability on the initial line. This gives \(|K*W(t)|\ll_{\epsilon_0}X^{o_{\epsilon_0}(1)}e^{\epsilon_0 t}\). No future portion of the history has been replaced in this inverse transform.

Put \(I=[t_1,t_2]\), \(L=2\log(T+2)\), and enlarge \(I\) by \(L\) on each side to \(I'\), and by \(2L\) on each side to \(I''\). Let \(w(u)=\int_{I'}K(t-u)dt\). It is nonnegative, at most \(\|K\|_1\), and at least a fixed positive constant on \(I\). Integration of (4) and absolute Fubini give \(|\int_{\mathbb R}wW|\ll_{\epsilon_0} T X^{\epsilon_0+o(1)}\). All \(u\notin I''\) contribute \(O(X^{-10})\) in absolute value for sufficiently large \(X\): on the lower tail use causality, \(|W(u)|\ll e^{u/2}\), and \(w(u)\ll T\exp(-c e^{2L})\). On the upper tail bound its integral by a constant times \(T e^{(t_2+2L)/2}\int_0^\infty e^{r/2}\exp(-c e^{2(L+r)})dr\). This also exhibits explicitly the cost of every untruncated future input. By (3), \(\int_{I''}w|W|\ge X^{(1-\sigma)b-o(1)}\); take \(\epsilon_0<(1-\sigma)b/2\). Decomposing into positive and negative parts gives, for each sign at the same \(X\),
\[
           \int_{I''} [\pm W(t)]_+dt \ge X^{(1-\sigma)b-o(1)}.      \tag{5}
\]

On \(I''\), the support \(e^{t-C}\le q\le e^t\) is strictly inside \((X^{.99},X)\) once \(X\) is large. Every original input influencing \(W\) on this interval is therefore a native terminal graph vertex. The corresponding prime response \(W_P(t)=-\sum_{p>y}p^{-1/2}h(t-\log p)\) is nonpositive. For any real \(c\), \(|W-cW_P|\) majorizes \([W]_+\) if \(c\ge0\) and \([-W]_+\) if \(c<0\). Thus (5) gives the same lower integral for the error of the minimizing \(c=c_X\).

To transfer it, in shell \(U\) write the testing weight as \(U^{-1/2}f_{t,U}(q/U)\) with \(f_{t,U}(v)=v^{-1/2}h(t-\log U-\log v)\). These functions have uniformly bounded sup norms and Lipschitz constants for \(1\le v\le2\), simultaneously in \(t,U\). Telescoping the left-grid-endpoint approximations on the actual \(s(X)\)-grid for these functions gives pointwise
\[
 |W(t)-c_XW_P(t)|\ll X^{o(1)}\|F_{\rm all}-c_XP_{\rm all}\|.
\]
Indeed in one base at depth \(k\) the coefficient increment is \(O(2^{-s}2^{-k})\) before multiplication by \(U^{-1/2}\); summing at most \(2^k\) charges by Cauchy and the \(O(\log X)\) depths gives the native weighted-node norm as in the original tree proof. Then apply Cauchy over \(O(2^{s(X)}\log X)\) bases. No new cutoff, shell, or evaluation grid is introduced. For the coarse-only observable choose \(c_X\) from the coarse projection. By (1) it obeys \(|c_X|\le X^{o(1)}\) since \(b\le1/2\). The fine squared norm of this same linear combination is \(O((1+|c_X|)^2\log X)=X^{o(1)}\) by the unsigned last-half estimate, so it can be subtracted after using (5). Integrating the pointwise bound over an interval of length \(O(\log X)\) gives \(\|F-c_XP\|\ge X^{(1-\sigma)b-o(1)}\) in either graph. Since \(\|P\|^2=X^{1+o(1)}\), the quantitative steps of this sign argument imply the same prime determinant exponent at \(b=1/2\) after \(\sigma\downarrow0\).

The sign argument uses all rough-history inputs during the two-sided smoothing and only restricts to native terminal vertices after obtaining (5). It does not apply to the signed cone probe \(A\). Neither argument here bounds the determinant by \(X^{1+\epsilon}\) independently of the actual zero exponent.
