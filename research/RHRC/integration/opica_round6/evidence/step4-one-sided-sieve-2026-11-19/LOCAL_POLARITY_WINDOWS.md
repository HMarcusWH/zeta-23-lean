# What zero density pays for in an actual interval

**DERIVED on paper.** For each fixed exponent tolerance, the genuinely unopposed positive or negative rough Möbius charge can be bounded at the critical scale using only a fixed multiplicative neighborhood. The compensated part remains open. A second calculation shows just how locally compensation must occur under a hypothetical rightward zero. If the rightmost real part \(B>1/2\) is unattained, every interval \([U,(1+\lambda)U]\) of fixed relative width in the terminal range already contains both one-sided native node energies with exponent \(2B-1\) relative to \(U\). If \(B>.79\), a single complete dyadic shell suffices without an unattained-edge assumption. None of this excludes those zeros.

Freeze \(X,\ y=\lceil\log_2X\rceil^2\), and let \(\mu_y(q)=\mu(q)\mathbf1_{P^-(q)>y}\). The rough measure on log time is \(\lambda_y=\sum_{n\ge1}\mu_y(n)n^{-1/2}\delta_{\log n}\). It always uses the complete arithmetic source. Set \(E_y(s)=\prod_{p\le y}(1-p^{-s})^{-1}\). On \(\Re z>1/2\) the bilateral transform of \(\lambda_y\) is exactly \(E_y(1/2+z)/\zeta(1/2+z)\). The positive shift construction previously used with the absolutely convergent integrated prime-area formula is adapted here to this reciprocal, its possible multiple poles, the changing prime mask and the actual node graph. [Earlier prime-area isolator](../step4-area-runs-2026-11-19/DENSITY_ISOLATOR.md) · [One-sided native tree and weights](../step4-prime-transport-2026-11-19/ONE_SIDED_NODE_CHARGES.md)

## A positive filter of finite log width

Fix \(1/2<a<1\). The density estimate \(N(a,T)\ll_a T^{3(1-a)/(2-a)}\log^5 T\), counting multiplicity at positive ordinates, yields
\[
             W_a=\pi\sum_{\beta\ge a,\ \gamma>0}m_\rho/\gamma<\infty .
\]
Here and below, sums with the factor \(m_\rho\) are over distinct zeros \(\rho=\beta+i\gamma\). The exponent of \(T\) is strictly less than one. This counts all relevant high zeros even if infinitely many approach a nonattained edge. [Chourasiya and Simonič, Corollary 1](https://arxiv.org/html/2507.15184v2#S1)

For every such zero put \(d=\pi/\gamma,\ \delta_\rho=\beta-1/2\), and convolve with \(m_\rho\) copies of the probability on \(\{0,d\}\) with mass ratio \(\Pr(d)/\Pr(0)=e^{\delta_\rho d}\). Its Laplace transform is
\[
                L_\rho(z)=\frac{1+e^{\delta_\rho d}e^{-dz}}
                                  {1+e^{\delta_\rho d}} .
\]
The factor vanishes at \(z=\delta_\rho\pm i\gamma\). The infinite convolution is a probability on \([0,W_a]\), since the sum of the support lengths is finite; its transform is the product, locally uniformly, since on each compact set each factor differs from 1 by \(O(d)\). We may optionally spare one conjugate pair \(\rho_*,\bar\rho_*\) with \(\Re\rho_*=\beta_*>a\), omitting all copies for that pair. Choose the least positive ordinate on this particular line. A different canceled factor could vanish at the spared point only when its real part equals \(\beta_*\) and \(\gamma_*/\gamma\) is an odd positive integer. The choice excludes this. The remaining infinite product is nonzero there.

Let \(M(z)\) be this product. On every closed strip \(a<d_0\le\Re s\le2\), at large \(|\Im s|\),
\[
                   |M(s-1/2)/\zeta(s)|\ll_{a,d_0}(2+|\Im s|)^C .   \tag{1}
\]
To check the division at clusters of zeros, the local zeta product gives
\(\log|\zeta(s)|=\sum_{|\gamma-\Im s|\le1}\log|s-\rho|+O(\log(2+|\Im s|))\), zeros repeated with multiplicity. The unit band has \(O(\log(2+|\Im s|))\) zeros. The local product follows by subtracting the xi logarithmic derivatives at \(s\) and \(2+i\Im s\): the terms outside the unit band contribute \(O(\log(2+|\Im s|))\) after grouping by unit distances and using the local zero count, gamma and Euler-product terms satisfy the same bound, and taking real parts of the integral in \(\Re s\) gives the local product. In particular it can be read as an absolute-value estimate by continuity away from the zeros. For each local zero of real part below \(a\) the distance from the strip is at least \(d_0-a\). Each local zero at or above \(a\) has an assigned factor with \(|L_\rho(s-1/2)|\le C_0|s-\rho|\), by differentiating its explicit two-atom formula on \(\Re z\ge0\); negative ordinates use the conjugate zero of the same factor. At large height the spared pair is absent. All other probability factors have modulus at most one. Thus all small denominators cancel with their full multiplicities and the cost of the remaining constants is polynomial. This proves (1) without an assumed bound on inverse zeta derivatives.

To obtain a nonnegative Lipschitz density \(K\), additionally convolve with \(N>C+3\) uniform boxes of combined width \(\eta>0\), taking \(N\ge3\). Their transform on the strip costs \(O_\eta((1+|\Im s|)^{-N})\), and is nonzero at every point with \(\Re(s-1/2)>0\). The support of \(K\) has width at most \(W_a+\eta\). On the same strip the moving Euler factor has upper \(\exp(O_{d_0}(y^{1-d_0}))=X^{o_{d_0}(1)}\). Therefore we can invert the smoothed transform and move it from \(\Re s>1\) to any \(d_0>a\) (with \(d_0<\beta_*\) in the spared case). The horizontals disappear by (1) and the box decay. Compact frequency segments are bounded after removing the stated poles; the pole of zeta itself is a zero of its reciprocal. The residual integral satisfies
\[
                       O_{a,d_0,K}\big(X^{o(1)}e^{(d_0-1/2)t}\big). \tag{2}
\]
Inversion gives the actual finite sum \((K*\lambda_y)(t)\), since the test has compact support. Initially it follows from absolute convergence on \(\Re s>1\), continuity and Fourier inversion there. No cut on the ordinate is made.

## A one-sided charge that is paid independently

With all the above poles canceled, (2) is the whole answer. Given any requested \(\epsilon>0\), fix \(a,d_0\) so that \(0<a-1/2<d_0-1/2<\epsilon/8\). If desired, convolve once with a wider uniform box, then translate by a fixed amount: because all preceding mass is positive, this yields a compact Lipschitz \(K\ge c_\epsilon>0\) throughout \([-\log2,0]\). The added box preserves the contour upper. The support still lies in a fixed interval depending on \(\epsilon\), independent of \(X,U\), or the cutoff-dependent prime signs. It follows for each \(X^{.99}\le U\le X\) that
\[
           \left|\sum_q \mu_y(q)q^{-1/2}K(\log(U/q))\right|
                            \ll_\epsilon X^{\epsilon/4}.             \tag{3}
\]
This upper has no dependence on \(B\). The filter is defined using the actual zero set in a proof; it is not an enumerated numerical list or an arithmetic CI certificate.

Here is an explicit interpretation with the original node weights. Use interior shells whose fixed support neighborhood lies strictly inside the terminal range, with a one-shell margin, so all relevant shells and all their labels are native. Choose any depth \(k\) corresponding to a coarse level in the chosen shell of size \(U\). In that shell use the nodes at depth \(k\) as roots; in every other shell use the original base nodes. In each root use the minimum over the active labels of the actual nonnegative function \(q^{-1/2}K(\log(U/q))\). In every descendant use the increase of this minimum over its parent. Empty nodes contribute zero. Denote these coefficients by \(c_J\). This is the exact positive expansion of (3) through singleton leaves. All target-shell roots have \(c_J\ge c_\epsilon/(2U)^{1/2}\). At nonroot depth \(j\), in a shell of size \(V\asymp_\epsilon U\), the derivative bound gives \(c_J\ll_\epsilon V^{-1/2}2^{-s-j}\). This holds independently of the separately chosen starting depth \(k\).

Write \(f_J=\sum_{q\in J}\mu_y(q)\). The fine levels omitted in the coarse tree have total original energy \(O(\log X)\) by the absolute count. Their coefficient dual norm \(\sum_{\rm fine}c_J^2/w_J\) is \(X^{o(1)}\), since every fine node is a nonroot and a shell-depth with at most \(2^{s+j}\) nodes costs \(O_\epsilon(2^{-s})\). Thus fine levels can be removed from this particular positive charge relation with additive error \(X^{o(1)}\), uniformly in \(k\). In particular at either chosen polarity, putting
\[
 H_{U,k}^{\pm}=
 \left[
 \frac{c_\epsilon}{\sqrt{2U}}\sum_{J\ {\rm target\ roots}}[\pm f_J]_+
  -\sum_{J\ {\rm used\ coarse}}c_J[\mp f_J]_+
 \right]_+ ,
\]
gives \(H_{U,k}^\pm\ll_\epsilon X^{\epsilon/4}+X^{o(1)}\). Its weighted squared cost \(\sum_{U,k}2^{-k}(H_{U,k}^\pm)^2\ll_\epsilon X^\epsilon\) over interior shells follows by the geometric sum and the number of shells. This positive excess subtracts only genuinely opposite node charges in a fixed local neighborhood. In particular if a neighborhood's coarse charges all have the chosen sign, its target-level contribution to the original one-sided square mass is bounded by \(O_\epsilon(2^{-k}X^{\epsilon/2}+2^{-k}X^{o(1)})\), using \(\sum [f_J]_+^2\le(\sum [f_J]_+)^2\). A nonempty native signal can still be compensated by neighboring charges; (3) gives no critical upper for their individual absolute sizes.

There is a single **source-only dyadic statistic** with the same unconditional subpower upper. Choose any integer \(r(X)\to\infty\) as slowly as desired with \(r=o(\log X)\), for example \(\lceil\log_2(2+\lceil\log_2(2+s)\rceil)\rceil\). Require each of the \(2r+1\) neighboring shells to be wholly terminal. For shell \(V=2^i\) set \(d_V=2^{-\lfloor i/2\rfloor}\). At target shell \(U=2^j\) and chosen coarse depth \(k\), use the depth-\(k\) roots there and base roots in the other shells. Let
\[
 P=d_U\sum_{\rm target\ roots}[\pm f_J]_+,\qquad
 N=\sum_{|i-j|\le r} d_{2^i}
 \left(\sum_{\rm roots}[\mp f_J]_+
    +\sum_{\substack{\rm strict\ descendants\\\rm coarse}}
                            2^{-s-\operatorname{depth}(J)}[\mp f_J]_+\right).
\]
Then for either fixed sign the dyadic rational statistic
\[
                \sum_{U,k}2^{-k}[P-r(X)N]_+^2\ll_\epsilon X^\epsilon
                \quad\hbox{for all sufficiently large }X.           \tag{3a}
\]
Indeed for each fixed requested exponent the constant support radius and all coefficient ratios above are eventually smaller than \(r(X)\). On roots \(c_J\ll_K d_V\); increments satisfy the stated descendant bound, while every target root has \(c_J\gg_K d_U\). Enlarging the set of opposite charges only increases \(N\). Divide the filtered inequality by its fixed lower coefficient constant and sum the resulting squared upper using \(\sum_k2^{-k}\le2\). Thus (3a) evaluates solely the original signed integers, dyadic weights and finite tree. No zero-dependent coefficient enters its definition. The factor \(r(X)\) prices opposite mass; (3a) cannot bound a large charge that has sufficiently much opposite mass nearby.

## A fixed multiplicative packet if a rightward zero exists

Now spare the selected pair. At \(s=\rho_*=\beta_*+i\gamma_*\) of multiplicity \(m\), the leading residue coefficient in the inversion is
\[
  C_X=\frac{m!\,\widehat K_L(\rho_*-1/2) E_y(\rho_*)}
               {(m-1)!\,\zeta^{(m)}(\rho_*)},
 \qquad \widehat K_L(z)=\int e^{-zu}K(u)\,du .
\]
Use the narrow kernel of width \(W_a+\eta\), without the broad plateau in (3). Then \(C_X\ne0\), and \(\exp(-O(y^{1-\beta_*}))\ll|E_y(\rho_*)|\ll\exp(O(y^{1-\beta_*}))\) from the finite factors. This is \(X^{\pm o(1)}\). For each fixed \(j\ge1\), logarithmic derivatives of \(E_y\) of order \(j\) at \(\rho_*\) are \(O_{\rho_*,j}(y^{1-\beta_*}\log^j(2y))\). This follows by termwise differentiation of the finite sum of Euler logarithms and their convergent prime-power series. Consequently \(E_y^{(j)}(\rho_*)/E_y(\rho_*)=O((\log X)^{j(2-2\beta_*)+o(1)})\). Since \(\beta_*>1/2\), this is \(o((\log X)^j)\). Thus for \(t\asymp \log X\) the whole smoothed response is
\[
 2e^{(\beta_*-1/2)t} t^{m-1}
   \big(\Re(C_Xe^{i\gamma_*t})+o(|C_X|)\big)
   +O(X^{o(1)}e^{(d_0-1/2)t}).                                    \tag{4}
\]
The little-oh is uniform on this \(t\) range for the fixed selected zero, includes all derivatives from every lower term of its pole, and allows the phase of \(C_X\) to change at each horizon.

Let a packet \([U,e^L U]\) be contained in the true terminal interval with \(L>W_a+2\pi/\gamma_*\), allowing extra strict room for the arbitrarily small smoothing width and endpoint margins. Choose \(t\) so its whole test-support interval lies strictly inside the packet. The available \(t\)-interval contains a complete period. At both extrema of the leading cosine in (4) the error is smaller by a strict power or by \(o(1)\) relative to its amplitude. Thus at the same \(X\) both polarities of the actual smooth observations have size at least \(U^{\beta_*-1/2-o(1)}\). Positive interpolation from original base nodes to leaves, as in [the original sign transfer](../step4-prime-transport-2026-11-19/ONE_SIDED_NODE_CHARGES.md), costs \(X^{o(1)}\) for the fixed bounded Lipschitz test. The input support has a fixed positive log margin inside the packet, whereas the relative base widths tend to zero. Only original nodes entirely inside the packet can have a nonzero test coefficient. Fine levels again cost \(O(\log X)\). Both one-sided coarse node energies inside that packet are therefore \(\ge U^{2\beta_*-1-o(1)}\) for every sufficiently large \(X\), uniformly in the location of an allowed packet.

If \(B>1/2\) is unattained, choose \(a_j\uparrow B\) with \(a_1>1/2\). The summable majorant at \(a_1\) shows \(W_{a_j}\to0\). Select actual real parts \(\beta_j>a_j\); the least ordinate on these lines tends to infinity. For **each fixed** \(L>0\), the width and frequency conditions ultimately hold and \(\beta_j\to B\). The packet upper \(U^{2B-1+o(1)}\) follows from the existing rough restricted Mertens/tree estimate on these \(O_L(1)\) comparable shells. Consequently **both** polarity energies have exact exponent \(2B-1\) in that packet at all sufficiently late cutoffs. The limit in \(X\) is taken first. There is no uniform shrinking-packet estimate.

At an attained edge, choose the least ordinate on \(\beta_*=B\). Any \(L>W_a+2\pi/\gamma_*\) still works. The tested height gives two effective examples. Platt and Trudgian verified that \(\beta=1/2\) throughout \(0<\gamma\le H=3\cdot10^{12}\). Integrating the explicit density upper gives
\[
 W_a=\pi\int_H^\infty \frac{N(a,t)}{t^2}\,dt .
\]
For \(a=.79,.80\) the row of Chourasiya and Simonič gives \(N(a,t)\le17.21 t^{1-e}(\log t)^v+6.826\log^2t+121.1\log t\), \(e=(2a-1)/(2-a)\), \(v=(7-5a)/(2-a)\). With \(D=\log H\), the first integral is at most \(17.21 H^{-e}D^v/(e-v/D)\), since \((D+r)^v\le D^v e^{vr/D}\). The others integrate to \(6.826(D^2+2D+2)/H\) and \(121.1(D+1)/H\). Including \(\pi\), the two resulting upper bounds are respectively below \(0.684343\) and \(0.334399\). Adding \(2\pi/H\) still leaves more than \(0.001\) in \(\log 2\) and \(\log(7/5)\), respectively. Hence if \(B>.79\), every sufficiently late whole native dyadic shell already has both polarity energies with full exponent \(2B-1\); if \(B>.80\), a factor-\(7/5\) packet suffices. [Verified critical zeros](https://arxiv.org/abs/2004.09765) · [Explicit zero density, Table 1](https://arxiv.org/html/2507.15184v2#S1) · [Arb check](check_density_windows.py) · [Interval receipt](DENSITY_WINDOWS_CHECK.json)

Selecting a late horizon or averaging many neighboring cutoffs cannot remove either sign in these regimes. The compact filter pays for unopposed signed excess but leaves open the critical upper on excess accompanied by nearby compensation. No new formal theorem, proof of RH, or claim of Step 4 closure follows.
