# Signed prime shares on the same unbalanced rough source

**DERIVED on paper, 20 November 2026.** A whole class of genuine rough labels has a negative unweighted charge, a single largest-prime share with a strongly cancelling signed charge, and a positive two-prime share. The three measurements use precisely the same labels. Each conclusion holds on every native base cell in a complete terminal shell. There is also an independent cancellation of the **unweighted** charge of two angular sectors of opposite large-prime parity. It works separately for each small cofactor. The estimate for their union still falls short of the required covariance bound.

## Actual rows and uniform range

Fix the native \(X,y=\lceil\log_2X\rceil^2\). Let \([U,2U)\) be any complete terminal shell, \(L=\log U\), \(P_y=\prod_{p\le y}(1-1/p)^{-1}\), and \(Z=U^\kappa\). The source is \(\mu_y(a)=\mu(a){\bf1}_{P^-(a)>y}\), with \(\mu_y(1)=1\). Fix an integer \(k\ge2\). In the ordered simplex \(r_1<\cdots<r_k\), \(\sum r_i=1\), take a fixed convex polytope \(D\) of positive relative volume, bounded away from the coordinate faces and the equalities between successive coordinates. The measure is \(dr_1\cdots dr_{k-1}\) with \(r_k=1-\sum_{i<k}r_i\). One may require \(r_k-r_{k-1}>d>0\) and put \(r_k\) arbitrarily close to one before fixing \(D\). Set \(r_*=\inf_D r_1>0\) and choose \(0<\kappa<(1-\kappa)r_*\).

Take exactly the squarefree rows
\[
 n=a p_1\cdots p_k\in[U,2U),\quad a\le Z,\quad \mu_y(a)\ne0,\qquad
 r_i=\frac{\log p_i}{\log(n/a)}\in D\ \text{jointly}.
\]
The notation means the vector belongs to \(D\). The primes are distinct, ordered and larger than \(a,y\), since \(p_i\ge U^{(1-\kappa)r_*}\). Consequently \(p_1,\ldots,p_k\) are the actual largest \(k\) primes of \(n\). Every label occurs once and its sign equals \((-1)^k\mu_y(a)\). For large \(U\), \(n/P^+(n)\ge U^{(1-\kappa)r_*}\). Common boundaries may consistently be taken half-open throughout.

For \(I\subset\{1,\ldots,k\}\) with \(\ell=|I|\), let \(S_{D,I}(J)\) sum the actual signs times \(\prod_{i\in I}\log p_i/\log n\) in an interval \(J\subset[U,2U)\). Each factor is the literal divisor share in \(\log n=\sum_{p\mid n}\log p\) on these squarefree rows. No new sign, permutation, or model of an individual row is introduced. Set
\[
 C_{D,I}=\int_D\frac{\prod_{i\in I}r_i}{\prod_{j=1}^k r_j}\,dr_1\cdots dr_{k-1}>0,
 \qquad \Phi(L)=L^{3/5}(\log L)^{-1/5}.
\]

## The common cofactor kernel

For some \(c>0\) depending on the fixed geometry, uniformly in both endpoints,
\[
 S_{D,I}(J)=(-1)^k C_{D,I}\int_J
 \sum_{a\le Z}\frac{\mu_y(a)}a
 \frac{(\log u-\log a)^{\ell-1}}{(\log u)^\ell}\,du
 +O\big(Ue^{-c\Phi(L)}\big).                                      \tag{1}
\]
This formula also holds on replacing \(\mu_y(a)\) on both sides by \(b(a)\mu_y(a)\), uniformly over all \(|b(a)|\le1\). In particular \(b\) may choose any common subset of the cofactors. The primality of every marked large factor stays in the sum.

To see this, express each prime sum as Stieltjes integration against \(d\vartheta(t)/\log t\). Replace these factors one at a time by \(dt/\log t\). With the other variables fixed, every angular inequality becomes linear in the remaining \(\log t\) after multiplication by the positive sum of all the logarithms. The product constraint from \(J\) is also an interval. Every nonempty slice thus uses one interval \([A,B]\subset[U^{(1-\kappa)r_*},2U/(a\prod_{j\ne i}p_j)]\), where integrated coordinates replace \(p_j\) at intermediate steps. Its weight is \(1/\log t\) times products of at most \(k\) positive log shares bounded by one. Its supremum and total variation are \(O_k(1)\) on that interval. For example, its derivative is bounded by \(C_k/(tL)\), with the other logarithms held fixed. Partial summation with the Vinogradov–Korobov bound for \(\vartheta(t)-t\) gives \(O(B e^{-c_0\Phi(L)})\), including endpoints. Integrating \(B\)'s upper bound over the other variables costs at most fixed powers of \(\log U\), since their remaining measures are \(dt/\log t\) or prime counting and have harmonic integral \(O(\log U)\). Summing \(1/a\) against \(|b(a)\mu_y(a)|\) costs \(O(\log U)\). Reduce \(c_0\) to absorb these costs. In the continuum set \(l_i=\log p_i\), \(S=\sum l_i=\log(u/a)\). The Jacobian \(dl_1\cdots dl_k=S^{k-1}dS\,dr_1\cdots dr_{k-1}\), the density \(\prod dp_i/\log p_i=e^S\prod dl_i/l_i\), and the product of the log shares give (1). The fixed ordering accounts for all multiplicities without a factorial divisor. [Johnston and Yang, Theorem 1.4](https://arxiv.org/html/2204.01980v2)

## The first three measurements

For \(J\) of length \(H\) with \(H\ge U\exp(-L^\sigma)\), fix \(1/2<\sigma<3/5\). This includes every native base cell for large \(X\). Uniformly on these intervals,
\[
\begin{aligned}
 S_{D,\varnothing}(J)&=(-1)^{k+1} C_{D,\varnothing}
       \frac{H P_y}{L^2}\left(1+O\left(\frac{1+\log y}{L}\right)\right),\\
 |S_{D,\{k\}}(J)|&\ll U e^{-c\Phi(L)},\\
 S_{D,\{k-1,k\}}(J)&=(-1)^k C_{D,\{k-1,k\}}
       \frac{H P_y}{L^2}\left(1+O\left(\frac1L\right)\right).
\end{aligned}                                                       \tag{2}
\]
The middle bound in fact holds on every \(J\). For \(k=2\), \(D\) may simply be \(r_0<r_1<r'_0<1/2\) (here \(r_0,r'_0\) are the interval endpoints). The constants are, respectively, \(\int_{r_0}^{r'_0}dr/[r(1-r)]\), \(\int_{r_0}^{r'_0}dr/r\) and \(r'_0-r_0\). A highly uneven split therefore still has negative raw charge and positive double share.

For completeness, the elementary signed cofactor inputs used in (2), at \(l=\log u\), are
\[
 \sum_{a\le Z}\frac{\mu_y(a)}{a(l-\log a)}
 =-\frac{P_y}{l^2}+O_\kappa\!\left(\frac{P_y(1+\log y)}{L^3}\right),\quad
 \sum_{a\le Z}\frac{\mu_y(a)}a=O(e^{-c\Phi(L)}),\quad
 \sum_{a\le Z}\frac{\mu_y(a)\log a}a=-P_y+O(e^{-c\Phi(L)}).
\]
The first is precisely the previously derived uniform reciprocal expansion for the one-prime cone. Its proof takes \(\log Z/\log U\) bounded strictly below one and works for any fixed \(\kappa<1\); one may restrict our \(\kappa<.01\) to use exactly its published range. The last two are the first reciprocal moments of \(\zeta(s)^{-1}\prod_{p\le y}(1-p^{-s})^{-1}\) at \(s=1\). For their uniform truncation error, freeze \(y\) and write \(\mu_y=\mu*{\bf1}_{y\text{-smooth}}\), with all powers included. At \(t\ge Z\) split the smooth variable \(d\) at \(\sqrt t\). Below the split, the unconditional Mertens bound at \(t/d\) gives \(tP_y e^{-c\Phi(\log t)}\). Above it, use \(1/\log y\) in Rankin's bound to pay \(O(t(\log y)^C e^{-\log t/(2\log y)})\). Uniformly \(\log y=O(\log\log U)\); this tail is absorbed upon reducing \(c\). Partial summation with \(1/a\) and \(\log a/a\) gives the stated exponential errors at \(Z\), again with adjusted constants. It justifies identifying the limits with the right-hand value and negative derivative of this Dirichlet series at one. In (1), the raw kernel uses the first expansion, the single share is constant in \(a\), and the double share is affine in \(\log a\). [Original one-prime cone calculation](../step4-prime-transport-2026-11-19/CONE_DRIFT.md) · [Lee and Leong, unconditional Mertens estimates](https://arxiv.org/abs/2208.06141)

Each basket has positive density relative to the true squarefree \(y\)-rough population on the intervals of (2). Indeed the unsigned version of (1) uses \(|\mu_y(a)|\). For \(\sqrt Z\le t\le Z\), inclusion–exclusion for primes \(\le y\) at adjacent orders \(C\log\log U\) gives rough count \(t(P_y^{-1}+o(P_y^{-1}))+U^{o(1)}\). The floor and Euler remainders follow from \(y^{C\log\log U}=U^{o(1)}\) and the exponential-series tail. Squareful rough integers through \(t\) cost at most \(t\sum_{m>y}m^{-2}\ll t/y\). Partial summation gives \(\sum_{\sqrt Z<a\le Z}|\mu_y(a)|/a\gg_\kappa L/P_y\). The unsigned continuum kernel divided by \(1/a\) is \(\asymp_D1/L\). The basket contains \(\gg_{D,\kappa} H/P_y\) genuine labels. A direct Bonferroni estimate with floor errors \(U^{o(1)}\) bounds the total rough population of \(J\) by \(O(H/P_y)\). This is a lower bound for density with constants fixed in advance, even though the constant can be small for a sharply unequal split.

## Signed cancellation between two genuine baskets

Choose ordered polytopes \(D_k,D_{k+1}\) of positive volume with
\(C_{D_k,\varnothing}=C_{D_{k+1},\varnothing}=C>0\). These exist with either largest-prime proportion arbitrarily close to one. Begin with small polytopes inside the desired separated regions, choose \(C\) below both raw angular volumes and shrink each continuously toward an interior point. Fix one \(\kappa\) small enough for both. The sets of integer labels are disjoint. A row in the larger basket has its \((k+1)\)st largest factor greater than \(Z\); in the smaller basket that factor, if present, divides \(a\le Z\).

On the union the **original unweighted signed charge** satisfies
\[
 \left|\sum_{\substack{n\in J\\ n\text{ in either basket}}}
         b(a_n)\mu_y(n)\right|
 \ll_{D_k,D_{k+1},\kappa} U e^{-c\Phi(L)},\qquad |b(a)|\le1 .       \tag{3}
\]
The kernels in (1) cancel exactly for every \(a\) and every \(u\). Since the \(b(a)\) may choose the sign of each residual, (3) also bounds the sum of the absolute **discrepancies of the two counts within each squarefree cofactor**, before multiplication by \(\mu_y(a)\). This is independent cancellation on positive-density labels, uniformly at both native endpoints. It uses one common cofactor weight in the two baskets. An independently chosen function of all large prime positions may destroy the equality of the angular integrals.

If one invokes a separately justified bound \(\vartheta(t)-t\ll_s t^s\) for \(1/2<s<1\), the same proof improves (3) to \(O_\epsilon(U^{1-m(1-s)+\epsilon})\), where \(m\) is the smaller of the two lower exponents \((1-\kappa)\inf_D r_1\). At every nonempty slice \(B\ge U^m\), so \(B^s\le B U^{-m(1-s)}\). There is no Mertens hypothesis in this two-basket improvement. The exponent remains larger than \(1/2\).

## What this says about the native covariance

On a complete shell with \(U\asymp X\), the individual base-cell charges in (2) force one-sided energy of magnitude at least \(U2^{-s_X} P_y^2/(\log U)^4=X^{1-o(1)}\) on the raw basket with its own polarity. Here the base weight is \(1/U\), its width \(U2^{-s_X}\), and it has \(2^{s_X}\) cells. The same estimate holds for the opposite polarity of the double-share field. The full shell charge on each base cell is \(O(U e^{-c\Phi(L)})\) directly from the rough Mertens estimate at its endpoints. The complementary *actual* unweighted labels hence compensate the raw basket's drift on each such cell. Equation (3) identifies a specific complementary basket at this precision. No sign assumption on unselected data was used.

The power of the error in (3) is still \(U^{1-o(1)}\). Squaring it can leave power-sized weighted energy; the calculation does not retire the union from the complete tree at subpower cost. The earlier removal of atypical histories and spent partners is selection-dependent. The theorem here holds before this selection and remains valid under any common multiplier depending on \(a\) alone. It does not assert the same estimate under that full selector or after a GCD condition on pairs. Fixed \(k\) counts only the marked large factors; \(a\) retains all its permitted factors and their signs. The signed bound for the full surviving source, Step 4 and RH remain **OPEN**. [Exact survivor definition and cost](../step4-one-sided-sieve-2026-11-19/PRIME_FACTOR_PATHS.md) · [Three-factor parity and selection limits](../step4-one-sided-sieve-2026-11-19/SMALL_PART_LARGE_PART.md)

## Check with fixed absolute prime thresholds

A second check uses a different mask. Take \(p_1>U^\alpha\) and \(p_k>U^d p_{k-1}\), where \(0<\kappa<\alpha\), \(d>0\), and \(\kappa+k\alpha+d<1\). For the product of all \(k\) log shares the continuum density before summing the cofactor is
\[
 \frac{(\log u-\log a-(k\alpha+d)L)^{k-1}}
      {k!(k-1)!(\log u)^k}.
\]
Indeed in log-prime variables subtract \(\alpha L\) from each coordinate and a further \(dL\) from the last. The resulting section is an ordered simplex. Ties have continuum measure zero. The discrete prime inequalities may be taken strict; the same uniform one-coordinate Stieltjes bound controls all boundaries. The denominator displayed is per \(du/a\). Thus for \(k=2\) the first signed moment gives exactly the coefficient \(+P_y/2\) on the \(H/L^2\) scale, independent of \(d\). For general fixed \(k\ge2\), that coefficient is
\[
 (-1)^k P_y\,\frac{(1-k\alpha-d)^{k-2}}{k!(k-2)!}.
\]
The zeroth moment vanishes up to the exponential truncation error. For \(j\ge2\) the complete \(j\)-th reciprocal log moment is \(O_j(P_y(1+\log y)^{j-1})\): differentiate the finite Euler product times \(1/\zeta(s)\) at its simple zero \(s=1\), using \(\sum_{p\le y}(\log p)^i/p=O_i((1+\log y)^i)\). Truncating any fixed-order moment costs \(O_j(e^{-c_j\Phi(L)})\) by the earlier tail argument. Higher moments therefore give relative \(O_{k,\alpha,d}((1+\log y)/L)\). This is an independent normalization check on the two-share effect. The angular sectors in (3) use relative log-prime proportions and are the ones with exactly matching unweighted kernels.
