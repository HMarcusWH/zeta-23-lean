# A sharp threshold for independent prime-factor fingerprints

**DERIVED on paper.** Resolve all the individual primes from the native roughness \(y=\lceil\log_2 X\rceil^2\) up through \(z=(\log X)^K\), with fixed \(K>2\). On the actual OPICA tree the squared total-variation discrepancy from the squarefree Euler law has the exact power \(X^{1-2/K+o(1)}\). For \(z=(\log X)^{2+o(1)}\) it costs only \(X^{o(1)}\) (with 1 added to the energy). The excess for \(K>2\) already occurs on a single complete terminal shell. An explicit signed prime-count probe has the same obstruction in the larger range. This restricts an attempted use of small-prime observations to close Step 4.

## Object measured

Use the base cells, descendants and weights of [PR 303's one-sided detector](../step4-prime-transport-2026-11-19/ONE_SIDED_NODE_CHARGES.md). Let \(N_J(S)\) count genuine squarefree \(y\)-rough integers \(n\) in \(J\) with exactly the prime subset \(S\) among \(y<p\le z\). Set
\[
 d_y=\zeta(2)^{-1}\prod_{p\le y}p/(p+1),\qquad
 \rho(S)=d_y\prod_{p\in S}(p+1)^{-1}
                 \prod_{y<p\le z,\ p\notin S}p/(p+1).
\]
The comparison is with the finite reference measure \(\rho\). The true integers always obey their multiplication and size constraints. Define
\[
 \mathcal E_K(X)=\sum_J w_J
 \left(\sum_S |N_J(S)-|J|\rho(S)|\right)^2.
\]
Use the full grid in every whole terminal shell. The same exponent holds with only the original coarse nodes, which include the occupied base cells used below.

## Upper bound on all subdivisions

The group-algebra over subsets records their symmetric differences. Writing \(A(n)={\bf1}_{\text{squarefree rough}}(n)\mathbf e_{S(n)}={\bf1}*B(n)\) in Dirichlet convolution gives the exact correction factors \(1-t\) for \(p\le y\), \((1+\mathbf e_{\{p\}}t)(1-t)\) for marked primes, and \(1-t^2\) above \(z\). For any fixed \(\max(1/2,1-1/K)<\sigma<1\),
\[
 \sum_d\|B(d)\|_1 d^{-\sigma}
 \le \zeta(2\sigma)\exp\!\big(2\sum_{p\le\max(y,z)}p^{-\sigma}\big)
 = X^{o(1)}.
\]
Here \(K(1-\sigma)<1\); a sum over all integers suffices for the last bound. At a prefix endpoint \(u\), replacing the exact floors by \(u/d\) costs at most \(2u^\sigma\sum_d\|B(d)\|_1d^{-\sigma}\), including the full tail beyond \(u\). The Euler value is \(\rho\). Subtract at both endpoints. In each shell the sum of weights at one depth is \(2^{s_X}/U\), where \(s_X=O(\sqrt{\log X})\). There are \(O((\log X)^2)\) depth-shell choices in total. Thus \(\mathcal E_K(X)\ll X^{2\sigma-1+o(1)}\). Letting fixed \(\sigma\) decrease to \(1-1/K\) gives the desired upper exponent. At \(z=(\log X)^{2+o(1)}\) use arbitrary fixed \(\sigma>1/2\) instead. [Vector calculation and corrections for actual spent partners](SURVIVOR_HAAR_FINGERPRINTS.md)

## A matching lower bound from impossible products

At each sufficiently large cutoff take the whole dyadic shell \(U=2^{\lfloor\log_2X\rfloor-1}\), so \(X/4<U\le X/2\). Write \(\mathcal B=\{p:z/2<p\le z\}\). Eventually \(z/2>y\). This interval contains \(N\asymp z/\log z\) primes by the prime number theorem. Put
\[
 j=\left\lfloor\frac{\log(2U)}{\log(z/2)}\right\rfloor+1 .
\]
Every product of \(j\) distinct primes in this bin exceeds \(2U\). In contrast, under \(\rho/d_y\) the probability \(p_j\) of precisely \(j\) hits in the bin is
\[
 p_j=\prod_{p\in\mathcal B}\frac p{p+1}
        \sum_{\substack{D\subseteq\mathcal B\\ |D|=j}}\prod_{p\in D}p^{-1}
 \ \ge\ c{N\choose j} z^{-j}
 \ \ge\ c\left(\frac{c'}{j\log z}\right)^j
 = X^{-1/K+o(1)}\quad\text{as a lower bound}.
\]
The first prefactor tends to 1, \(j=o(N)\), and \(j\log(j\log z)=(1/K+o(1))\log X\). These impossible configurations are common to every cell of the shell. Their mass alone forces \(\sum_S |N_J(S)-H\rho(S)|\ge H d_y p_j\). The \(2^{s_X}\) base cells have \(H=U2^{-s_X}\) and weight \(1/U\); all are eventually occupied by the scalar rough count estimate at \(\sigma=1/2+\delta\). Hence
\[
 \mathcal E_K(X)\ \ge\ U\,2^{-s_X}\,d_y^2p_j^2
 \ \ge\ X^{1-2/K-o(1)}.
\]
Since \(d_y\asymp1/\log y\), this matches the upper exponent. For instance, raising the tracked range from the quadratic logarithm to \((\log X)^3\) entails a cost \(X^{1/3+o(1)}\) for this specific statistic.

The discrepancy is detectable even on patterns that occur in a given base cell. If \(\mathcal R_J=\{S:N_J(S)>0\}\), the actual total on \(\mathcal R_J\) is \(N_J\), and the reference assigns at most \(d_y(1-p_j)\) to that set. The unmarked scalar estimate gives \(N_J-Hd_y=O_\delta(U^{1/2+\delta}X^{o(1)})\). Choose \(\delta<1/2-1/K\). The excess of the actual count over the reference on \(\mathcal R_J\) is then at least \((1-o(1))H d_y p_j\). This uses a cell-dependent set, which total variation permits.

## What changes for a signed observation?

For the fixed signed test \((-1)^{|\mathcal B\cap S|}{\bf1}_{|\mathcal B\cap S|\ge j}\) all true observations on the shell are zero. Its reference expected magnitude after signed averaging is \((1-o(1))p_j\) under \(\rho/d_y\). Indeed, the elementary symmetric functions of \(1/p\) in the bin satisfy \(p_{i+1}/p_i\le(\sum_{\mathcal B}1/p)/(i+1)\) whenever \(p_i>0\). All the tail after \(j\) has mass \(o(p_j)\). Including the parity of every other marked prime multiplies this expectation by \(\prod_{y<p\le z/2}(1-2/(p+1))\to(2/K)^2>0\), by Mertens' prime harmonic formula. The test still sees the same power of discrepancy. The parity being tested here is that of the marked primes; the actual Möbius sign includes all remaining factors.

A size-conditioned fingerprint law would change the comparison being measured and would require its own proof. The outstanding OPICA bound is on the complete centered even surplus times the centered odd deficit, aggregated before taking positive parts. Neither this new obstruction nor the Euler-law upper bounds that product. Step 4 and RH remain **OPEN**.

## Conditioning on exactly the fingerprints observed in each cell

The same exponent survives even if the reference discards *every* fingerprint absent from the actual cell and renormalizes on those that occur. This lower bound uses genuine integer observations. On a nonempty \(J\), let \(\mathcal R_J\) be its realized patterns, \(A_J=\sum_S N_J(S)\), and compare \(N_J\) with either of the measures
\[
 |J|d_y\,{\rho|_{\mathcal R_J}\over\rho(\mathcal R_J)}
 \qquad\text{or}\qquad A_J\,{\rho|_{\mathcal R_J}\over\rho(\mathcal R_J)}.
\]
For an empty node set both comparisons to zero. This convention covers all depths. Write \(\Delta_J=\|N_J-|J|\rho\|_1\). Removing the absent reference mass and redistributing it to total \(|J|d_y\) costs exactly \(2|J|\rho(\mathcal R_J^c)\le 2\Delta_J\) in \(\ell^1\). Replacing total \(|J|d_y\) by \(A_J\) costs at most \(\Delta_J\). Consequently each new discrepancy is at most \(4\Delta_J\), giving the same upper exponent as before. At \(z=(\log X)^{2+o(1)}\) the energy with 1 added is still subpower.

Fix \(K>2\) and use the previous \(U\asymp X\). Write \(s=s_X\), \(H=U2^{-s}\), and \(\ell=N^{-1}\sum_{p\in\mathcal B}\log p\) for the mean logarithm in \(\mathcal B=(z/2,z]\). Let \(j'\) be a nearest integer to \((\log U-\tfrac12 s\log2)/\ell\). Choose a \(j'\)-subset uniformly without replacement from the \(N\) actual primes in \(\mathcal B\). Its sum of logarithms has mean \(j'\ell\) and variance at most \(j'(\log 2)^2\) by the finite-population variance formula. Rounding that mean from the desired center costs at most \(\ell/2\). Since \(j'\asymp\log X/\log\log X=o(s^2)\) and \(\ell=O(\log\log X)=o(s)\), Chebyshev gives a \(1-o(1)\) proportion of products \(d\) in the range
\[
       U2^{-2s/3}\le d\le U2^{-s/3}.
\]
Unique factorization and the same binomial estimate as above give
\[
 \sum_{d\ {\rm in\ this\ family}}{1\over d}
 \ \ge\ (1-o(1)){N\choose j'}z^{-j'}
 \ \ge\ X^{-1/K-o(1)}.                                           \tag{1}
\]
These are globally feasible fingerprints. Each \(d\) produces \(\gg (U/d)/\log(2U/d)\) labels \(dq\in[U,2U)\), with \(q>z\) prime, uniformly by the ordinary prime number theorem on dyads, since \(U/d\ge 2^{s/3}\gg z\). All these labels are genuine squarefree \(y\)-rough integers and their fingerprints specify exactly the primes in \(d\). Distinct \(d\) give disjoint labels. By (1), and \(\log(2U/d)=O(s)=X^{o(1)}\), their combined number is at least \(U X^{-1/K-o(1)}\).

Every base cell contains the empty fingerprint for sufficiently large \(X\). Indeed its reference density is
\(\rho(\varnothing)=d_y\prod_{y<p\le z}(1+1/p)^{-1}\asymp_K d_y\).
Apply the upper proof to this one coordinate with any fixed \(1-1/K<\sigma<1\). Its error is \(O(U^\sigma X^{o(1)})=o(Hd_y)\) uniformly on the base cells. Thus \(\rho(\mathcal R_J)\ge\rho(\varnothing)\) there. For fingerprint \(S_d\) belonging to \(d\), the exact odds are \(\rho(S_d)/\rho(\varnothing)=1/d\). Under either conditioned comparison a base cell accordingly predicts at most \(\max(Hd_y,A_J)/d\le H/d\le 2^{-s/3}\) labels of that fingerprint. The integer base width gives \(A_J\le H\). In a cell actually containing \(dq\) the observed count is one, since \(d>H\). Each of the labels counted in (1) therefore contributes at least \(1-2^{-s/3}\) of *positive* discrepancy in its own observed fingerprint. Summing over the bases gives \(\gg UX^{-1/K-o(1)}\). Squaring by Cauchy–Schwarz over \(2^s\) roots with weight \(1/U\) proves \(\ge X^{1-2/K-o(1)}\) for either conditioned energy, even using just these realized coordinates. The assertion is for the sum over the base cells.

The fingerprints used in this last construction have \(j'\gg\log\log U\) marked factors. Each witness \(dq\) exceeds the running-count tolerance of the existing typical-path selector. It would therefore be wrong to transfer this lower bound to that selected population. The obstruction is to retaining the Euler odds after conditioning on actual local support or its total size. It does not exclude a source-dependent law with different weights, or furnish an upper for the original signed parity product.
