# What the true parity counts can do together in the rough-source tree

**DERIVED on paper, 20 November 2026.** The squares of all simultaneous same-direction fluctuations of the two surviving parity populations have total cost \(O_\epsilon(X^\epsilon)\), with the actual tree weights. This includes sibling differences and holds after resolving every small-prime fingerprint simultaneously. Opposite fluctuations remain capable of carrying the signed Step 4 signal. A genuine large-prime sector gives a counterexample to extending the fingerprint model indiscriminately.

The research checkout inspected was commit \(\mathtt{adc9c6ce04f73dc276513b81ae4a316a0a8367eb}\), tree \(\mathtt{8ed7eaba2f04c213e4c1d633d99673fd19ffe220}\). The inputs are the [whole-shell detector](../step4-prime-transport-2026-11-19/ONE_SIDED_NODE_CHARGES.md) and its [exact surviving labels and signed deletion cost](../step4-one-sided-sieve-2026-11-19/PRIME_FACTOR_PATHS.md).

## An unsigned arithmetic estimate at the critical scale

Freeze \(y=\lceil\log_2 X\rceil^2\), \(s=\lceil\sqrt{\lceil\log_2 X\rceil}\rceil\). In every complete dyadic shell \([U,2U)\subset (X^{.99},X]\), use the original base width \(H_0=U2^{-s}\), dyadic widths \(H=H_0 2^{-k}\) down to one site, and \(w_J=2^{-k}/U\). A zero-weight endpoint convention at powers of two has no arithmetic effect. All interval lengths below are ordinary lengths, with one consistent half-open convention.

Let \(a(n)=\mu(n)^2{\bf1}_{P^-(n)>y}\), with \(a(1)=1\). Its exact density at frozen \(y\) is
\[
 d_y=\prod_{p\le y}(1-p^{-1})\prod_{p>y}(1-p^{-2})
     ={1\over\zeta(2)}\prod_{p\le y}{p\over p+1}.
\]
For a set \(\mathcal P\) of marked primes in \(y<p\le z\), the actual fingerprint \(F(n)\) records *which* marked primes divide \(n\). Allow \(z=(\log X)^{2+o(1)}\) and any subset of the primes in this range. Define a measure on subsets by
\[
 \rho(F)=d_y
 \prod_{p\in F}{1\over p+1}
 \prod_{p\in\mathcal P\setminus F}{p\over p+1}.
\]
This is an approximation to an unselected squarefree counting measure at finite \(X\); no independence assumption is made on the observed integers. Write \(N_J(F)=\#\{n\in J:a(n)=1,\ F(n)=F\}\). For every fixed \(0<\delta<1/2\), uniformly for every subinterval \(J\) of every complete shell,
\[
 \sum_F|N_J(F)-|J|\rho(F)|
 \ll_\delta U^{1/2+\delta} X^{o_\delta(1)}.                       \tag{1}
\]
In particular there is no factor counting fingerprints, even when a different set of allowed fingerprints is chosen on each cell.

To prove this, take the finite group of subsets with symmetric difference. Write \(\mathbf e_F\) for its point masses. In its real group algebra the \(\ell^1\) norm is submultiplicative. The multiplicative coefficient \(A(n)=a(n)\mathbf e_{F(n)}\) factors as \(A={\bf1}*B\) in Dirichlet convolution, with \({\bf1}(n)=\mathbf e_\varnothing\). If \(t=p^{-s'}\) is a formal Euler variable, the local factors of \(B\), writing \(1=\mathbf e_\varnothing\), are
\[
 1-t\quad(p\le y),\qquad
 (1+\mathbf e_{\{p\}} t)(1-t)\quad(p\in\mathcal P),\qquad
 1-t^2\quad(p>y,\ p\notin\mathcal P).
\]
For \(\sigma=1/2+\delta\), the sum of the norms of the marked factor's coefficients weighted by powers of \(p^{-\sigma}\) is \((1+p^{-\sigma})^2\). Thus
\[
 \sum_{d\ge1}{\|B(d)\|_1\over d^\sigma}
 \le \zeta(2\sigma)\exp\!\left(2\sum_{p\le \max(y,z)}p^{-\sigma}\right)
 =X^{o_\delta(1)}.
\]
The last assertion follows even on majorizing the prime sum by the sum over integers, since \(\max(y,z)^{1-\sigma}=(\log X)^{1-2\delta+o(1)}\). Absolute convergence at one gives \(\sum B(d)/d=\rho\); dividing the marked local factor at one by \(1-p^{-2}\) gives the two probabilities displayed above. Now
\[
 \left\|\sum_{n\le t}A(n)-t\rho\right\|_1
 \le \sum_{d\le t}\|B(d)\|_1+t\sum_{d>t}{\|B(d)\|_1\over d}
 \le 2t^\sigma\sum_{d\ge1}{\|B(d)\|_1\over d^\sigma}.
\]
Apply this at the two endpoints. Half-open integer intervals only shift the endpoint convention by a bounded amount. This proves (1).

Put \(D_J=N_J-H\rho\) as a vector. There are \(2^{s+k}\) cells at depth \(k\); their total original weight is \(2^s/U\). Summing (1) squared over \(O(\log X)\) depths and shells, with \(\delta\) chosen before \(X\), proves for every \(\epsilon>0\)
\[
 \sum_J w_J\|D_J\|_1^2+
 \sum_{J\ {\rm internal}}w_J\|D_{J_L}-D_{J_R}\|_1^2
 \ll_\epsilon X^\epsilon.                                        \tag{2}
\]
The argument covers the full regular dyadic grid. Restricting the sums to occupied nodes or to original coarse nodes preserves the bound. At a retained internal node the counts in its two geometric children are evaluated even if one child is empty.

## Which fluctuations have now been paid?

Use the actual original selection on a whole shell. For each fingerprint, let \(T_J\) count **all** removed labels in \(J\), including every spent partner. Let \(P_J,M_J\) count the remaining positive and negative Möbius labels respectively. These are vectors of integer counts. Define \(c_J=(H\rho-T_J)/2\), \(p_J=P_J-c_J,\ m_J=M_J-c_J\). Exactly,
\[
 p_J+m_J=D_J,\qquad p_J-m_J=P_J-M_J .
\]
Consequently, on the node/fingerprint pairs on which both fluctuations have the same weak sign,
\[
 \sum_J w_J \sum_{\{F:p_J(F)m_J(F)\ge0\}}
       \{p_J(F)^2+m_J(F)^2+[p_J(F)-m_J(F)]^2\}
 \le 2\sum_J w_J\|D_J\|_1^2\ll_\epsilon X^\epsilon.                \tag{3}
\]
The same assertion holds with \(F\) summed out *before* the sign test, or with any chosen subset of fingerprints summed before it, independently for each node. Pointwise the two terms \(p^2+m^2\) and \((p-m)^2\) are each bounded by \((p+m)^2\) on this event. On all node/fingerprint pairs, including the opposite-sign ones, \((|p|-|m|)^2\le (p+m)^2\). Thus unequal magnitudes beyond this same budget are excluded as well.

For sibling differences apply the same argument to \(p_{J_L}-p_{J_R}\) and \(m_{J_L}-m_{J_R}\). The deterministic \(H\rho/2\) offsets cancel because the two children have equal widths. Each true parity contrast has the correction \(+(T_{J_L}-T_{J_R})/2\). Their sum is the true unsigned contrast \(N_{J_L}-N_{J_R}\), whose complete weighted cost is paid in (2). This keeps both children, including opposite signs and both ends of each past match. It is an unconditional restriction on the observed survivor arithmetic. A Haar increment of the raw survivor charge has the difference of these two contrasts. The criterion still uses the original tree, including its root charges. No identity has turned a signed detector into an unsigned tree reconstruction.

One directly usable consequence with no fingerprint condition is
\[
 \left|\left(\sum_J w_J[P_J-M_J]_+^2\right)^{1/2}
      -2\left(\sum_J w_J[P_J-c_J]_+^2\right)^{1/2}\right|
 \le \left(\sum_J w_J D_J^2\right)^{1/2}.
\]
Here counts and centers are scalars after summing fingerprints. The allowance follows from \(P_J-M_J=2(P_J-c_J)-D_J\) and the Lipschitz bound for the positive part. The yet-unproved upper concerns one actual parity population exceeding this known center. The possible large contribution is an upward fluctuation of one parity paired with a downward fluctuation of the other, almost equal in magnitude in the sense of (2). Equation (2) alone permits that behavior.

There is a sharper product formula. For all real \(p,m\),
\[
 0\le [p-m]_+^2-4[p]_+[-m]_+\le (p+m)^2 .                         \tag{4}
\]
For \(p\ge0\ge m\) the difference is exactly \((p+m)^2\). For \(p\le0\le m\) it is zero. When \(p,m\) have the same sign the product is zero and \(|p-m|\le |p+m|\). Swapping \(p,m\) gives the opposite polarity. Thus (2) also pays the sum of absolute errors incurred when replacing the signed one-node energy by the true opposed-deficit product \(4[p_J]_+[-m_J]_+\). This holds directly on each individual fingerprint and for summed fingerprints. For transfer between raw and survivor fields use the full fingerprint-summed populations: the raw counts have center \(H d_y/2\), and the survivors have center \((H d_y-T_J)/2\). The triangle inequality, (4) twice, and the pre-existing \(O(1)\) absolute signed-square change per whole shell give
\[
 \sum_J w_J
 \left|4[p^{\rm raw}_J]_+[-m^{\rm raw}_J]_+
           -4[p^{\rm surv}_J]_+[-m^{\rm surv}_J]_+\right|
 \ll_\epsilon X^\epsilon.
\]
The inherited matching estimate for the complete signed count does not automatically grant the same raw-to-survivor transfer fingerprint by fingerprint, since a target and its spent partner can have different fingerprints. Neither side of this comparison has an independent subpower upper at present.

## A concrete obstruction for extending the Euler law to large factors

In each original base cell \(J\) of a complete shell let \(\mathcal B=(U^{3/5},U^{7/10}]\) mark actual primes. At most one marked prime divides \(n<2U\) for sufficiently large \(U\). Before the selector, let \(N_1(J)\) count rough squarefree labels containing one. For \(p\in\mathcal B\) and \(n=pm\) in the shell one has \(m<p\). Consequently
\[
 N_1(J)=\sum_{p\in\mathcal B}\ \sum_{m\in J/p}a(m)
       =d_y H\sum_{p\in\mathcal B}{1\over p}
          +O_\delta\big(U^{.85+.3\delta}X^{o_\delta(1)}\big).
\]
The vector-convolution proof works unchanged at cofactor endpoints \(t\le 2U/p\) using the same fixed \(y\), here with \(\mathcal P=\varnothing\). Summing \((U/p)^{1/2+\delta}\) over all integers \(p\le U^{.7}\) gives the stated exponent. The estimate also holds on arbitrary subintervals; the relative asymptotics below use \(H=H_0=U^{1-o(1)}\). The prime harmonic sum tends to \(\lambda=\log(7/6)>0\) by Mertens' theorem. Since \(d_y\asymp1/\log y\), the genuine mean of the one-bit sector \((-1)^{\#\{p\in\mathcal B:p\mid n\}}\) under the rough-squarefree counts tends to \(1-2\lambda\) uniformly in every base cell. The Euler-product prediction would tend to \(\exp(-2\lambda)\), strictly larger. Equivalently the Euler model gives positive limiting probability to at least two marked primes, an impossible integer event in this shell.

The erroneous center would give a squared error \(\gg U2^{-s}d_y^2\) from the base cells of one such shell. For a complete shell with \(U\asymp X\) this is \(X^{1-o(1)}\). This is an actual obstruction, even at the level of one marginal before selection. The small-prime result (1) uses cutoffs for which \(\sum_{y<p\le z}1/p=o(1)\); it cannot account for parity among all larger factors. After the actual selection, (2)–(3) apply with the measured removal counts. The large-prime asymptotic above is for the unselected input.

An auxiliary finite integer check with \(y=5,\ z=23\) inverted \(A={\bf1}*B\) by subset counts, then reconstructed all prefix fingerprints simultaneously. At \(8,64,512,2048\) it recovered respectively \(2,16,131,519\) squarefree rough integers in \(2,7,22,28\) nonempty fingerprints. These are finite algebra checks with auxiliary parameters. The new estimates and their limitations above are paper deductions. The critical bound on the signed survivor excess, Step 4, and RH remain **OPEN**.
