# A fixed binary tree for the signed Möbius covariance

**DERIVED on paper.** A single dyadic rational, built from ordinary integer counts at the nodes of a fixed binary tree, has positive-part exponent \(2B-1\) at every sufficiently large integer cutoff, where \(B\) is the supremum of the real parts of the nontrivial zeta zeros. Only pairs in a very narrow common cell with small greatest common divisor enter this signed statistic. A one-sided cofinal subpower upper for it would imply RH. The estimate on that statistic remains open.

## The exact source graph

Take an integer \(X\ge2\), put \(\theta=1/100\), and retain the integers \(q\) satisfying \(q^{100}>X^{99}\) and \(q\le X\). Give each the actual label \(\mu_6(q)=\mu(q)\mathbf1_{(q,6)=1}\). Put \(j_*=\lfloor\log_2 X\rfloor\), \(s=\lceil\sqrt{j_*}\rceil\). In shell \(U=2^j\le q<2U\) use aligned half-open base cells of integer length \(2^d\), \(d=\max(0,j-s)\). Split each cell into two equal children and continue to single integers. A level \(k\in\{0,\ldots,d\}\) inside a base cell has \(2^k\) nodes before clipping. Every node is intersected with the retained terminal integers. A terminal or shell boundary can leave a clipped node or an empty node; the underlying grid is unchanged. The weights are \(w_J=2^{-j-k}\) at level \(k\).

The finite statistic is
\[
 C_{\rm tree}(X)=2\sum_J w_J
 \sum_{\substack{q<r\ \in J\\ \gcd(q,r)^{100}<X}}\mu_6(q)\mu_6(r).
                                                                         \tag{1}
\]
Both indices must belong to the same terminal base cell. At all large \(X\), \(r/q<1+2^{-s}\) there, and \(q/\gcd(q,r),r/\gcd(q,r)>X^{0.98}\). Everything in (1) uses integer cutoffs, bit operations, arithmetic signs, and dyadic rationals. The tree and its weights are determined by \(X\) before the signs are inspected.

The positive comparison statistic is \(A_X=\sum_Jw_J S_J^2\), where \(S_J=\sum_{q\in J}\mu_6(q)\). Define \(b=B-1/2\). Then
\[
 \boxed{\qquad 1+[C_{\rm tree}(X)]_+=X^{2b+o(1)}\qquad}                \tag{2}
\]
along **all** integers tending to infinity. For \(b>0\) the signed covariance itself is eventually positive with this exponent. For \(b=0\) the baseline one is part of (2).

## Why these exact integer charges capture a fixed band

Suppose \(b>0\). Given a fixed arbitrarily small loss \(u>0\), the [fixed-band detector](FIXED_HEIGHT_OBSTRUCTION.md) gives some fixed bounded real interval \(I\) such that
\[
 \int_I\left|\sum_{q\le X}\mu_6(q)q^{-1/2-it}\right|^2dt
 \gg X^{2b-u}
\]
at every sufficiently large \(X\). To see that the order of choices works for unattained \(B\), take an actual zero with \(\delta=\Re\rho-1/2\) sufficiently close to \(b\). Its fixed-width band has a lower amplitude exponent at least \(b-7(b-\delta)/4\), by the modulated-box proof there. For an attained edge use the full exponent result. Constants may depend on that fixed zero and band. Early labels \(q\le X^{1-\theta}\) have \(I\)-norm \(O_{\epsilon,I}(X^{(1-\theta)(b+\epsilon)})\) by the Mertens upper and partial summation. With \(u<2\theta b\) and sufficiently small preliminary \(\epsilon\), the terminal sum retains the lower squared-norm exponent \(2b-u\).

Consider one base cell in shell \(U\). For \(q\in J\) of this cell write the exact weight as \(q^{-1/2-it}=U^{-1/2-it}f_t(q/U)\), \(f_t(v)=v^{-1/2-it}\). On \(1\le v\le2\), \(|f_t|\le1,\ |f_t'|\ll_I1\). For each depth let its piecewise-constant approximation be \(f_t\) evaluated at the left endpoint of the **unclipped** node, divided in its argument by \(U\). At the last level the left endpoint is the integer label itself. Thus telescoping the approximations gives an exact representation of the weighted sum through the base charge and the charges of all of its descendants. At level \(k\ge1\) each coefficient increment costs \(O_I(2^{-s}2^{1-k})\) for \(j\ge s\); a shell with \(j<s\) has depth zero. Cauchy's inequality gives
\[
 \sum_{J\text{ at level }k}|S_J|
 \le 2^{k/2}\left(\sum_{J\text{ at level }k}|S_J|^2\right)^{1/2}.
\]
Taking the triangle inequality first and then Cauchy over at most \(1+\log_2 X\) levels yields for the field \(D_{\rm base}(t)\)
\[
 |D_{\rm base}(t)|^2
 \ll_I(1+\log X)\sum_{J\text{ below or equal to base}}2^{-j-k}S_J^2 .
                                                                         \tag{3}
\]
For clipped nodes the absent labels just contribute zero to \(S_J\). No replacement of native phases by an unpriced constant is used.

There are at most \((1+\log_2 X)2^s=X^{o(1)}\) base cells. Cauchy across bases and integration of (3) on \(I\) give \(A_X\gg X^{2b-u-o(1)}\). Taking \(u\) arbitrarily small proves the lower exponent \(2b\). The numerical **number of all nodes** need not be subpower. The quantity used when summing uniform estimates is their **weighted count**: on each base and level, \(\sum_J 2^{-k}\le1\), and hence its sum over all bases and levels is \(X^{o(1)}\).

## Removing the nonprimitive terms

Uniformly over intervals of endpoints \(T'\le T\), the restricted Mertens sum obeys
\[
 \left|\sum_{\substack{n\in(T',T]\\(n,6l)=1}}\mu(n)\right|
 \ll_\epsilon l^\epsilon T^{B+\epsilon}.                               \tag{4}
\]
Indeed \(M(t)\ll_\epsilon t^{B+\epsilon}\) follows by sharp-cutoff Perron to the right of \(B\) when \(B<1\); absolute counting suffices for \(B=1\). To remove the prime factors of \(6l\), convolve with the indicator of integers supported on those primes and bound the resulting Euler product by \(O_\epsilon(l^\epsilon)\). Each large prime factor costs at most \(p^\epsilon\), since \(B\ge1/2\). Two prefixes give the interval form. [Uniform restricted-sum argument](PRIMITIVE_BAND_COVARIANCE.md) · [Underlying sharp-cutoff bound](../step4-matched-fibres-2026-11-19/FACTORIAL_TERMINAL_MASS_EXPONENT.md)

Using (4) on \(S_J\) gives \(2^{-j}|S_J|^2\ll_\epsilon U^{2b+2\epsilon}\). The weighted node count proves \(A_X\ll_\epsilon X^{2b+\epsilon}\) with preliminary epsilons decreased as needed.

Within a single clipped node let the exact GCD of an ordered pair be \(d_0\). Its contribution to \(S_J^2\) is
\[
 \mu_6(d_0)^2
 \sum_{\substack{e\le2U/d_0\\ (e,6d_0)=1}}\mu(e)
 \left|\sum_{\substack{k:\,d_0ek\in J\\(k,6d_0e)=1}}\mu(k)\right|^2.
                                                                         \tag{5}
\]
To derive (5), put the pair equal to \(d_0u,d_0v\) with \((u,v)=1\), and expand this coprimality indicator over \(e\mid(u,v)\). Squarefreeness requires \((uv,6d_0)=1\); after extracting \(e\), its two Möbius factors square to one wherever the term survives. No independent labels or sign changes are inserted. Formula (5) is for the unnormalized integer charges, hence has no extra \(1/d_0\) or \(1/e\) factor.

Apply (4) at \(T=2U/(d_0e)\) and multiply by \(2^{-j}=1/U\). For any sufficiently small fixed \(\epsilon>0\) the summand has absolute upper
\[
 \ll_\epsilon U^{2b+2\epsilon}(d_0e)^{-1-2b}.
\]
Here the \((d_0e)^{2\epsilon}\) from coprimality is canceled by the same power from the upper endpoint. With \(D=X^\theta\) and \(b>0\), summing \(d_0\ge D,\ e\ge1\), then all nodes with level weight \(2^{-k}\), bounds the **signed** large-GCD contribution by \(O_{\epsilon,b}(X^{2b+\epsilon}D^{-2b})\). The original unsigned pair mass need not satisfy this bound. When \(b=0\), truncate both sums at \(2U\). At most two harmonic factors appear and this entire sector is \(O_\epsilon(X^\epsilon)\) after summing weighted nodes.

Each label belongs to one node per level of its base. Its full diagonal weight is \(\sum_k2^{-j-k}<2/U\). Summing all shell labels therefore costs at most \(2\) per shell, or \(O(\log(2X))\) altogether. Subtract the large-GCD term and any remaining small-GCD diagonal from \(A_X\). The result is exactly (1). For \(b>0\) choose \(u<2\theta b\) with room for the errors and then send \(u\) to zero. This proves (2). For \(b=0\) both \(A_X\) and the absolute value of its signed large-GCD contribution are \(O_\epsilon(X^\epsilon)\); the baseline one completes (2).

## All fine levels are already bounded in absolute value

The last half of the levels in every base can be removed uniformly, even after taking absolute values inside any GCD mask. In a shell of length \(U\), let \(H_0=2^d\) be the base length. Each level-\(k\) node has integer length \(H=H_0/2^k\), and there are at most \(U/H\) such nodes in the shell before clipping. Its ordered pair mass, including the diagonal if desired, is at most \(H^2\), since every label has magnitude at most one. Thus the entire level costs at most
\[
 (U^{-1}2^{-k})(U/H)H^2=H_0/4^k .
\]
The sum over \(2k\ge d\) is at most \(4/3\) per shell, and \(O(\log(2X))\) over the entire terminal graph. All these estimates survive arbitrary deletions of pairs. Define \(C_{\rm coarse}\) by retaining only \(2k<d\) in (1), so each retained physical node has length \(H>\sqrt{H_0}\). Then \(|C_{\rm coarse}-C_{\rm tree}|\ll\log(2X)\). Consequently \(1+[C_{\rm coarse}]_+=X^{2b+o(1)}\) at every cutoff as well, including the case \(b=0\). Only these coarser levels still need a signed estimate.

## Exact finite calculation

The checker factors each coprime-to-six terminal label with FLINT, independently verifies the Möbius value, and includes every active pair through integer counts. For \(D_*=\lfloor(X-1)^{1/100}\rfloor\), define \(c_m=\sum_{d\mid m,\ d\le D_*}\mu(m/d)\). Then \(\sum_{m\mid(q,r)}c_m=\mathbf1_{\gcd(q,r)\le D_*}\) exactly. Processing one integer at a time, the verifier keeps prior signed counts for each of its divisors within the current node. Multiplying by \(c_m\) reconstructs the primitive unordered pair sum without a quadratic pair loop. Every output is stored over an explicit power-of-two denominator. The two smaller runs independently enumerate every unordered pair, evaluate the integer GCD directly, and use XOR to count its shared ancestors. Artificial larger GCD caps exercise divisors above 1 even though \(D_*=1\) at these finite native cutoffs. [Reproducing script](check_dyadic_tree.py) · [Exact integer receipts](DYADIC_TREE_CHECK.json)

| \(X\) | Native signed \(C_{\rm tree}\) | Verification |
|---:|---:|---|
| 2,424 | \(387/32768\) | Independent pairs; selected as a positive-sign fixture |
| 4,103 | \(-1403/131072\) | Independent pairs; crosses a power-of-two shell boundary |
| 1,048,576 | \(-9613629/1073741824\) | Complete divisor-inversion sweep |

At \(X=2^{20}\), the terminal range begins at \(912839\). There are \(20{,}719\) positive and \(20{,}536\) negative labels. The full tree energy is \(1215236689/8589934592\), computed on \(148{,}273\) occupied nodes counting depths. The coarse primitive covariance is \(-75295/8388608\); the fine levels add \(24131/1073741824\) with absolute cost \(31387561/1073741824\). Setting every nonzero label to \(+1\) on the identical full graph gives primitive covariance \(511030426921/1073741824\). This control shows how much the actual signs matter in that finite calculation. The native covariance can have either sign. These finite values do not decide its eventual exponent.

By (2), independently establishing \(C_{\rm tree}(X)\le X^\epsilon\) at arbitrarily large integer \(X\) for each \(\epsilon>0\) would imply RH. All summands and the retained near-equal primitive graph are explicit. No such asymptotic upper, Step 4 theorem, or RH proof has been obtained here.
