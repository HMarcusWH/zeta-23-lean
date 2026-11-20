# The deficit product can change by almost a full power on one genuine cofactor

**DERIVED on paper.** Removing one explicitly described largest-prime cofactor from the genuine survivor graph leaves its unsigned discrepancy unchanged after the measured deletion correction, preserves its same-cofactor counting law and preserves its all-depth relative signed cancellation. Nevertheless this single deletion creates positive opposed-parity energy of size $X^{1-o(1)}$. The earlier per-cofactor primitive GCD bound costs $o(1)$ on all its incident edges. The new conclusion measures the signed mixed compensation with the complete complement of this fibre and identifies a subgraph on which the claimed inference fails. The signed upper on the complete graph remains open.

Work at the earlier all-rough matching on $X=2^{100t}$ and the whole terminal shell $[U,2U)$ with $U=X/2$. Write $L=\log U$, $F=L^{3/5}(\log L)^{-1/5}$, $D=X^{.01}$, $H_0=U2^{-s_X}$ and $w_J=H/(UH_0)$ at native node width $H$. Each squarefree $y$-rough label has $y=\lceil\log_2 X\rceil^2$ and its true factorization $n=mp$, $p=P^+(n)$. All matched target and donor cofactors of this particular selector are at most $2^{s_X/2}$. Let $R$ be the actual post-matching graph and $r_J$ its signed charge. On every native node $H\ge H_3\asymp U^{.58}$ all original matches cancel in the node. Rough Mertens at the two endpoints then gives $|r_J|\ll U\exp(-c_0F)$ for some fixed $c_0>0$. [Input matching and cofactor ranges](../step4-prime-transport-2026-11-19/PRIME_SPLIT.md) · [Rough Mertens and same-cofactor theorem](SURVIVOR_COFACTOR_PAIRS.md)

Fix $0<\theta<c_0/8$ before increasing $X$. Set $P=\exp(\theta F/2)$ and choose one prime $q_1\in(P,2P)$ and a different prime $q_2\in(2P,4P)$. Bertrand's theorem, or the ordinary PNT, gives both at all sufficiently late cutoffs. Put $m=q_1q_2$. Then $\log m=\theta F+O(1)$, $2^{s_X/2}<m<D$, and both factors exceed $y$. All genuine labels
$$
 \mathcal B_m=\{mp\in[U,2U):p\ \text{prime}\}
$$
have $p>q_2$, have Möbius sign $-1$, and belong to $R$. Their count $g_J$ in any $J$ with $H\ge H_*=U\exp(-2\theta F)$ satisfies uniformly
$$
 g_J=(1+o(1))\,\frac{H}{m\log U}.
 \tag{1}
$$
The interval $J/m$ has start comparable with $U/m$ and length $(U/m)^{1-o(1)}$, safely above the uniform prime-number-theorem threshold. Also $\log(U/m)=(1+o(1))\log U$. Longer intervals can be partitioned into permitted lengths. Only prime counts on these explicit intervals are used. [Guth–Maynard, Corollary 1.3](https://arxiv.org/abs/2405.20552)

## The full contrast on actual labels

Write $R'=R\setminus\mathcal B_m$, keeping exactly the original signs. Its charge is $r'_J=r_J+g_J$ at every node. For $H\ge H_*$, (1) is $\ge U\exp(-(3\theta+o(1))F)$, so uniformly $r'_J=g_J(1+O(\exp(-cF)))>0$. The constant $c>0$ may shrink from line to line. At the base cells alone,
$$
  \sum_{|J|=H_0} w_J[r'_J]_+^2
  =(1+o(1))\frac{H_0}{m^2\log^2 U}
  = U\exp(-(2\theta+o(1))F).
  \tag{2}
$$
The corresponding original positive energy on the bases is at most $O(U^2\exp(-2c_0F)/H_0)$. Their ratio tends to zero. This is an actual change on the same source, prior to any claim about acceptable deletions.

In the corrected center $c_J=(H d_y-T_J)/2$, $T_J$ counts every originally matched label in $J$. For $R'$ it becomes $c'_J=c_J-g_J/2$. Removing these negative labels changes the deviations of even and odd populations from $(e_J,o_J)$ to $(e_J+g_J/2,o_J-g_J/2)$. Thus their sum is *exactly* the same. Their difference gains $g_J$. The pointwise deficit-product lemma and the critical unsigned bound now imply
$$
 4\sum_{|J|=H_0} w_J[e'_J]_+[-o'_J]_+
 =(1+o(1))\frac{H_0}{m^2\log^2 U}.
 \tag{3}
$$
The additive $O_\varepsilon(X^\varepsilon)$ error is negligible, for instance with $\varepsilon=1/3$. The same unsigned discrepancy is retained on each small-prime fingerprint if its measured deletion counts are updated there. The compensated contingency-table identities are finite equalities on the resulting table; the cone marker on this old survivor graph is constant. None of these equalities controls the additional signed component in (3). [Unsigned arithmetic and exact deficit product](SURVIVOR_HAAR_FINGERPRINTS.md) · [Finite determinant identities](../../CONE_CONTINGENCY.md)

## Cross terms and the critical GCD cost

All ordered distinct pairs internal to $\mathcal B_m$ have sign $+1$ and GCD exactly $m<D$. Their signed count in $J$ is $g_J(g_J-1)$. Their ordered signed mixed count with the entire complement $R'$ is exactly $-2g_Jr'_J$ before masking. Apply the existing [fixed-cofactor mask bound](../step4-prime-transport-2026-11-19/FIXED_COFACTOR_MASK.md). For a fixed $n=mp$ in this fibre and $r\ne n$, $\gcd(mp,r)\ge D$ forces $p\mid r$ because $\gcd(mp,r)$ otherwise divides $m<D$. In any $H$-node there are at most $2H/p\le 2Hm/U$ other multiples of $p$. Counting both orientations and all possible partners gives an absolute upper. At any depth, $\sum_{|J|=H}g_J\ll U/(m\log U)$ by PNT on the whole shell. Its one-cofactor specialization yields
$$
 \sum_J w_J\#\{\text{rejected ordered pairs touching }\mathcal B_m
                                  \text{ in }J\}
 \ \ll\sum_H \frac{H}{UH_0}\frac{Hm}{U}\frac{U}{m\log U}
 \ \ll\frac{H_0}{U\log U}.
 \tag{4}
$$
In particular the native primitive graph retains the measured compensation. For the coarse nodes $H\ge H_*$ the unmasked mixed count equals $-2g_J^2(1+O(\exp(-cF)))$. For finer nodes its absolute value and $g_J^2$ are bounded by $O(H^2)$; their total weighted cost is $O(H_*^2/H_0)$. Divide by the base lower in (2) to bound this fine fraction by $\exp(-(2\theta+o(1))F)$. Equation (4) pays the mask on every level. Therefore, for $C_{\rm mixed,D}(J)$ the *complete* signed mixed ordered incidence and the sum over the whole shell tree,
$$
 \sum_J w_J |C_{\rm mixed,D}(J)+2g_J^2|
 \ll e^{-cF}\sum_J w_J g_J^2 .
 \tag{5}
$$
This independently determines a substantial genuine signed sector at all depths, with a critical absolute bound on the discrepancy between the two GCD conventions. It also shows how much a proof would lose by omitting its complement.

## Why the earlier relative estimate survives

Deleting $\mathcal B_m$ leaves the protected cofactor dyad $[2Z,4Z)$ intact, where $Z=\lfloor2^{s_X/200}\rfloor$. For the new graph the same-cofactor upper decreases and the previous lower still holds at every admitted interval length. In particular the weighted primitive same-cofactor sum $S'_D$ still has order $H_0V(y)/(Z\log^2 U)$. All $H\ge U\exp(-aF)$, with fixed $a<\theta/8$, satisfy $|r'_J|\ll U\exp(-\theta F/2)$ at native coarse nodes: bound $g_J\le 1+U/m$ and use the untouched original-bound estimate for $r_J$. Repeat the ordered-pair decomposition and GCD rejection bound from the earlier paper at those nodes. On finer nodes bound the total signed pair sum by $H^2$ and divide its geometric sum by the unchanged base denominator. This proves, for some $c'>0$,
$$
 \sum_J w_J |C'_{\ne,D}(J)+S'_D(J)|
   \ll e^{-c'F}\sum_J w_J S'_D(J).
 \tag{6}
$$
All three quantities are computed on the *same modified true subgraph*. The assertion tests the strength of the earlier relative estimate with an unspecified positive constant, exactly as previously obtained. It does not identify this new $R'$ with the permissible matched source for Step 4. Equations (2)–(3) show explicitly that deleting the fibre would violate the critical one-polarity transfer already on the subcollection of base cells. The true arithmetic coupling between this fibre and the rest is quantified by (5). The missing task is to control the residual after such compensations on the unchanged full source to absolute $X^\varepsilon$, rather than relative $\exp(-cF)$ at a baseline of size $X^{1-o(1)}$. Step 4 and RH remain **OPEN**.
