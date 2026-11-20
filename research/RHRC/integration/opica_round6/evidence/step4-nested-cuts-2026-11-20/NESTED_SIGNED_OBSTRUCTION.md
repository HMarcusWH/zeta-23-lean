# A hypothetical off-line zero forces a nested sequence of actual parity deficits

**DERIVED on paper, conditional on the existing OPICA paper detector and interval estimates.** The finite tree argument below is elementary. Its application to zeta inherits the analytic assumptions and verification status of those earlier arguments. PR 303 at `a6a001fd570cd7cf9b97fdad59e373760a3153ec` is the source. Step 4 and RH remain open.

## The arithmetic observable

Let \(B=\sup_{\rho}\Re\rho\) over the nontrivial zeros and \(b=B-1/2\). Fix one sign \(s\in\{-1,1\}\) and constants \(0<a<c<1/4\). Use exactly the complete terminal shells for the native rough Möbius field, with integer cutoff \(X\), \(X^{.99}<n\le X\), \(y=\lceil\log_2 X\rceil^2\), and squarefree integers free of primes through \(y\). A power-of-two endpoint has zero rough weight at the cutoffs under discussion. On the shell \([U,2U)\), put \(j=\log_2 U\), \(s_X=\lceil\sqrt{\lfloor\log_2X\rfloor}\rceil\), \(H_0=U2^{-s_X}\), and use the native dyadic cells at widths \(H_0 2^{-k}\) with weights \(w_J=2^{-k}/U\). Only sufficiently large cutoffs enter the estimates.

Let \(f_J\) be the signed sum over **all** genuine labels in the cell. Let \(r_J\) be its surviving charge after one actual three-stage selection, counting removal of every target and its spent opposite-sign partner. Denote the raw unsigned total by \(N_J\), removed count by \(T_J\), surviving even/odd counts by \(P_J,M_J\), and \(d_y=\zeta(2)^{-1}\prod_{p\le y}p/(p+1)\). Subtract \((|J|d_y-T_J)/2\) from both survivor counts to obtain \(p_J,m_J\). Let \(Q_J^+=4[p_J]_+[-m_J]_+\), with the populations reversed for \(Q_J^-\). From the definitions, at every cell, including those with unequal removed populations,
\[
 Q_J^s=\big[[s r_J]_+^2-D_J^2\big]_+,\qquad D_J=N_J-|J|d_y .
\tag{1}
\]
Indeed \(2p_J=D_J+r_J\), \(2m_J=D_J-r_J\). If \(sr_J>|D_J|\), both factors have the required sign and the product is the difference of squares. Otherwise both sides vanish. This refines the finite two-sided error estimate already checked in Lean. [Registered finite inequality](../../../../../../Zeta23/OPICARound6/PrimeFactorPaths/ParityDeficitProduct.lean) · [Actual matching and its largest cell](../step4-one-sided-sieve-2026-11-19/PRIME_FACTOR_PATHS.md)

For each surviving label of sign \(s\), look at its actual ancestors \(J_k(n)\) between \(L_U=\lfloor aj\rfloor\) and \(K_U=\lfloor cj\rfloor\). Define one scalar for the **complete collection** of whole terminal shells,
\[
 Z_s(a,c;X)=\max_{U,n}\ \min_{L_U\le k\le K_U} Q^s_{J_k(n)}/U .
\tag{2}
\]
Take a zero maximum for an empty selection. Every count in (2) includes the full signed population of its cell. At these levels the widths exceed \(U^{.58}\) eventually. Each previously removed opposite-sign pair lies in a common stage-three cell and hence wholly in or out of each tested cell. Thus \(r_J=f_J\), and the two centered populations are **exactly equal to their raw counterparts**: deleting one integer of each sign subtracts one from the common center as well. This allows computation of the node costs from the raw arithmetic. All raw row paths may be used in (2) instead of just positive survivors of the selected polarity: any strictly positive minimum ends in a cell of strictly positive signed survivor count in that polarity; a surviving representative from that cell gives the same path. This does not give a raw-to-survivor identity per fingerprint.

## Why an entire path is forced

On the raw source the inherited one-sided lower gives \(1+\sum_Jw_J[s f_J]_+^2=X^{2b+o(1)}\) on all sufficiently late horizons for either polarity. All coarse cells of all whole terminal shells enter here. The existing maximal-interval estimate gives, at a single full dyadic level,
\[
 \sum_{|J|=H_0 2^{-k}} |f_J|^2\ll_\eta U^{2B+\eta} X^{o_\eta(1)}.
\tag{3}
\]
For precision about the growing roughness mask, convolve the ordinary Möbius function with the indicator of integers all of whose prime factors are at most \(y\). At each prime the Dirichlet factors give exactly the rough Möbius function. Apply Minkowski in the finite vector of disjoint cells. For each smooth divisor \(d\le2U\), apply the ordinary estimate on the intervals scaled by \(d\); if their widths are below one, counting at most once per integer bounds the squared sum by \(O(U/d+1)\). The unmasked estimate can equally start from the repository's \((n,6)=1\) variant, in which case the smooth convolution adds only primes strictly between 3 and \(y\). The norms sum at cost \(\prod_{p\le y}(1-p^{-B-\eta/2})^{-1}=X^{o_\eta(1)}\): for fixed \(\eta>0\) the logarithm is bounded by a constant times \(1+\sum_{n\le y}n^{-1/2-\eta/2}=o(\log X)\). The bounded scaled-shell endpoint range is covered by counting. At \(B=1\) the raw count suffices. [Interval estimate and hypotheses](../step4-prime-transport-2026-11-19/TREE_INTERVALS.md) · [One-sided lower on whole shells](../step4-prime-transport-2026-11-19/ONE_SIDED_NODE_CHARGES.md)

Suppose \(b>0\). By (3), summing \(2^{-k}\) for \(k\ge L_U\) costs at most \(X^{2b-.99a+o(1)}\) over all whole shells, where the usual arbitrarily small fixed exponent losses are absorbed in the notation. The earlier levels therefore retain \(X^{2b-o(1)}\) energy. At each level \(\sum_Jw_J U=2^{s_X}\); the number of levels and shells is polylogarithmic. At **every** sufficiently late cutoff there is an actual cell \(I\) of depth \(k_0<L_U\) with
\[
 s f_I/\sqrt U\ \ge X^{b-o(1)} .
\tag{4}
\]
Take a child with larger signed charge in polarity \(s\) at each split. The children partition the actual labels. On this one path, **simultaneously**,
\[
 s f_{J_k}/\sqrt U\ \ge 2^{k_0-k} X^{b-o(1)}
       \quad(k_0\le k\le K_U).
\tag{5}
\]
Here \(r=f\) on the path by the common-cell matching identity. The established scalar unsigned bound gives \(|D_J|\ll_\eta U^{1/2+\eta}X^{o_\eta(1)}\) uniformly in every such cell. If \(c<b\), choose \(\eta\) and the losses in (4) below the fixed gap. Equation (1) then implies \(Q^s_J=(s f_J)^2(1-o(1))\) uniformly on the chosen path. The last cell has a genuine surviving representative of sign \(s\). On the other hand (3) gives \(Q^s_J/U\le X^{2b+o(1)}\) on all tested cells. At every horizon taken sufficiently late for the chosen constants,
\[
 (2b-2c)_+\ \le\ \liminf_{X\to\infty}\frac{\log(1+Z_s(a,c;X))}{\log X}
 \ \le\ \limsup_{X\to\infty}\frac{\log(1+Z_s(a,c;X))}{\log X}
 \ \le\ 2b .
\tag{6}
\]
The first inequality at \(b\le c\) is simply nonnegativity. No quantitative lower for an opposed product is asserted when the signed charge is comparable to the unsigned error. The scalar discrepancy bound and all growing-horizon implications in (3)–(6) retain their paper status. [Unsigned discrepancy on genuine arithmetic](../step4-parity-deficit-2026-11-20/SURVIVOR_HAAR_FINGERPRINTS.md)

## The new arithmetic test

Fix one polarity and consider, for example, \(a=c/2\) for a sequence of positive fixed \(c\) tending to zero. At each chosen cutoff, each path is allowed to stop at **its own level** in the specified window. If for a sequence \(c_i\downarrow0\), \(\lambda_i\downarrow0\), one proves independently that at arbitrarily late cutoffs every such path has a cell with \(Q^s_J\le C_i U X^{\lambda_i}\), then (6) gives \(b\le c_i+\lambda_i/2\) for every \(i\), and hence \(b=0\). Choose the parameters and constants before the lower horizon; the cutoff may depend on them. The blocking cell may depend on the path. For any single prescribed \(c,\lambda\) the same argument gives the quantitative zero ceiling \(B\le1/2+c+\lambda/2\). Under RH, (3) gives the cofinal test for every fixed window and every positive loss. These statements concern the actual zeta function through the inherited paper implications.

There is an exact finite way to search this condition. Among all complete dyadic cuts with allowed stopping levels, minimize the maximum node cost \(Q^s_J/U\). The value equals (2). If every path hits a low-cost cell, stop at its first such cell; the chosen nodes form a disjoint cover. Conversely a cover meets every path. A strictly high path ends in a cell containing a true representative, so allowing paths into empty cells does not increase the nonnegative maximum. The recursion at an eligible nonterminal node is the minimum of its cost and the maximum of its two child values. Both children are required. Using different polarities for different paths can destroy the criterion.

## What the small-prime constraint adds to the witness

Use the paper's enhanced matched source with fingerprints \(F=D_z(n)\le M=U^{o(1)}\) for any prescribed uniform subpower range; freeze the marked set within the chosen shell. Inside the terminal cells at depth \(K_U\), match surviving positives to surviving negatives until only their signed excess remains. Merge upward by pairing opposite remaining signs from the two children. These auxiliary cancellations represent the exact finite sum. They never change the source used to evaluate \(Q\). In the early cell (4) exactly \(s f_I\) actual representatives of the chosen sign remain. In every descendant, the number of these inherited representatives is at most its original survivor excess of that sign, because later matching can only delete representatives. At least \(s f_I/M\) of the representatives in \(I\) have one **identical** fingerprint. Follow the child with more of these rows. Their number at depth \(k\) is at least \(2^{k_0-k}s f_I/M\). This proves (5) with a subpower loss while exhibiting the same small-prime product and the same remaining cofactor parity among the counted labels at every level. In particular a purely combinatorial dispersion into subpower-many small-prime patterns cannot prevent this witness.

The representatives are signed witnesses for the full cell calculation. They do not prove an excess *inside the same fingerprint* after the other fingerprints are discarded. For example, let the first child have two positive A labels and three negative B labels, and the other child two positive B labels. The parent has positive total charge and negative net B charge. A B label can nevertheless be a positive surviving representative of the parent after the full matching. [Genuine fingerprint bound and required full complement](../step4-parity-deficit-2026-11-20/MOMENT_CORRECTED_SURVIVOR_FINGERPRINTS.md)

## An allowed comparison and a sharp failed comparison

The original tree and finite generator use the floor inside the square root defining \(s_X\). One subsequent paper uses a ceiling there. They differ by one when \(\lfloor\log_2X\rfloor\) is a square and \(X\) is strictly between powers of two. Keep the ceiling for the *roughness* \(y\). To evaluate the effect of the depth change take the same signed field, set \(d=j-s_X\ge2\), and let \(E_k\) be the native weighted positive-part energy at that depth. The finer base's level \(k\) is exactly the native level \(k+1\), with twice its weight. The coarse test in the generator is the strict inequality \(2k<d\). Thus with coarse totals \(V,V'\) on the native and one-step-finer bases,
\[
 V'=2\{V-E_0+\mathbf1_{2\mid d}E_{d/2}\},\qquad
 V\le(5/2)V',\qquad V'\le2V+2 .
\]
For the first upper, the two child charges give \(E_0\le4E_1=2E'_0\), and the other native coarse terms cost at most \(V'/2\). For the other upper, integer capacity \(|f_J|\le |J|\) at width \(2^{d/2}\), summed with the native weights over the shell, gives \(E_{d/2}\le1\). This covers any common selected population with signs in \(\{-1,0,1\}\), including clipping of the terminal range with its underlying grid held fixed. Equivalence of totals at the required exponent does not identify cells at the same numerical depth. The finite replay distinguishes the conventions at \(X=65{,}537\), where they give 4 and 5.

There is also a sharp arithmetic falsification of the proposed path test if a complement is dropped. On the separate aligned selector at \(X=2^{100t}\), the earlier one-cofactor diagnostic deletes one genuine negative fibre on the shell \(U=X/2\). The resulting charge in every original base cell is \(U^{1-o(1)}\). Keep the raw unsigned discrepancy with the updated exact removed count. Greedy descent forces a path with positive charge at least \(U^{1-c-o(1)}\) down to \(K_U\), and equation (1) gives \(Z'_+(a,c;X)\ge U^{1-2c-o(1)}\) on that shell. Conversely at the last allowed level, the intrinsic bound by the width squared divided by \(U\) gives \(Z'_+\le U^{1-2c+o(1)}\). The invalidly altered graph attains the *entire* possible exponent for this diagnostic. The missing fibre and its mixed term in the genuine field are explicit in the cited calculation. The stopping test cannot be justified using only assumptions that survive this deletion. [Arithmetic counterexample on its own selector](../step4-parity-deficit-2026-11-20/SINGLE_COFACTOR_PARITY_DEFICIT.md)

**OPEN.** No independent proof that each path encounters such a cell has been obtained. The criterion localizes what an off-line zero must force on the actual coupled source. Its formal transfer and the required arithmetic upper remain obligations. The finite replay tests 13,122 signed eight-leaf cases and uses the exact PR generator on the documented base at \(X=1{,}656{,}575\). On its auxiliary selected rows the hereditary witness counts are 1,679, 991, 507, 259, 130 and 67, all with empty marked fingerprint. Their final cell contains the genuine prime 1,463,447. The experiment is on a full base **inside a clipped shell**. It is independent of the asymptotic whole-shell requirement. [Exact finite receipt](STOPPING_CHECK.json) · [Replay](check_stopping.py)
