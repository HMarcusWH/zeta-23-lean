# Either sign of the actual Möbius cell excess detects the obstruction

**DERIVED on paper.** For each node \(J\) of the original rough tree let \(f_J\) be its signed count of terminal squarefree \(y\)-rough integers. Each such integer contributes \(+1\) if it has an even number of prime factors and \(-1\) if it has an odd number. Define two nonnegative calculations on the full or coarse-only tree:
\[
 V_+(X)=\sum_Jw_J\max(f_J,0)^2,\qquad
 V_-(X)=\sum_Jw_J\max(-f_J,0)^2 .
\]
For each sign independently, at every sufficiently late integer cutoff,
\[
 \boxed{\qquad 1+V_\pm(X)=X^{\,2b+o(1)},\qquad
 b=\sup_\rho\Re\rho-\tfrac12 .\qquad}
 \tag{1}
\]
Thus a cofinal upper \(V_+(X)\ll_\epsilon X^\epsilon\) for every \(\epsilon>0\) would suffice. The same is true for \(V_-\). The upper has to come from the arithmetic of the actual signed counts. The statement pays the opposite sign in the logical closing test; it does not say that its energy is small.

## A sign-preserving transfer to the grid

Both upper bounds follow from the full positive tree energy. For the lower when \(b>0\), write \(T=\log X\) and take \(0<\sigma<.005\). The [complete signed-history estimate, equation (5)](SINGLE_PROBE_SCALES.md) supplies **both** lower integrals
\[
 \int_{I''}[\pm W(t)]_+\,dt\ge X^{(1-\sigma)b-o(1)} .
\]
Here \(W(t)=\sum_q\mu_y(q)\,q^{-1/2}h(t-\log q)\), with \(h=\mathbf1_{[0,1]}*\mathbf1_{[0,1]}\) the nonnegative Lipschitz tent. The same true interval \(I''\), of length \(O(\log X)\), works for both signs. Throughout that interval every contributing label is in the actual terminal range. The proof uses the positive xi kernel and the signed convolution with its entire source history before making that restriction. In particular the assertion concerns positive and negative parts of the same actual input at each horizon. It is stronger than an absolute lower on one sample.

Fix \(t\in I''\). In shell \(U\), write the test weight as \(U^{-1/2}\phi(q/U)\), where \(\phi(v)=v^{-1/2}h(t-\log U-\log v)\) has uniformly bounded sup norm and Lipschitz constant and is nonnegative on \([1,2]\). In each occupied node take the minimum value of \(\phi\) over its actual nonzero terminal labels. On a child the minimum increases or stays fixed. Use the base minimum as the coefficient at the root and the child minimum minus the parent minimum as the coefficient at a finer node. The sum down the path to a singleton recovers exactly that label's test value. Empty nodes can be omitted. Thus the signed observation is an **exact nonnegative** linear combination of the original node charges; neither the sign nor the absolute value of a charge was used to choose the minima.

To check its norm, denote the coefficient including \(U^{-1/2}\) at node \(J\) by \(c_J(t)\). The root coefficient is \(O(U^{-1/2})\); at depth \(k\ge1\), the parent diameter gives \(c_J=O(U^{-1/2}2^{-s-k})\). With \(w_J=2^{-k}/U\), the \(2^s\) roots cost \(O(2^s)\) in \(\sum c_J^2/w_J\) per shell. Each finer depth has at most \(2^{s+k}\) nodes and costs \(O(2^{-s})\). Across all depths and shells the total is \(X^{o(1)}\). Hence pointwise
\[
 [\pm W(t)]_+\le \sum_J c_J(t)[\pm f_J]_+
       \le X^{o(1)}\sqrt{V_\pm(X)} .
\]
The upper constant is uniform in \(t\). Integrate, use the lower on each polarity, take the lower limit in \(X\), then take \(\sigma\downarrow0\). This proves (1) for the complete tree. Removing fine nodes costs \(O(\log X)\) for each polarity by the absolute fine-level square bound, proving the coarse version. For \(b=0\) use the full upper and the added one. The passage back to the original primitive covariance uses the same signed large-GCD estimate as [the rough detector](ROUGH_PRIME_TRANSPORT.md). No terms are discarded from the original source equation.

The test also works after **omitting both outer clipped shells entirely**. For each fixed \(\sigma>0\), all the tent's inputs in \(I''\) lie a factor tending to infinity inside the terminal limits, so their shells are whole. Use just those complete shells in the same positive-coefficient pairing. More generally for fixed \(.99<r<u<1\), keep only complete shells inside \([X^r,X^u]\). Use \(t_1=(r+\eta)\log X,\ t_2=(u-\eta)\log X\), with \(0<2\eta<u-r\), in the signed-history proof. All influencing shells then fit inside this smaller band after its \(O(\log\log X)\) padding. The lower exponent for either squared polarity is at least \(2(u-\eta)b\); sending \(\eta\) to zero gives \(2ub\). The matching upper follows from the restricted Mertens interval bound \(O_\epsilon(X^\epsilon U^{1/2+b})\) times the weighted node count \(O(2^s\log X/U)\) in each shell. Thus \(1+V_\pm^{[r,u]}=X^{2ub+o(1)}\). This is a detection result on a smaller observable. It makes no upper-bound claim for the discarded boundary shells by themselves.

## Fewer prime-probe comparisons

Let \(p_J\le0\) be the signed count of rough primes. Keep in the [single-prime determinant](SINGLE_PROBE_SCALES.md) only node pairs with \(f_I f_J\le0\). This includes zero-charge nodes. For these pairs,
\[
 (p_I f_J-p_J f_I)^2\ \ge\ p_I^2 f_J^2+p_J^2 f_I^2.
\]
Summing gives a lower of \(\|P\|^2\min(V_+,V_-)\): partition the prime energy by positive, negative and zero \(f_J\); it pairs with the opposite sign of \(f\), or with both for zero. Such pairs have distinct endpoints automatically when a product of the two squared terms is nonzero. The full prime norm squared is \(X^{1+o(1)}\), by ordinary PNT and the whole-shell base count. The ordinary determinant upper and (1) therefore give
\[
 1+\frac1X\sum_{\substack{I<J\\ f_I f_J\le0}}w_Iw_J(p_I f_J-p_J f_I)^2
       =X^{2b+o(1)} .
\]
Within this smaller observable, [small width-product pairs](TWO_ARITHMETIC_PROBES.md) cost \(O(X\log^4(2X))\) together. At most \(O(2^s\sqrt X\log^4(2X))\) unordered node pairs remain before the sign check: at two specified shell-depth choices their number is at most \(UV/(H_IH_J)<2^s\sqrt{UV/X}\le2^s\sqrt X\). This bound is on the number of candidate comparisons and does not bound their remaining weights.

**OPEN.** Neither one-sided excess has an independently established cofinal subpower upper. Finite sums, small prime deficits and the signed-history lower do not establish this one-sided arithmetic constraint. The result identifies precisely which sign information can be removed from the obligation while preserving the full zero-sensitive implication.

An exact moving-cutoff control illustrates the distinction. At \(2^{20}\) the full coarse \(V_+\) is zero. It stays zero for the next 578 cutoffs, then equals \(31/33554432\) at \(1{,}049{,}155\). The negative prime 913337 has just left through the lower endpoint. In the clipped interval \([913338,913408)\), three positive semiprimes and two negative primes give charge \(+1\). Five nested nodes register that surplus. This is an endpoint effect on a finite range, and the complete-shell test above is designed to work without either endpoint. [One-sided counts](ONE_SIDED_NODE_CHECK.json) · [First positive cutoff and factors](FIRST_POSITIVE_COARSE.json)
