# Two dense prime interaction graphs on the genuine source

**Paper result, 19 November 2026.** Ordinary PNT independently gives the sign and leading size of each of two dense sets of actual prime pairs at every late observation time. The sets are determined by the distance between their logarithms. Their leading terms and all terms linear in the deviation of the prime distribution cancel when they are recombined. The signed quadratic deviation remains.

Use exactly the native one-copy source \(j=(D^2-1/4)^2q_s\), \(s=1/4096\). On the fixed compact interval \([-s,s]\) define
\[
 \nu_t=e^{-t/2}\sum_{\substack{p\ {\rm prime}\\ |t-\log p|\le s}}
       \frac{\log p}{\sqrt p}\,\delta_{t-\log p},\qquad
 g(v)=e^{-v/2}j(v).
\]
Partial summation against the ordinary prime number theorem gives weak convergence of these positive measures to \(e^{-v/2}dv\). For a smooth test this follows by replacing \(d\vartheta(y)\) by \(dy\), integrating its error once on \([e^{t-s},e^{t+s}]\), and using \(\sup |\vartheta(y)-y|/y\to0\) there. Their total masses are bounded, so uniform approximation handles continuous tests. The double-product measures converge weakly as well. Sets with the boundaries \(|v-w|=\Delta\) are continuity sets for the limit.

The source moments imply \(\int g=0\) by two integrations of \(D^2-1/4\) against \(e^{-v/2}\). For \(\Delta>0\) put
\[
 K_\Delta=\iint_{|v-w|\le\Delta}g(v)g(w)\,dv\,dw.
\]
Extend \(g\) by zero. Translating an \(H^1\) function gives \(\|g(\cdot+u)-g\|_2\le |u|\|g'\|_2\). Therefore
\[
 K_\Delta=2\int_0^\Delta\langle g,g(\cdot+u)\rangle du
 \ \ge\ 2\Delta\|g\|_2^2-\frac{\Delta^3}{3}\|g'\|_2^2.
\]
Take the fixed \(\Delta=\min(s,\|g\|_2/\|g'\|_2)>0\), determined entirely by the native source. Then \(K_\Delta\ge(5/3)\Delta\|g\|_2^2>0\).

At time \(t\), let \(N_\Delta(t)\) be the ordered signed sum of the ordinary-prime products \(v_p(t)v_q(t)\) with \(p\ne q\) and \(|\log(p/q)|\le\Delta\), where \(v_p(t)=(\log p)/\sqrt p\,j(t-\log p)\). Let \(F_\Delta(t)\) be the complementary ordered distinct-pair sum. Divide by \(e^t\) and apply product convergence. The diagonal is \(O_j(t)\) in unnormalized units. The limiting unrestricted product has integral \((\int g)^2=0\). Thus
\[
       N_\Delta(t)=(K_\Delta+o(1))e^t,\qquad
       F_\Delta(t)=(-K_\Delta+o(1))e^t.                  \tag{1}
\]
Here the upper limit on physical interaction width is \(2s\), while the internal cut \(\Delta\) is strictly smaller. A fixed window in logarithmic distance still allows exponentially many integer separations. In particular a constant logarithmic width and bounded graph degree impose very different arithmetic restrictions.

The positive Gauss rule from the [one-copy graph deduction](NATIVE_WINDOW_GRAPH_DEDUCTION.md) integrates constants on each panel of width \(O(1/n)\). The maximum of \(e^t\) on such a panel is at most \(e^{O(1/n)}\) times its minimum, so
\(\sum_i w_i e^{t_i}=(1+o(1))e^n(1-n^{-2})\).
The least node tends to infinity and (1) therefore sums to the same leading constants times \(e^n\). The sparse additive gaps removed in the companion deduction cost \(O_j(n\log n\,e^{\sqrt n})\). Removing those gaps leaves (1)'s terminal leading constants intact. The actual diagonal and all prime powers are separately paid as specified in that deduction.

There is also an exact arithmetic cancellation before estimating any error. Let \(\tau=g(v)dv\), \(r_t=j\nu_t-\tau\), and write \(B_\Delta\) for the bilinear integral over \(|v-w|\le\Delta\). Including the diagonal while making the split, the near contribution divided by \(e^t\) is
\[
 K_\Delta+2B_\Delta(\tau,r_t)+B_\Delta(r_t,r_t).
\]
Because \(\tau([-s,s])=0\), the complementary contribution divided by \(e^t\) is exactly
\[
 -K_\Delta-2B_\Delta(\tau,r_t)
    +r_t([-s,s])^2-B_\Delta(r_t,r_t).
\]
All first-order marginal errors cancel *at each actual node*. The remaining real nonnegative energy is \(e^t r_t([-s,s])^2\), the full ordinary-prime field squared in its original normalization. Hence estimating the two leading constants more accurately, without controlling this actual discrepancy, cannot close Step 4. Under the external displacement ceiling \(b\), the terminal complete energy has exponential rate at most \(2b\), while each of (1)'s dense components has rate one. Proving a cofinal all-positive-exponent upper for the signed far-additive-gap sum in the companion note would close the remaining gap. **That upper is OPEN.**

[Native field and support](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeSourceFamily.lean) · [Original source moments](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/CCM/OriginalSincWeightedPoleMoments.lean) · [PNT for the actual prime staircase](https://dlmf.nist.gov/27.2)
