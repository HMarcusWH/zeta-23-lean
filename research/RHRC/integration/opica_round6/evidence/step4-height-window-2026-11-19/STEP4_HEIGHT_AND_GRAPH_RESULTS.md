# OPICA graph deductions, the improved external ceiling and a finite exclusion for the original trial

19 November 2026. **Step 4 OPEN. RH OPEN.** This paper calculation uses the full signed OPICA trial with both lobes, every prime power, both phase choices and all zero multiplicities. For every disjoint trial with center separation at most **288,000 in log-time**, the calculation rules out the negative depth required of a generated off-line packet. The closing theorem needs arbitrarily late apertures. The result also improves the previous report's bound for the full signed K5 composite residual.

## The external input and what changed

The tracker merged its exact continuum-contact theorem on 15 November. Its exact root \(\theta=0.8733458561067185768\ldots\) lies in \((13/15,7/8)\) and satisfies
\[
3888\,19^5(15\theta-13)^4(1-\theta)^5
 =7(7-6\theta)^4(9\theta-7)^5 .
\]
The pinned theorem quantifies over every Dirichlet character at every positive modulus, excluding the principal pole. At modulus one the L-function equals \(\zeta\). Thus \(\Re\rho\le\theta\) for every nontrivial zero. Write \(b=\theta-1/2\). I inspected the exact theorem, its isolation and rational comparison and the external successful proof-verification and admission checks. This imports external theorem authority. This pass did not rebuild its transitive proof. Liu's published preprint endpoint gives the slightly weaker \(0.3749570194\ldots\) displacement. The previous OPICA sieve note's exponent \(1/2\) accounts only for the classical prime-error estimate. [Tracker theorem at the merge](https://github.com/GTimG/QuasiRiemannTracker/blob/42cf5415cfaa4205caaa25ab11160724606cdc33/submissions/2026-11-13-continuum-exact-contact/src/Candidate/Main.lean) · [External proof check](https://github.com/GTimG/QuasiRiemannTracker/actions/runs/43761452075/job/132957199949) · [External admission](https://github.com/GTimG/QuasiRiemannTracker/actions/runs/43761452075/job/132984087044) · [Liu, Theorem 27.1](https://arxiv.org/html/2610.12234v2#S27)

## How the graphs changed the calculation

The merged OPICA tree is 573cda1f06d2d7a0e61349a53183311e4ba621fc at commit c867a8f15320ad6ac69177e0a498de4cb9d744f9. I traversed all 16 graph relation shards from those exact Git objects. Of 1,280,018 compiler uses, 1,236,174 distinct directed edges record use in the declaration's value. Among the 339 registered claim bindings I compared the fixed source window, slowly varying source window and fixed two-factor mask rate theorems. Their proof-value neighborhoods in the Zeta23 namespace contain 1,282, 1,281 and 1,640 other declarations, respectively. All three share 1,281, including the actual prime field, zero-displacement supremum, infinite sinc product and derivative-moment estimate. The path from the two-factor mask theorem to the sinc product takes nine edges. Its path to the paid low-mask estimate takes four. The proof of the recovery-budget theorem lies outside those three value paths to the named anchors. Exact forward witnesses, definitions and the selected roots are in the graph receipt.

This led to two different uses of the common source. Its sinc product prices the discarded high zeros in the *original* two-lobe test below. Its derivative estimate makes polynomially many positive observations on a terminal log-window sufficient for the *one-copy* native field, as derived in the companion graph note. The two native fields are kept at their different source definitions. The compiler graph records mathematical dependencies. The estimates follow by reading the reached declarations and checking their hypotheses. [Merged graph and relation contract](https://github.com/HMarcusWH/zeta-23-lean/tree/c867a8f15320ad6ac69177e0a498de4cb9d744f9/research/RHRC/graph) · [Actual native source family](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeSourceFamily.lean#L17)

## The native trial over a verified horizon

Use \(s=1/4096\), the even unit-mass original density \(q\) supported on \([-s,s]\), \(k=(D^2-1/4)q,\ h=k*k\), and \(M=\int k^2\). With bilateral Laplace convention \(Q(p)=\int e^{-pv}q(v)\,dv\), the complete correlation multiplier is \(H(p)=(p^2-1/4)^2Q(p)^2\). Write \(p=\rho-1/2,\ \gamma=\Im\rho,\ g=|\gamma|\). The normalized two-lobe energy for center separation \(t=2a>2s\), aperture \(L=t+2(1+s)\), and phase \(\sigma=\pm1\), is
\[
 M\,\Re W(\phi,\phi)=C(0)+\sigma C(a)
 =\Re\sum_\rho H(p)(1+\sigma e^{pt}).
\]
The sum counts multiplicity. Reversing the sign of \(pt\) gives the same total by the zero symmetries and evenness. On the critical line \(Q(i\gamma)\) is real and \(H(i\gamma)\ge0\). Each such zero therefore contributes \(H(i\gamma)(1+\sigma\cos(\gamma t))\ge0\). This sign retains the self-energy \(C(0)\). [Weil correlation and detector](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/ExceptionalZero/UniversalSincPhysicalDetector.lean) · [Two-lobe phase and normalization](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/ExceptionalZero/UniversalSincOriginalPhaseDepth.lean)

For \(u_r=s/[r(r+1)]\) the \(r\)-th sinc factor in \(Q(p)\) has absolute value at most \(e^{u_r|\Re p|}\min(1,1/(u_r g))\) when \(g>0\). Use the integral of cosine for the first estimate and the complex sine formula for the second. Since \(\sum_r u_r=s\), taking the first \(N\) inverse factors while retaining the full product gives
\[
 |Q(p)|\le e^{s|\Re p|}\frac{N!(N+1)!}{(sg)^N}.
\]
Put \(x=\sqrt{sg}\) and \(N=\lfloor x\rfloor\). For \(N\ge1\), \(\log N!\le N\log N-N+1+\log N\) follows by integral comparison. This gives \(|Q(p)|\le e^{s|\Re p|+4}(1+x)^3e^{-2x}\), also valid when \(N=0\). Thus throughout the nontrivial-zero strip,
\[
 |H(p)|\le e^{8+s}(g+2)^4(1+\sqrt{sg})^6e^{-\sqrt g/16}. \tag{1}
\]
The source scale in the exponent comes from squaring the actual sinc product. [Original widths and scale](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/CCM/UniversalSincDetector.lean#L27)

Let \(H_0=3\cdot10^{12}\). The verified finite-height theorem places all zeros with \(0<|\gamma|\le H_0\) on the critical line. The published zero-counting estimate implies the loose bound \(N((m+1)^2)\le10(m+2)^4\) for \(m\ge1\) (using monotonicity below \(e\) if necessary), with \(N\) counting positive ordinates with multiplicity. Apply (1) in bins \(m\le\sqrt g<m+1\) and count both signs. With \(m_0=\lfloor\sqrt{H_0}\rfloor=1,732,050\),
\[
 \sum_{g>H_0}|H(p)|
 \le 60000\sum_{m\ge m_0}(m+2)^{18}e^{-m/16}<e^{-107900}.
\]
Indeed the ratio is at most \(\exp(-1/16+18/(m_0+2))\), whose geometric sum is below 20. The logarithm of the prefactor including this sum is below 14, \(18\log(m_0+2)<260\), and \(m_0/16>108253\). [Platt–Trudgian, verified zero height](https://arxiv.org/abs/2004.09765) · [Explicit zero counting](https://doi.org/10.1090/mcom/4133)

For \(t\le288000\) we have \(bt<0.374\cdot288000=107712\). Restoring the entire unchecked-height contribution therefore gives
\[
 M\,\Re W(\phi,\phi)\ \ge\ -(1+e^{bt})e^{-107900}.
\]
Finally \(\int k=-1/4\) and Cauchy–Schwarz on \([-s,s]\) gives \(M\ge1/(32s)=128\). In particular **\(\Re W(\phi,\phi)>-e^{-180}\)** throughout the specified range, for both signs. A negative-depth trial requiring \(\Re W(\phi,\phi)\le-e^{\beta L}\) with \(\beta>0\) cannot occur there. The conclusion is a paper composition of the published finite-height result, external ceiling, and the original detector. The OPICA existence theorem under an off-line zero permits arbitrarily late trials.

At an unbounded horizon \(T\), the same count shows \(\sum_{g>G}|H(p)|\ll_h e^{-\sqrt G/20}\) for large \(G\). Thus the entire tail beyond \(G=100(T+1)^2\) costs \(O_h(e^{-(1/2-b)T})\) uniformly for \(0\le t\le T\). The unresolved spectral contribution is confined to \(H_0<|\gamma|\le100(T+1)^2\). One cannot assume critical-line membership in this growing band. The corresponding arithmetic field still contains every prime power.

## Transfer to the actual K5 residual

Let \(I(T)\), \(W_T\), \(C_2(T)\) and \(C_{\ge3}(T)\) be exactly the full quantities in the squarefree report. Then
\[
 |I(T)|+|C_2(T)+C_{\ge3}(T)|\ll_\theta e^{bT}. \tag{2}
\]
To see the endpoint rate without an epsilon, take a fixed smooth \(\chi\) vanishing up to log-time 1 and equal to one from 2 onwards. The cost of replacing \(W_T\) by \(F_T=\chi W_T\) in \(I\) is polynomial in \(T\), since the compact early range contains finitely many actual atoms. The explicit formula applied to the compact test \(x^{-1/2}F_T(\log x)\) cancels the centered continuum exactly. A nontrivial zero contributes \(-\int e^{pt}F_T(t)dt\). A trivial zero at \(-2j\) contributes the analogous term with exponent \(-2j-1/2\). Their total is polynomial since \(t\ge1\). These formulas also follow by integrating the distributional prime explicit formula against the test. Its endpoint derivatives through at least order two vanish, making the zero sum absolutely convergent after the next integration. [Prime explicit formula](https://dlmf.nist.gov/25.16)

Integrating twice by parts bounds each nontrivial term by \(|p|^{-2}\int_0^T e^{bt}|F_T''(t)|dt\). The aperture kernels obey \(|W_T^{(j)}(T-u)|\ll(1+u)^{18-j}\) for \(j=0,1,2\). Indeed the kernels indexed by \(m=13,15,17\) have endpoint order \(m\); differentiating their integral \(j\) times leaves a bound by \(\int_t^T (L-t)^{m-j}dL\). The transition of \(\chi\) on \([1,2]\) costs polynomially. The remaining integral is \(O_b(e^{bT})\) since \(b>0\). Zero counting gives \(\sum_\rho|p|^{-2}<\infty\). The sieve error \(\mathrm{poly}(T)e^{O(T/\log T)}\) from the squarefree report is absorbed into \(e^{bT}\). This proves (2) without assigning the new scalar a native trial identity.

Each composite sector has magnitude asymptotic to a positive constant times \(e^{T/2}/T^2\). Thus their relative mismatch is now bounded by \(O_\theta(T^2 e^{-(1-\theta)T})\). This is a fixed exponential saving in the *relative* error; the absolute signed residual may still grow as \(e^{bT}\). Step 4 requires an independent upper \(I(T)\le C_\eta e^{\eta T}\) eventually for every \(\eta>0\), or a sufficient native arithmetic bound. The theorem imported into (2) already excludes displacements larger than \(b\). Feeding (2) back into the same zero detector cannot improve that ceiling by itself.

## What the other two graph calculations found

The historical graph contains 1,329,677 relations in total. I reconstructed the three registered RH-route dependency closures and deleted candidate vertices one at a time to test which connections survive. All three paths to the named prime functional pass through the literature explicit formula and its Weil implementation. Only the canonical remainder route reaches the explicit \(\Lambda(m)/\sqrt m\) staircase identification in these closures. The archive contains the paths and individual deletion results. The historical export contains no Round 4 declarations. I inspected the later constraint and experiment registers separately. All 45 recorded candidate results leave the independent arithmetic estimate open. [Weighted prime staircase](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/CCM/CanonicalPrimeRemainder.lean#L87) · [Frontier candidate register](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/research/RHRC/integration/opica_round4/arithmetic_frontier/CANDIDATE_RESULTS.jsonl)

The native carrier graph has four minimal combinations of the available even-ray, odd-adjoint-ray and respective strict-ground implications. The two mixed combinations work as well. Every one requires a shared negative ground to be excluded. The direct smooth-energy route has a different premise. I also checked all 10,012 rational interval containments in the separate archived PR 302 diagnostic. Its genuine K5 case at 7/4 has signed endpoint below one, positive reciprocal mass above one, and residues with signs \(+,+,-\). It supplies a concrete test for any attempt to estimate by positive parts. [Carrier implications](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICARound4/ClosureConsumers.lean) · [Archived diagnostic](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/44257687280/attempts/2)

**The new unbounded-scale deduction** uses the one-copy field. On the terminal log-window \([n-2\log n,n]\), positive quadrature preserves the exact zero-displacement growth rate. Its diagonal is asymptotic to \(2\|j\|_2^2 n\log n\). At any node and for any symmetric selection of pairs with at most \(D\) partners per prime, all selected absolute edge terms together cost at most \(D\) times that node's diagonal. The proper-prime-power field tends to \(1/32\), and its mixed terms are controlled by a two-sided norm comparison. Consequently every additive gap up to \(e^{\sqrt n}\) can be paid independently in the complete energy. What remains is one *signed* upper at arbitrarily late horizons for ordinary-prime pairs separated by more than \(e^{\sqrt n}\) and with \(|\log(q/p)|\le2/4096\). The exact sum and order of quantifiers are in the graph deduction. Even an exponentially growing but bounded-degree selection, with degree exponent below twice a putative positive displacement supremum, would leave all exponential growth in the signed complement. [Native window theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeWindowRate.lean#L1154)

**Local formal result.** Seven declarations in two new supporting modules compiled with pinned Windows Lean using warm repository imports. They include the factorial bound above on the actual original Fourier transform, for every truncation order. Their printed axioms contain only propext, Classical.choice and Quot.sound. The finite trial exclusion and the signed-pair reduction have paper status. The repository has received no new proof or claim-validation result in this pass.

## Reproducibility and scope

The companion archive contains the merged-graph path calculation and its underlying blob hashes, the source and compiler output for the sinc estimates, an interval check of the numerical inequalities and the supporting signed-response investigations. Mathematical estimates in this note have paper status. Step 4 has no new closing theorem or production CI qualification.
