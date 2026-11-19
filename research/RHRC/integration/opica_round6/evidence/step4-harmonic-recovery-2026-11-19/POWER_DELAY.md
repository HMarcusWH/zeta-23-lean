# An arithmetic recurrence on a shorter range for the graph's first harmonic

**DERIVED on paper, 19 November 2026.** This recurrence uses the Möbius labels and the full signed row. The part outside the stated range costs \(O(\sqrt x)\) unconditionally. A signed estimate inside the range remains open.

Use \(a=24/25,\ c=21/20\). Write \(\mu_6(q)=\mu(q)\mathbf1_{(q,6)=1}\), \(u(q)=\mathbf1_{(q,6)=1}\). Put \(g(y)=\cos(2\pi c y)/y\) for \(1\le y<1/a\), zero elsewhere, and \(v(x)=\sum_q\mu_6(q)g(x/q)\). If \(L=\lfloor x\rfloor\), the uniform comparison is \(xv(x)=2\pi^2 T_L+O(x)\). To see the error size, the two cutoffs differ by \(O(1)\) endpoints and the phases differ by \(O(1/q)\). For \(q\asymp L\), \(1/(q\sin^2(\pi/q))=q/\pi^2+O(1/q)\). There are \(O(L)\) terms. This is the native harmonic derived from the residue graph.

## Exact cancellation through a positive power of the cutoff

Fix \(0<\alpha<1/2\), \(Y=\lfloor x^\alpha\rfloor,\ m=Y+1,\ K=\lfloor Y\sqrt x\rfloor\). Set
\[
 b_d=\mu_6(d)\quad(1\le d\le Y),\qquad
 b_m=-m\sum_{d\le Y}\mu_6(d)/d,\qquad w_x(k)=\sum_{d\mid k,\ d\le m} b_d u(k/d).
\]
At each given \(x\), freeze these coefficients before evaluating smaller inputs. The correction imposes \(\sum b_d/d=0\). The Dirichlet convolution \(\mu_6*u=\mathbf1_{n=1}\) gives \(w_x(1)=1,\ w_x(k)=0\) for \(2\le k\le Y\) and
\[
 \sum_{k\ge1}w_x(k)v(x/k)=\sum_{d\le m}b_d g(x/d)=0
 \qquad(x/m>1/a).
\]
The convolution is finite at each \(x\). Its coefficient identity holds before taking the cosine, so no pairs of unequal products have been identified.

For all \(t\ge0\), \(U(t)=\sum_{j\le t}u(j)=t/3+O(1)\), by residues modulo six. From \(1=\sum_{d\le Y}\mu_6(d)U(Y/d)\) one gets \(\left|\sum_{d\le Y}\mu_6(d)/d\right|=O(1)\). Consequently \(\sum|b_d|=O(Y)\). Mean cancellation gives the stronger uniform discrepancy
\[
 \left|\sum_{k\le t}w_x(k)\right|
 =\left|\sum_{d\le m} b_d\,[U(t/d)-t/(3d)]\right|\ll Y
 \quad\text{at every }t.
\]
The norm of \(g\) in bounded variation, with its endpoint jumps, is finite. Only \(q\le z\) contribute to \(v\) on \((0,z]\), so its total variation there is at most \(z\,\mathrm{Var}(g)\) for \(z\ge1\). Abel summation of \(w_x(k)v(x/k)\) for \(k>K\), with its boundary term, now costs \(O(Yx/K)=O(\sqrt x)\). Thus
\[
 v(x)=-\sum_{Y<k\le K} w_x(k)v(x/k)+O(\sqrt x).
\]
For \(\alpha=1/4\) the arguments are between approximately \(x^{1/4}\) and \(x^{3/4}\). This eliminates both ends while retaining the actual shorter signed rows. The constants for large \(x\) depend only on the fixed profile and \(\alpha\).

## What a signed estimate would buy

Let \(F(z)=1+\sup_{1\le y\le z}|v(y)|/\sqrt y\). Denote the middle sum by \(D(x)\). If one could establish
\[
 |D(x)|\le C_\eta x^{1/2+\eta}F(x/(Y+1))
\]
for every fixed \(\eta>0\) at every sufficiently large \(x\), then \(|v(x)|=O_\epsilon(x^{1/2+\epsilon})\) for all \(\epsilon>0\). Indeed \(x/(Y+1)\le x^{1-\alpha}\). On each interval whose shorter arguments have already been bounded, use \(F(y)\le A y^\epsilon\). Choose \(\eta<\alpha\epsilon\), then a fixed starting point beyond which \(C_\eta x^{\eta-\alpha\epsilon}\le1/2\). Choose \(A\) to cover the base interval, the added constant and the \(O(\sqrt x)\) error. Extending the intervals by \(z\mapsto z^{1/(1-\alpha)}\) proves the bound. The zero visibility of the actual row then excludes every rightward zero. An alternative uses the positive, averaged criterion in DELAYED_GAIN.md.

Why the signed estimate costs arithmetic information can be checked independently. For each fixed set of coefficients, the Dirichlet series of \(w_x\) is
\(\zeta(s)(1-2^{-s})(1-3^{-s})\sum_{d\le m}b_d d^{-s}\). It converges for \(\Re s>0\) by the prefix discrepancy. At a zeta zero \(\rho\) of real part \(\beta>0\) the series vanishes. After \(K\), its tail has magnitude \(O_\rho(YK^{-\beta})\) by Abel summation. The negative middle operator acting on the diagnostic profile \(y^\rho\) thus returns \(x^\rho(1+O_\rho(YK^{-\beta}))\); for \(\alpha=1/4,\ \beta\ge1/2\), the relative error is \(O_\rho(x^{-1/8})\). Also every prime \(m<p\le K\), \(p>3\), has \(w_x(p)=1\), so the absolute weighted coefficient sum grows at least on the order of \(\sqrt K/\log K\) by the prime number theorem. The actual signed input is essential. The companion analysis uses \(u*v=g\) on that input to evaluate the attainable exponent of its delayed gain.

At \(x=2^{22}\), \(Y=45,\ m=46,\ K=92160\). The native row divided by \(\sqrt x\) is \(-0.01714238417\); the signed middle and tail are \(+0.02880054337\) and \(-0.01165815920\). The normalized sums of absolute row contributions are \(12.4555\) and \(37.5155\). The exact rational coefficient check covers 167,773 products, and two independent evaluations agree on all 4,194,304 prefix discrepancies. POWER_DELAY_REPLAY.json and its scripts specify the computation. DILATION_REPLAY.json tests different, primorial weights on the same input and should be read separately.
