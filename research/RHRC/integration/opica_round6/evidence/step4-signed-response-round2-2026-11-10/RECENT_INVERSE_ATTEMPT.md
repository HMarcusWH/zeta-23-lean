# Recent inverse attempt: a logarithmic-age restriction, with the genuine signed obstruction retained

10 November 2026. **DERIVED paper mathematics; no new Lean compilation, no CI qualification, no Step 4 closure.** This extends the preceding complete-source inverse reduction. It uses the actual universal-sinc source's quantitative Gevrey theorem rather than treating C-infinity regularity as a free growing-order budget.

The full original arithmetic coupling remains

\[
Z(t)=\sum_{m\ge2}\Lambda(m)m^{-1/2}h(t-\log m),\quad
U(t)=\sum_{m\ge2}(\log m)m^{-1/2}h(t-\log m),\quad
Z(t)=\sum_{n\ge1}\mu(n)n^{-1/2}U(t-\log n).
\tag{1}
\]

Every sum is locally finite. The source h is unchanged, S=1/2048, and both fields vanish before t0=log(2)-S. The completion a*Z=c*U is not changed or inverted in a stronger function space.

## 1. The actual integer drive has a justified stronger envelope

The current actual q has fixed positive Gevrey-order-two constants. Fixed derivatives and convolution therefore give constants C,A with

\[
\sup_u|h^{(k)}(u)|\le C A^k(k!)^2\qquad(k\ge0).
\tag{2}
\]

This step is already used in the previous round's Fourier input adapter. It follows from the literal `universalSincSource_gevrey_bound`, not from an arbitrary-source assumption.

Put f0(y)=y^(-1/2)h(-log y), f1(y)=(log y)f0(y), extended by zero. There are fixed G>0 and A>=1 such that

\[
\|f_0^{(k)}\|_1+\|f_1^{(k)}\|_1\le G A^k(k!)^2
\qquad(k\ge0).
\tag{3}
\]

Here is an elementary justification of the composition loss. On the fixed interval [exp(-S),exp(S)], the analytic derivatives of phi(y)=-log y obey |phi^(j)|/j!<=D^j for a fixed D. The finite chain-rule coefficient formula gives

\[
\frac{|(h\circ\phi)^{(k)}|}{k!}
\le C D^k\sum_{m=1}^k A^m m!\binom{k-1}{m-1}
\le C D^k k! A(1+A)^{k-1}.
\]

Multiplication by the fixed analytic factors y^(-1/2) and log y preserves this bound after increasing the fixed exponential base. The factors (k+1) from the Leibniz sum are absorbed into that base. Compact support and flat endpoints then give (3) globally and in L1. Thus no horizon-dependent derivative constant has been hidden.

The actual half-pole moments give integral f0=integral f1=0. At x=exp(s),

\[
U(s)=x^{-1/2}\left[s\sum_m f_0(m/x)+\sum_m f_1(m/x)\right].
\]

For each even k>=2, Euler–Maclaurin with vanishing endpoint terms and (3) yields

\[
|U(s)|\le G(1+s)e^{s/2}(A e^{-s})^k(k!)^2.
\tag{4}
\]

One does not need a sharp Bernoulli bound: the normalized periodic Bernoulli functions satisfy ||B_k/k!||infinity<=1/2 for k>=1. Indeed B1 has that bound, each subsequent normalized function has mean zero and derivative equal to its predecessor, and its oscillation is bounded by the integral of the absolute derivative. This coarse bound suffices for (4).

Set X=e^(s/2)/sqrt(A). When X>=8 choose the even order k=2 floor(X/4). Then X/4<=k<=X/2 and k!<=k^k, so

\[
(A e^{-s})^k(k!)^2\le(k^2/X^2)^k\le4^{-k}
\le\exp\left[-\frac{\log4}{4\sqrt A}e^{s/2}\right].
\]

For X<8, use the elementary actual-drive bound |U(s)|<=C0(1+s)e^(s/2). Increasing the fixed constant by at most 16 covers this compact initial range. Consequently fixed source constants C_h,c_h>0 give the unconditional envelope

\[
\boxed{|U(s)|\le C_h(1+s)e^{s/2}\exp(-c_h e^{s/2}),\quad s\ge0.}
\tag{5}
\]

For example c_h=log(4)/(4sqrt(A)), C_h=max(G,16C0) work with the preceding choices. This is a derived actual-source bound; it is not attributed to an existing Lean declaration that only states fixed-order rapid decay.

## 2. Remove all but logarithmically recent integer-drive ages

Choose once and for all

\[
B\ge\max(1,2/c_h),\qquad q(t)=B^2(t+2)^2.
\]

Define the complete old-age part and retained part by

\[
O(t)=\sum_{1\le n\le e^t/q(t)}\frac{\mu(n)}{\sqrt n}U(t-\log n),
\qquad V_{\log}(t)=Z(t)-O(t).
\]

If e^t/q(t)<1 the first sum is empty. Otherwise every old-age sample has s=t-log n>=log q(t), and (5) gives

\[
\begin{aligned}
|O(t)|
&\le C_h(1+t)e^{t/2}
\sum_{n\le e^t/q(t)}\frac1n
\exp\left(-c_h\sqrt{e^t/n}\right)\\
&\le C_h(1+t)^2e^{t/2}\exp[-c_hB(t+2)]\\
&\le C_h e^{-4}(1+t)^2e^{-3t/2}.
\end{aligned}
\tag{6}
\]

We used only sum_(n<=N)1/n<=1+log N<=1+t and c_h B>=2. The empty-sum case also satisfies the bound. All original terms remain in (1); (6) explicitly pays those absent from V_log.

The retained sum is therefore exactly

\[
V_{\log}(t)=\sum_{e^t/q(t)<n\le e^{t-t_0}}
\frac{\mu(n)}{\sqrt n}U(t-\log n).
\tag{7}
\]

Its integer-drive ages satisfy

\[
t_0\le t-\log n<2\log[B(t+2)].
\]

This is narrower than the previous fixed-fraction age range. B can be large at the tiny fixed source scale; no practical reduction at L4 or L5 is claimed. B is fixed before later horizons and is not chosen from a desired outcome.

For the exact age-weighted norm, (6) gives

\[
\boxed{|A_Z(T)-A_{V_{\log}}(T)|
\le5C_h e^{-4}e^{-T/2}.}
\tag{8}
\]

Indeed the weighted error is at most C_h e^(-4)e^(-T/2) times integral_0^T (1+t)^2e^(-t)dt, whose full half-line integral is 5.

Combining this with the already paid chronological prefix gives

\[
\boxed{\left|A_Z(T)-\int_{T/2}^{T}e^{-(T-t)/2}|V_{\log}(t)|dt\right|
\le C_0T/2+5C_h e^{-4}e^{-T/2}.}
\tag{9}
\]

Thus the required cofinal upper is equivalent, at the same horizons and after paid polynomial absorption, to the new logarithmic-age target. This is a true quantitative reduction, not an estimate of the remaining signed sum.

## 3. The short integer factor is now only polynomial in observation time

Expanding the *whole* U inside (7), its compact source support gives m<=exp(S)q(t). Hence the exact retained expression can be written

\[
V_{\log}(t)=
\sum_{2\le m\le e^S q(t)}\frac{\log m}{\sqrt m}
\sum_{e^t/q(t)<n\le e^{t-t_0}}
\frac{\mu(n)}{\sqrt n}h(t-\log(mn)).
\tag{10}
\]

All indices are integers under the displayed real cutoffs. Endpoint h values vanish, so the inclusive upper bounds create no extra contribution. This is a complete finite double sum; no prime powers or complementary terms were selected away.

The small integer factor is O_h((1+t)^2), rather than exp(t/2). The remaining long factor carries the exact Möbius signs and the source cutoff. Treating the terms of (10) separately would require additional cancellation estimates for the long Möbius sums, and may lose cancellation between different m. The double-sum identity itself supplies no such estimate.

## 4. The native absolute-value obstruction survives this narrower range

The proof of (6) also applies with |mu(n)| and |U|. Therefore the previously established genuine-source asymptotic

\[
\sum_{n\ge1}\frac{|\mu(n)|}{\sqrt n}|U(t-\log n)|
\sim c_U e^{t/2},\quad
c_U=\zeta(2)^{-1}\int_0^\infty e^{-s/2}|U(s)|ds>0
\]

is unchanged when n<=e^t/q(t) is removed. The late-half weighted absolute envelope still has asymptotic c_U e^(T/2). The analogous signed-U but mu-squared control also retains its positive exp(t/2) leading coefficient.

Thus narrowing the ages does not turn the remaining family into a small absolute sum. It locates the cancellation but does not establish it. This is a control for an estimate on the **actual** kernel, not a substitution of another prime field.

## 5. Test the tempting special-kernel annihilation argument in exact arithmetic

One possible hope is that the many actual U moments annihilate the unstable modes of Möbius inversion. The exact transforms show why that inference is unsupported.

Define the fixed signed profile

\[
F(y)=y^{-1/2}U(-\log y)\quad(0<y\le1),\qquad F(y)=0\ (y>1).
\]

The new envelope makes its Mellin integral converge for every complex z. Causality removes a neighborhood of y=1, and the double-exponential bound removes every power divergence at y=0. With H(z)=integral exp(-zu)h(u)du,

\[
\mathcal M F(z)=\int_0^\infty F(y)y^{z-1}dy
=\widehat U(z-1/2)=-H(z-1/2)\zeta'(z).
\tag{11}
\]

The identity is first justified by absolute convergence for Re z>1 and then by analytic continuation; the double source zero pays the zeta-prime pole at 1. On that same initial half-plane the exact Dirichlet-series Möbius inverse gives

\[
\frac{\mathcal M F(z)}{\zeta(z)}
=-H(z-1/2)\frac{\zeta'(z)}{\zeta(z)}.
\tag{12}
\]

Suppose, as a diagnostic, rho is an actual hypothetical nontrivial zero of multiplicity m and the unchanged source is visible there. Then zeta-prime has a zero of order m-1. Equation (11) therefore cancels **m-1**, not m, orders of the inverse pole. Precisely,

\[
-H(z-1/2)\frac{\zeta'(z)}{\zeta(z)}
=\frac{-mH(\rho-1/2)}{z-\rho}+\text{a holomorphic function near }\rho,
\tag{13}
\]

and the residue is nonzero by actual source visibility. This computation retains the genuine divisor coupling and every source moment. It does not assert a zero exists, assume a rightmost zero, or identify one isolated residue with the entire time response. It shows that the special drive is not an automatic annihilator of the hypothetical mode. An argument claiming that all such modes disappear merely because U is very small would contradict the local transform algebra (13).

This is fully compatible with a future arithmetic contradiction ruling out rho. What has not been supplied is the independent signed estimate that would produce that contradiction.

## 6. First unsupported line after this attempt

The new reduction leaves the exact finite quantity in (9)–(10). The required new inequality remains

\[
\forall\eta>0\ \exists C_\eta>0\ \forall R>0\ \exists T\ge\max(R,16):
\quad\int_{T/2}^T e^{-(T-t)/2}|V_{\log}(t)|dt
\le C_\eta e^{\eta T}.
\]

A legitimate hypothetical-zero-dependent rate below its positive displacement would also suffice. No such upper was derived here. Applying Cauchy or separate absolute bounds to (10) does not prove it; the native absolute-envelope control shows the size of that loss. Fixed local source moments also do not prove it, as the exact residue calculation makes explicit.

**New useful result:** the actual Gevrey theorem upgrades the inverse-age cutoff to O(log t), leaving a complete polynomial-short-factor/arithmetic-long-factor sum with exponentially vanishing discarded error. **Still OPEN:** its independent signed cancellation and the Step 4 closure.

## Sources and qualification

- [Literal full source, integer action and rapid drive](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/OPICARound4/ActualSourceHyperbola.lean).
- [Actual universal-sinc Gevrey theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/UniversalSincPhysicalBounds.lean) and its [derivation](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/UniversalSincInverseGevreyBounds.lean), current snapshots read in the preceding round and used here with their exact quantified scope.
- Previous complete-source inverse proof, squarefree-density controls and retained opposite weighted moments: `work/step4-weighted-response-2026-11-10/DIVISOR_RESEARCH.md`.
- Exact source visibility and full weighted lower remain inherited paper/formal inputs with their existing qualifications; no compiler was run here.

No novelty claim beyond this project's new composition is made. The work establishes supporting derived estimates, not an unconditional prime-error theorem or RH.
