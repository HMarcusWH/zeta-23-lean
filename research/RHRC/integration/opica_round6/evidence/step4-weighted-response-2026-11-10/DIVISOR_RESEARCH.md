# Complete divisor coupling: controlled inverse histories and a native absolute-value barrier

10 November 2026. **DERIVED paper arguments; not Lean-compiled or CI-qualified. Step 4 remains OPEN.** This pass works on the selected complete-source weighted response. It does not modify the source, repository, arithmetic coefficients, or any acceptance gate.

## 1. Literal objects and identities retained

Freeze the actual universal-sinc seed q, S=1/2048, and h=((D²−1/4)q)*((D²−1/4)q). Retain

\[
 Z(t)=\sum_{n\ge2}\Lambda(n)n^{-1/2}h(t-\log n),\qquad
 U(t)=\sum_{n\ge2}(\log n)n^{-1/2}h(t-\log n).
\]

Both fields vanish before t0=log(2)−S>0. Every history is causal and locally finite. Write

\[
 (N*f)(t)=\sum_{n\ge1}n^{-1/2}f(t-\log n),\qquad
 (M*f)(t)=\sum_{n\ge1}\mu(n)n^{-1/2}f(t-\log n).
\]

The exact coefficient identities 1*Λ=log and μ*1=ε imply, at each finite time and without an infinite rearrangement,

\[
 U=N*Z,\qquad Z=M*U.
\tag{1}
\]

The original completion a*Z=c*U remains intact. Equation (1) does not replace it with an arbitrary input. In particular the U below is the complete actual integer drive, not a test profile with the same moments.

The target remains

\[
 A_Z(T)=\int_0^T e^{-(T-t)/2}|Z(t)|dt,
\]

with an independent cofinal upper at every fixed positive exponent. Absolute values must stay outside the full signed sum defining Z.

## 2. Every fixed decay order of the actual integer drive

For each even integer k≥2, put

\[
 f_0(y)=y^{-1/2}h(-\log y),\quad f_1(y)=(\log y)f_0(y),
\]

extended by zero off the positive half-line. These are smooth compact profiles. The half-pole moments give ∫f0=∫f1=0. At x=e^t,

\[
 U(t)=x^{-1/2}\left[t\sum_n f_0(n/x)+\sum_n f_1(n/x)\right].
\]

The fixed-order Euler–Maclaurin remainder, with all endpoint terms zero, gives

\[
 |U(t)|\le B_k(1+t)e^{-(k-1/2)t},\quad t\ge0,
\tag{2}
\]

where one valid fixed constant is

\[
 B_k=\frac{\|\widetilde B_k\|_\infty}{k!}
 (\|f_0^{(k)}\|_1+\|f_1^{(k)}\|_1).
\]

Here tilde-B is the periodic Bernoulli polynomial. Each chosen k and its derivative constant are fixed before t or T. No derivative-order-uniform estimate is used. For k=4 this recovers the previously derived e^(−7t/2) envelope, rather than attributing this strength to a weaker formal declaration.

## 3. Exact removal of the long-age inverse sector

Fix any 0≤α<1 and choose one even k with b=k(1−α)−1/2>0. Split the actual inverse identity exactly:

\[
 Z_{\rm old,\alpha}(t)=\sum_{1\le n\le e^{\alpha t}}
 \frac{\mu(n)}{\sqrt n}U(t-\log n),\qquad
 Z_{\rm recent,\alpha}(t)=Z(t)-Z_{\rm old,\alpha}(t).
\]

The labels refer to the **age of the integer-drive sample in Möbius inversion**. They are not the original prime-field cutoff, the A09 square-root mask, or a primitive-pair cutoff.

For every term of the first sum, s=t−log n lies between (1−α)t and t. By (2),

\[
 |Z_{\rm old,\alpha}(t)|
 \le B_k(1+t)e^{-(k-1/2)t}
       \sum_{n\le e^{\alpha t}}n^{k-1}
 \le B_k(1+t)e^{-bt}.
\tag{3}
\]

Consequently, for every T≥0,

\[
 |A_Z(T)-A_{Z_{\rm recent,\alpha}}(T)|
 \le B_k\left(\frac1b+\frac1{b^2}\right).
\tag{4}
\]

The proof is the reverse triangle inequality, then the bound of the time weight by one and integration of (1+t)e^(−bt). The actual error also tends to zero: dominated convergence applies to that integrable envelope multiplied by e^(−(T−t)/2)1_0,T.

Thus for **every fixed α<1**, the complete weighted target is equivalent up to a fixed bounded cost to the retained inverse coefficients n>e^(αt). No contribution was discarded without a paid error. This localizes the unknown cancellation near the full exponential inverse cutoff; it does not prove that cancellation. Choosing α depending on T would require new control of k and Bk and is not justified here.

## 4. Taking absolute values of the inverse coefficients has an exact exponential cost

Define the actual absolute inverse envelope

\[
 B_{\rm abs}(t)=\sum_{n\ge1}\frac{|\mu(n)|}{\sqrt n}
                    |U(t-\log n)|.
\]

This bounds |Z(t)|, but it is far too large at the required scale. In fact,

\[
 e^{-t/2}B_{\rm abs}(t)\longrightarrow
 c_U:=\frac1{\zeta(2)}\int_0^\infty e^{-s/2}|U(s)|ds>0.
\tag{5}
\]

This uses the actual μ and actual complete U, rather than a free oscillatory example.

Proof: the elementary identity μ(n)²=Σ_(d²|n)μ(d) gives

\[
 Q(X):=\sum_{n\le X}|\mu(n)|=\frac{X}{\zeta(2)}+O(\sqrt X).
\]

Indeed expand the floors, bound their total errors by √X, and bound the tail of the absolutely convergent sum Σμ(d)/d² by O(X^(−1/2)). No zero-free region is used.

Put F(y)=y^(−1/2)|U(−log y)| for 0<y≤1, and F(0)=0. The field vanishes near y=1; (2) makes F continuous at zero, bounded, and supported in [0,e^(−t0)]. For x=e^t,

\[
 e^{-t/2}B_{\rm abs}(t)=\frac1x\sum_{n\ge1}|\mu(n)|F(n/x).
\]

The squarefree counting asymptotic, first for interval indicators and then by uniform approximation for continuous F, yields ζ(2)^(−1)∫F. The substitution y=e^(−s) identifies this integral with that in (5).

Strict positivity is source-specific and elementary. Since 2S<log(3/2), the whole interval [log2−S,log2+S] contains only the n=2 pulse of U. There U(t)=(log2)/√2 h(t−log2). The source h is not zero (its integral is 1/16), so U is not zero and the integral in (5) is positive.

Integrating the asymptotic against the actual age weight gives

\[
 \int_0^T e^{-(T-t)/2}B_{\rm abs}(t)dt
       \sim c_U e^{T/2}.
\tag{6}
\]

For completeness, divide the integral by e^(T/2). Its integrand becomes e^(t−T)[e^(−t/2)Babs(t)]; the mass of this exponential kernel tends to one and its bounded bracket tends to cU. Boundedness follows either from the same weighted-counting argument or directly from (2) in unit age intervals. The finite initial interval contributes zero in the limit.

Equation (6) is an actual obstruction to the **triangle-inequality proof strategy**. It is not an obstruction to the desired signed bound. It does not identify Babs with Z.

## 5. Even preserving the full signed U does not repair unsigned inversion

There is a sharper diagnostic. Keep all of U's internal pulse cancellations but replace only μ by |μ|:

\[
 Z_+(t)=\sum_{n\ge1}\frac{\mu(n)^2}{\sqrt n}U(t-\log n).
\]

The same proof, now using the continuous signed profile y^(−1/2)U(−log y), gives

\[
 e^{-t/2}Z_+(t)\longrightarrow
 \frac1{\zeta(2)}\int_0^\infty e^{-s/2}U(s)ds.
\]

The integral is not the previously canceled opposite weighted moment ∫e^(s/2)U(s)ds. For Re z>1/2, absolute convergence gives

\[
 \widehat U(z)=-H(z)\zeta'(z+1/2),\quad
 H(z)=(z^2-1/4)^2Q(z)^2.
\]

The rapid decay (2) permits a limit z↓1/2 on the left. The ordinary residue-one pole of ζ at 1 gives on the right

\[
 \int_0^\infty e^{-s/2}U(s)ds=Q(1/2)^2>0.
\tag{7}
\]

The double zero of H cancels the double pole of −ζ′; it does **not** make the value zero. Q(1/2)>0 because the actual q is a nonzero nonnegative probability density. Thus

\[
 Z_+(t)\sim\frac{Q(1/2)^2}{\zeta(2)}e^{t/2},\qquad
 A_{Z_+}(T)\sim\frac{Q(1/2)^2}{\zeta(2)}e^{T/2}.
\tag{8}
\]

This replacement is explicitly not the genuine Möbius inverse and does not preserve μ*1=ε. It therefore cannot serve as a full native counterexample. It identifies exactly the information an argument loses when it uses only squarefree support/density and preserves all source moments while forgetting the signs of μ.

## 6. Where the signed divisor attack stops

The finite exact echo identity can be paired with the sign of the actual Z without assuming global L2 membership. With sgn(0)=0 and ωT(t)=e^(−(T−t)/2),

\[
 A_Z(T)+\sum_{2\le n\le e^T}\frac1{\sqrt n}
 \int_{\log n}^T\omega_T(t)\operatorname{sgn}(Z(t))Z(t-\log n)dt
 =\int_0^T\omega_T(t)\operatorname{sgn}(Z(t))U(t)dt.
\tag{9}
\]

The right side is independently bounded by ||U||1. Equation (9) retains the full delay coupling and all cross signs. It provides no bound on AZ until the complete signed echo term on the left has an independently justified lower bound. Bounding its terms absolutely recreates the inverse problem. No such lower bound has been proved here.

Similarly, (4) reduces the research target to the actual signed sum over n>e^(αt), but no estimate on that complete retained sum is obtained. The squarefree density theorem used in (5) controls |μ|; it cannot be substituted for cancellation of μ against the precise profile U.

The first unsupported line is therefore a bound on this **signed** complete inverse response (or an equivalent actual echo anti-alignment estimate) strong enough to beat the visible zero's growth rate. The new results narrow the location of that arithmetic information and prove that an absolute inverse budget cannot supply it. They do not close Step 4.

## Scope and references

- Source/target and exact closing quantifiers: [route decision](../step4-route-selection-2026-11-10/ROUTE_DECISION.md).
- Literal current source definitions: [ActualSourceHyperbola](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/OPICARound4/ActualSourceHyperbola.lean).
- Integer action and floor kernel: [NativeFloorCompletionSource](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/NativeFloorCompletionSource.lean).
- Completion scope: [NativeCompletionEquation](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/NativeCompletionEquation.lean).
- Earlier prime-insertion and proportional-pair failures: [Pass 16](../step4-study-2026-11-09/PASS16_PRIMITIVE_AND_SIGNED_PRIME_ENERGY_REVIEW.md).

No claim of new theorem novelty is made. The new project contribution is a complete-source proof of the bounded inverse-history reduction and an explicit exponential asymptotic falsifying absolute inverse control, with the genuine coefficient/source scope and the remaining signed estimate identified.
