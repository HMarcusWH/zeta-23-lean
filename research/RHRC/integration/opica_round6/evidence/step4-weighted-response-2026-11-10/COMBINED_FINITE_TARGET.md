# A smaller exact arithmetic target, with both discarded costs paid

10 November 2026. **DERIVED paper reduction, not a proof of the required arithmetic upper.** No Lean or CI claim. The full actual source and complete divisor identity are retained.

## 1. Fix every object first

Use the literal fixed source h, S=1/2048, and t0=log(2)-S>0. Let

\[
Z(t)=\sum_{m\ge2}\Lambda(m)m^{-1/2}h(t-\log m),\quad
U(t)=\sum_{m\ge2}(\log m)m^{-1/2}h(t-\log m).
\]

Both vanish for t<t0. The exact finite divisor identity gives

\[
Z(t)=\sum_{n\ge1}\mu(n)n^{-1/2}U(t-\log n).
\tag{1}
\]

Keep this full identity available throughout the proof. Introduce a partial sum only with an explicit bound for the difference.

The elementary source estimate and fixed second-order Euler–Maclaurin estimate give constants C0,B2 depending only on h, fixed independently of T, such that

\[
|Z(t)|\le C_0(1+t)e^{t/2},\qquad
|U(t)|\le B_2(1+t)e^{-3t/2}\quad(t\ge0).
\tag{2}
\]

For example, C0=e^(3S/2)(1+S)||h||infinity works, and

\[
B_2=\frac{\|f_0''\|_1+\|f_1''\|_1}{12},\quad
f_0(y)=y^{-1/2}h(-\log y),\quad f_1(y)=(\log y)f_0(y)
\]

works after extending those smooth compact profiles by zero. Their integrals vanish by the actual half-pole moments. Only this fixed derivative order is needed below.

## 2. Define the remaining complete signed sum

For each t>=0, define

\[
V(t)=\sum_{e^{t/2}<n\le e^{t-t_0}}
\frac{\mu(n)}{\sqrt n}U(t-\log n).
\tag{3}
\]

The inequalities describe integer indices exactly, including noninteger and boundary cutoffs. Values at t-log(n)=t0 vanish anyway. When the upper endpoint is below the lower endpoint the sum is empty. This is an inverse-history cutoff, not the prime-only cutoff of A09.

For n<=e^(t/2), (2) gives

\[
\begin{aligned}
\left|\sum_{n\le e^{t/2}}\frac{\mu(n)}{\sqrt n}U(t-\log n)\right|
&\le B_2(1+t)e^{-3t/2}\sum_{n\le e^{t/2}}n\\
&\le B_2(1+t)e^{-t/2}.
\end{aligned}
\tag{4}
\]

The last inequality uses sum_(n<=N)n<=N^2 for integer N>=1. All indices beyond e^(t-t0) have zero drive value. Therefore (1) and (4) give the actual-source bound

\[
|Z(t)-V(t)|\le B_2(1+t)e^{-t/2}.
\tag{5}
\]

The terms removed here have integer-drive age at least t/2. No assertion is made that the remaining Möbius signs are independent or random.

## 3. Compose the two reductions at the same horizon

Let omega_T(t)=exp(-(T-t)/2) and define

\[
\mathcal V(T)=\int_{T/2}^{T}\omega_T(t)|V(t)|\,dt.
\]

The entire chronological prefix costs

\[
\int_0^{T/2}\omega_T(t)|Z(t)|dt
\le\frac{C_0T}{2}.
\tag{6}
\]

The inverse-history replacement costs, even when bounded on the larger interval [0,T],

\[
\int_0^T\omega_T(t)|Z(t)-V(t)|dt
\le B_2(T+T^2/2)e^{-T/2}.
\tag{7}
\]

Combining the reverse triangle inequality with (6)–(7),

\[
\boxed{|A_Z(T)-\mathcal V(T)|\le
\frac{C_0T}{2}+B_2(T+T^2/2)e^{-T/2}.}
\tag{8}
\]

This is valid at every T>=0. It preserves one common horizon and all original arithmetic information, with the deleted contributions explicitly paid. No limit interchange, global L2 assumption, or growing derivative order is used.

Consequently the every-positive-rate cofinal upper for A_Z is equivalent to the same upper for mathcal V. For a requested rate eta, use the upper at eta/2 and absorb the fixed polynomial after fixing its constants; then enlarge the lower horizon before invoking the cofinal statement. The two directions use the same argument.

Under a hypothetical zero with displacement delta, a cofinal upper for mathcal V at any fixed 0<=eta<delta also suffices: add the polynomial in (8), and compare with the existing eventual exp(delta*T) lower at the same selected horizon. No assertion that eta=0 absorbs a polynomial into a constant is needed; the polynomial itself is smaller than exp(delta*T).

## 4. What the full OPICA machinery still has to bound

The remaining region is precisely

\[
T/2\le t\le T,\qquad e^{t/2}<n\le e^{t-t_0},\qquad
t_0\le t-\log n<t/2.
\]

The integer drive U in this region is still its full signed integer sum, and the outer coefficients are still the exact signed Möbius inverse. The task is to bound their complete interaction before the absolute value, not the individual terms.

The divisor investigation establishes that the actual absolute inverse envelope has size c_U exp(t/2), with c_U>0. This remains true after the negligible sector (4) is removed. Thus its weighted late-half cost has the same forbidden exp(T/2) leading scale. Merely using rapid decay of U, squarefree support, or its positive/negative moment identities cannot supply (8)'s missing upper.

The scale investigation identifies the same target as normalized total variation of a genuine compact prime-power primitive. The operator investigation identifies it as a weighted norm of a particular complete prime-source response column. These are mutually compatible representations of one arithmetic problem. Their equalities do not yet imply an upper bound.

## 5. First unproved line

There is no independent estimate here proving

\[
\forall\eta>0\ \exists C_\eta>0\ \forall R>0\ \exists T\ge\max(R,16):
\quad \mathcal V(T)\le C_\eta e^{\eta T}.
\]

The reduction makes the remaining arithmetic domain smaller and rules out a specific absolute-value shortcut. It does not replace or discharge that line. Step 4 remains OPEN.

## Sources and derivation scope

- [Actual source definitions and rapid integer-drive theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/OPICARound4/ActualSourceHyperbola.lean).
- [Original source fixed-order derivative machinery](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/UniversalSincInverseGevreyBounds.lean), read at the current pinned head; the present proof only needs fixed second order and does not claim a new Gevrey theorem.
- Centered weighted zero lower.
- This round's detailed divisor, scale and source-column notes are linked from the live research checkpoint.
