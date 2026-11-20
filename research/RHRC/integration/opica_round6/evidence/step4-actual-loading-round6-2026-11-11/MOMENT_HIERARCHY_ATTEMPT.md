# Complete moment hierarchy: explicit higher poles, rapid compensated outputs, and the unchanged inverse deficit

11 November 2026. **DERIVED paper investigation; pending independent review. No new Lean compilation, CI qualification, repository modification, or closing arithmetic upper.** Baseline PR299 head `b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`, tree `d0a6b1ad78523c23834eb01f57f4910a22e30d3b`.

This pass uses the complete actual integer drive and all of its signed moments. It proves an explicit statement for every fixed number of forward divisor completions: after subtracting its entire causal pole polynomial, the genuine completed output decays faster than every fixed exponential. The corresponding compensated pairings with the genuine prime field are independently bounded. The full local transform calculation then shows that this entire hierarchy still has exactly the original one-order inverse deficit at a hypothetical visible zero. Neither the stronger output bounds nor the moment identities establish the missing actual-loading lower.

## 1. Unchanged source, full causal histories, and fixed-order quantifiers

Retain the actual compact even source

\[
h=(D^2-\tfrac14)^2(q*q),\qquad
H(z)=\int_{\mathbb R}e^{-zv}h(v)dv
=(z^2-\tfrac14)^2Q(z)^2,
\]

with support in `[-S,S]`, `S=1/2048`, and q the unchanged nonnegative normalized seed. In particular `Q(1/2)>0`. Retain every prime power in

\[
Z(t)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}h(t-\log n),
\qquad
U(t)=\sum_{n\ge2}\frac{\log n}{\sqrt n}h(t-\log n).
\tag{1}
\]

Both fields vanish before `t0=log(2)-S>0`. Every field is extended by zero to negative time. Write

\[
N=\sum_{n\ge1}n^{-1/2}S_{\log n},\qquad
M=\sum_{n\ge1}\mu(n)n^{-1/2}S_{\log n}.
\]

The exact finite-history identities are `NZ=U`, `MU=Z`, and `MN=NM=I`. There is no restart at a late observation time. The original smooth completion `a*Z=c*U` is also retained.

The source argument in [DIVISOR_RESEARCH](../step4-weighted-response-2026-11-10/DIVISOR_RESEARCH.md), section 2, gives for each fixed even k>=2

\[
|U(t)|\le B_{k,h}(1+t)e^{-(k-1/2)t},\qquad t\ge0.
\tag{2}
\]

The same conclusion at every fixed derivative order follows by applying the same finite Euler--Maclaurin argument to the corresponding derivative of h. All of those sources remain compact and their transforms retain the required half-pole zeros. Consequently every exponential/polynomial moment of U exists absolutely. None of the constants below is asserted uniform as the completion order or requested decay order increases.

For `Re z>1/2`, absolutely convergent transforms give

\[
\widehat U(z)=-H(z)\zeta'(z+\tfrac12),\qquad
\widehat Z(z)=-H(z)\frac{\zeta'(z+\tfrac12)}{\zeta(z+\tfrac12)}.
\tag{3}
\]

The first transform is entire: its apparent singularity at `z=1/2` is removed by the double zero of H. This agrees with (2). The second identity is used initially only in its absolutely convergent half-plane, and then as a meromorphic identity when explicitly stated. No global L2 membership of Z is assumed.

## 2. What the complete signed moment hierarchy actually says

Define

\[
M_r=\int_0^\infty t^r e^{-t/2}U(t)dt,
\qquad \widehat U^{(r)}(1/2)=(-1)^rM_r.
\tag{4}
\]

The ordinary residue-one pole of zeta gives

\[
M_0=Q(1/2)^2>0.
\tag{5}
\]

This is the negative-weight moment, not the canceled positive-weight moment. The latter hierarchy is also explicit:

\[
\int_0^\infty e^{t/2}U(t)dt=0,
\qquad
\int_0^\infty te^{t/2}U(t)dt=0,
\]

but

\[
\boxed{\int_0^\infty t^2e^{t/2}U(t)dt
=Q(-1/2)^2\log(2\pi)>0.}
\tag{6}
\]

Indeed `H''(-1/2)=2 Q(-1/2)^2` and `zeta'(0)=-(1/2)log(2pi)`. The latter standard special value is recorded in [DLMF 25.6.11](https://dlmf.nist.gov/25.6.E11). Thus an induction which treats the full weighted moment hierarchy as vanishing is false for the actual source already at order two.

More generally, for each complex z and every r, the absolutely convergent signed moment is exactly `(-1)^r` times the r-th derivative of `-H(z)zeta'(z+1/2)`. This is stronger information than an unsigned moment bound, but it is not an assertion of vanishing at unselected points.

## 3. Exact genuine higher completions and their complete pole polynomials

Fix an integer j>=1 before any observation horizon and define

\[
V_j=N^jU=N^{j+1}Z.
\tag{7}
\]

These are actual complete arithmetic fields. If `d_k(n)` counts ordered k-tuples of positive integers with product n, finite divisor symmetry gives

\[
\boxed{V_j(t)=\frac1{j+1}
\sum_{n\ge2}\frac{d_{j+1}(n)\log n}{\sqrt n}
h(t-\log n).}
\tag{8}
\]

To check the coefficient, sum `log n_{j+1}` over all `(j+1)`-tuples with product n, and average over the `(j+1)` symmetric slots. Their summed logarithm is `log n`. No factorization, multiplicity, or prime power has been omitted.

On `Re z>1/2`,

\[
\widehat V_j(z)=-H(z)\zeta(z+\tfrac12)^j\zeta'(z+\tfrac12).
\tag{9}
\]

Put `w=z-1/2` and define analytic functions near zero

\[
B(w)=w\zeta(1+w),\quad B(0)=1,
\qquad A(w)=(1+w)^2Q(1/2+w)^2.
\]

Direct differentiation, including the minus sign in (9), gives

\[
\widehat V_j(1/2+w)=w^{-j}C_j(w),
\qquad C_j(w)=A(w)B(w)^j[B(w)-wB'(w)].
\tag{10}
\]

Let `c_{j,k}=C_j^{(k)}(0)/k!`. Define the entire causal pole profile, not just its leading term,

\[
P_j(t)=\mathbf1_{t\ge0}e^{t/2}
\sum_{\ell=1}^j c_{j,j-\ell}\frac{t^{\ell-1}}{(\ell-1)!}.
\tag{11}
\]

Its transform on `Re z>1/2` is the complete principal part of (9) at `z=1/2`. Equivalently its coefficients depend on `M_0,...,M_{j-1}` and finitely many Laurent coefficients of zeta at one. The first examples are

\[
P_1(t)=\mathbf1_{t\ge0}M_0e^{t/2},
\]

\[
P_2(t)=\mathbf1_{t\ge0}e^{t/2}
[M_0t+2\gamma_E M_0-M_1].
\tag{12}
\]

Here `gamma_E` is Euler's constant; the Laurent convention is [DLMF 25.2.4](https://dlmf.nist.gov/25.2.E4). In every fixed order,

\[
P_j(t)=e^{t/2}
\left[\frac{M_0}{(j-1)!}t^{j-1}+O_{j,h}((1+t)^{j-2})\right]
\tag{13}
\]

for j>=2, with the exact first formula for j=1. In particular the entire hierarchy of uncompensated higher completions has a genuine growing main term. Repeated completion does not preserve the cheaply bounded output class.

## 4. A stronger unconditional result after all pole terms are paid

Set

\[
R_j(t)=V_j(t)-P_j(t),\qquad t\ge0,
\]

and extend R_j by zero to negative time. For every fixed j>=1 and every fixed A>0,

\[
\boxed{|R_j(t)|\le C_{j,A,h}e^{-At}\quad(t\ge0).}
\tag{14}
\]

One explicit valid constant is

\[
C_{j,A,h}=\frac1{2\pi}\int_{\mathbb R}
|H(-A+i\xi)\zeta(1/2-A+i\xi)^j
\zeta'(1/2-A+i\xi)|d\xi.
\tag{15}
\]

The bound at a single endpoint can equivalently be defined by right continuity; point values do not affect any subsequent integral.

Proof of finiteness and contour shifting: on any fixed vertical strip, integration by parts in the compact smooth transform H gives decay faster than every fixed inverse power of `1+|Im z|`. Zeta and its derivative have at most polynomial growth on that fixed strip away from its finite pole. A direct justification uses the finite Euler--Maclaurin representation [DLMF 25.2.10](https://dlmf.nist.gov/25.2.E10), choosing its fixed order large enough for the left edge; its bounded periodic-Bernoulli integral and polynomial factors give the growth bound. Differentiation of that absolutely convergent integral on a slightly narrower strip, or Cauchy's formula on a fixed larger strip at large imaginary height, gives the corresponding derivative bound. These choices are made for the fixed j and A.

Consequently (9) is absolutely integrable on the starting line `Re z=c>1/2` and on `Re z=-A`, and its horizontal contour integrals vanish. The ordinary Laplace inversion of the genuine smooth field V_j may be shifted between these lines. The only enclosed pole is `z=1/2`, of order j, and its residue contribution is precisely (11). The remaining line integral equals R_j for `t>0` and is bounded by (15) times `exp(-At)`. Continuity from the right gives the endpoint convention in (14). This proof never divides by zeta, so it neither assumes a zero-free region nor crosses inverse poles at zeta zeros.

All causal history terms remain visible. Since V_j is zero for `0<=t<t0`,

\[
R_j(t)=-P_j(t)\qquad(0\le t<t_0).
\tag{16}
\]

In general R_j has the jump or derivative mismatch at zero required to compensate the causal pole profile. It is not a smooth function after zero extension. No integration by parts may erase this initial compensation. The statement (14) is a late-time rapid decay bound with a source-fixed constant that also pays (16), not a claim that R_j is identically small at every scale or vanishes initially.

In particular the previously proved `NU=M_0 exp(t/2)+O_h(exp(-t/2))` sharpens, on nonnegative time, to an error smaller than every fixed exponential. The older all-real-time convention used an untruncated exponential; here P_j is causal, so the exact negative-time cancellation is instead encoded by (16) and zero extension.

## 5. An independently bounded complete compensated pairing

The actual complete source has the elementary estimate `|Z(t)|<=C_Z exp(t/2)`. Choose any fixed A>1/2 in (14). Then for every horizon T,

\[
\boxed{\int_0^T|Z(t)R_j(t)|dt
\le\frac{C_ZC_{j,A,h}}{A-1/2},}
\]

\[
\boxed{\int_T^\infty|Z(t)R_j(t)|dt
\le\frac{C_ZC_{j,A,h}}{A-1/2}e^{-(A-1/2)T}.}
\tag{17}
\]

Also `||R_j||_2^2<=C_{j,A,h}^2/(2A)`. These inequalities use the full actual drive, every divisor completion, the complete pole polynomial, and the full prime field. They are not estimates for selected blocks or a free pulse class.

The exact uncompensated pairing is therefore

\[
\int_0^T Z(t)V_j(t)dt
=\sum_{\ell=1}^j\frac{c_{j,j-\ell}}{(\ell-1)!}
\int_0^T t^{\ell-1}e^{t/2}Z(t)dt
+\int_0^T Z(t)R_j(t)dt.
\tag{18}
\]

Only the final term is independently bounded by (17). Subtracting the pole terms creates a bounded compensated functional; it does not independently bound the signed prime moments which have been subtracted, or the energy of Z.

Those prime moments can be written with every boundary contribution retained. Define

\[
\Psi_r(v)=\int_{-\infty}^v w^re^{w/2}h(w)dw,
\qquad \kappa_r=\Psi_r(+\infty)=(-1)^rH^{(r)}(-1/2).
\]

Finite Fubini gives, for each integer r>=0,

\[
\boxed{\int_0^T t^re^{t/2}Z(t)dt
=\sum_{n\ge2}\Lambda(n)
\sum_{b=0}^r\binom rb(\log n)^{r-b}
\Psi_b(T-\log n).}
\tag{19}
\]

The lower endpoint is zero because `log n>=log2>S`. The upper sum is finite (`n<=exp(T+S)`), with every prime power retained. Here `kappa_0=kappa_1=0`, so these first two primitives are compactly supported and yield pure terminal collars. But `kappa_2=2Q(-1/2)^2>0`. Starting at r=2, a statement that all terms are only terminal collars is false: exact bulk Mangoldt sums occur as well. If desired write `Psi_b(v)=kappa_b 1_{v>=0}+theta_b(v)`, where theta_b is supported in `[-S,S]`; the resulting bulk sums and compact collars must both be kept. Their cancellation has not been independently estimated here.

## 6. Compatibility of the entire hierarchy with a hypothetical visible zero

This is a local calculation of the genuine meromorphic transforms, not a replacement of Z by an isolated exponential, not a claim that a zero exists, and not a dominant-zero expansion of the full field.

Suppose a zeta zero `rho=p+1/2` has multiplicity m>=1 with `0<Re p<1/2`, and retain the actual source visibility `H(p)!=0`. Locally write

\[
\zeta(z+1/2)=(z-p)^m b(z),\qquad b(p)\ne0.
\]

The complete actual drive transform then has exactly order m-1:

\[
\widehat U(z)=-mH(p)b(p)(z-p)^{m-1}
+O((z-p)^m).
\tag{20}
\]

Every genuine higher completion has exactly order `(j+1)m-1`:

\[
\boxed{\widehat V_j(z)
=-mH(p)b(p)^{j+1}(z-p)^{(j+1)m-1}
+O((z-p)^{(j+1)m}).}
\tag{21}
\]

These statements include the complete signed moment hierarchy: for example the first `(j+1)m-1` jets of `widehat V_j` vanish, but the next jet is nonzero. The prime field's recovery still obeys the exact same identity

\[
\frac{\widehat P_j(z)+\widehat R_j(z)}
{\zeta(z+1/2)^{j+1}}
=-H(z)\frac{\zeta'(z+1/2)}{\zeta(z+1/2)}.
\tag{22}
\]

The left side has the unchanged simple-pole residue `-m H(p)`, for every j. The rapidly decaying R_j has an entire transform, while the transform of P_j is meromorphic only at `1/2`. At p they compensate exactly:

\[
(\widehat P_j+\widehat R_j)^{(b)}(p)=0
\quad(0\le b<(j+1)m-1),
\]

and the next derivative is nonzero by (21). This statement does not assume that the separate P_j jet is nonzero. Inverting the two terms separately may introduce high-order poles whose cancellations must be retained; their complete sum leaves precisely the original simple pole. Rapid decay of the compensated forward output does not remove that pole.

Thus all the newly bounded compensated outputs and pairings are compatible with the existing genuine-source visible-zero lower for `A_Z`. They control different expressions, and no contrary estimate for `A_Z` or the weighted energy follows. To remove the local inverse pole through numerator divisibility would require one extra vanishing order beyond (21). On this actual visible source, the exact coefficient in (21) says that extra order cannot be supplied while retaining the hypothetical zero. Proving that no such zero exists remains the arithmetic task; it is not supplied by reapplying the known forward identity.

## 7. Derivatives and infinite families do not provide a free quantitative upgrade

Differentiating the genuine transform equation `zeta(z+1/2) widehat Z(z)=widehat U(z)` gives the exact triangular identities

\[
\sum_{b=0}^r\binom rb
\zeta^{(b)}(z+1/2)\widehat Z^{(r-b)}(z)
=\widehat U^{(r)}(z).
\tag{23}
\]

They hold in the original absolute half-plane and meromorphically elsewhere. They are the derivatives of the same equation, not additional positive estimates. Equation (20) checks all of them locally under the hypothetical zero. In time-domain uses, t-moments, source derivatives, and the causal initial corrections are distinct operations; differentiating P_j across zero introduces delta terms and must not be treated as differentiation of an untruncated exponential on the entire line.

The full signed moment sequence of U determines its entire transform. That supplies exact identification, but the reconstruction of Z still divides by the same zeta factor. Neither a finite number nor an unpriced infinite tower of the identities above supplies a lower singular value for that inverse. A horizon-dependent completion order `j=j(T)` would additionally require uniform constants in (15), all its required source derivatives and the pole polynomial; this note supplies only each fixed order. It does not infer a useful growing-order estimate from those separate statements.

For scale, even the elementary exact inverse of (7) costs exponentially after taking absolute values. The coefficients of `M^{j+1}` obey

\[
|\mu^{*(j+1)}(n)|\le d_{j+1}(n),\qquad
\sum_{n\le e^T}\frac{d_{j+1}(n)}{\sqrt n}
\le2e^{T/2}(1+T)^j.
\tag{24}
\]

To prove the last inequality, sum the last tuple coordinate using `sum_{n<=x} n^{-1/2}<=2 sqrt(x)`, then bound each of the remaining j harmonic sums by `1+T`. This is an upper budget, not an assertion that the genuine signed inverse attains it. It establishes that applying an absolute inverse bound to the rapidly decaying pieces does not by itself produce the every-positive-rate target. The exact cancellation between recovered P_j and recovered R_j cannot be discarded.

## 8. Relation to the actual-loading target and disposition

The reviewed [source-core composition](../step4-signed-correlation-round5-2026-11-11/SOURCE_CORE_FRAME_COMPOSITION.md) constructs the actual approximation `v_L` inside its source-defined finite core, with full unfiltered and filtered errors paid at `L=2T`. The [frame investigation](../step4-signed-correlation-round5-2026-11-11/FRAME_LOWER_ATTEMPT.md) shows that the normalized entire low-prime filter family is equivalent, up to `exp(o(T))`, to the single full-prefix measurement N. Its narrower sufficient target is

\[
\|Nv_L\|_{2,[0,T]}^2\ge c_{h,\gamma,\eta}e^{-\eta T}
\int_0^T e^{-\gamma(T-t)}|v_L(t)|^2dt
\tag{25}
\]

for each prescribed eta>0 at common cofinal horizons, with fixed `0<gamma<1`. The moment hierarchy does not prove (25). Its compensated expressions are affine functions of higher completed outputs, with source-fixed pole profiles. Their independent boundedness is genuine, but there is no demonstrated coercive comparison back to the actual weighted loading.

This is not a new unpriced approximation problem. The same divisor tuple bound in (24) gives the full-prefix operator estimate

\[
\|N^{j+1}f\|_{2,[0,T]}
\le2e^{T/2}(1+T)^j\|f\|_{2,[0,T]}.
\]

For the reviewed approximation `||Z-v_L||_2<=d_L<=exp(-3L/4)` with `L=2T`, it follows that

\[
\boxed{\|N^{j+1}v_L-P_j\|_{2,[0,T]}
\le\|R_j\|_2+2(1+T)^je^{-T}.}
\tag{26}
\]

Thus every fixed number of genuinely compensated higher measurements also has an independently bounded actual-core value, with its entire prefix error paid. The right side of (26) is affine data, not the norm of a homogeneous filter on arbitrary core vectors: the exact P_j offset cannot be dropped. Passing from this collection to a lower for the actual weighted loading still requires a quantified estimate, and is not supplied by small outside-core errors or finite dimension.

The valid new results are the exact complete higher divisor formula (8), all causal pole polynomials (10)--(13), the independently rapid complete compensated output (14), its bounded complete pairing (17), and the precise terminal/bulk prime-moment accounting (19). The actual-source zero-jet calculation (20)--(22) shows why all of these statements can coexist with the existing hypothetical-zero lower: each forward completion adds exactly as many zero factors as its inverse subsequently divides out, leaving the same one-order deficit.

No all-positive-rate signed response bound was obtained. **Step 4 and RH remain OPEN.** This result narrows the next useful inequality to actual weighted loading or complete signed inverse cancellation; adding more forward completions or declaring more moments canceled is not a replacement for that inequality.

### Source and validation scope

- Fixed source/divisor decay and opposite-tilt distinction: [DIVISOR_RESEARCH](../step4-weighted-response-2026-11-10/DIVISOR_RESEARCH.md).
- Actual twice-completed growing term and unpaid first terminal moment: [FILTER_FAMILY_ATTEMPT](../step4-signed-correlation-round5-2026-11-11/FILTER_FAMILY_ATTEMPT.md), section 4.
- Source-only core, physical metric, preserved affine offset and paid filter error: [SOURCE_CORE_FRAME_COMPOSITION](../step4-signed-correlation-round5-2026-11-11/SOURCE_CORE_FRAME_COMPOSITION.md) and its independent review.
- Weighted target and exact family comparison: [FRAME_LOWER_ATTEMPT](../step4-signed-correlation-round5-2026-11-11/FRAME_LOWER_ATTEMPT.md).
- Standard analytic tools were checked against the linked primary DLMF formulas. All higher-completion conclusions above are derived here for the literal project source; they are not attributed to an existing Lean declaration.

No source file, repository file, acceptance policy, or earlier frozen note was changed.
