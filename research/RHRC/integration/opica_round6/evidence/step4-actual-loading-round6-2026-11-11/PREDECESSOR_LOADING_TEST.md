# Actual predecessor loading: uniform legal approximation and a cubic crossing ceiling

11 November 2026. **DERIVED paper estimates, pending independent review. No repository edit, new Lean compilation, CI qualification, or Step 4 closure.** Baseline: [PR299](https://github.com/HMarcusWH/zeta-23-lean/pull/299), source head `b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`.

This note supplies the general-cutoff, all-translate native approximation needed by `ACTUAL_LOADING_OPICA_CONSTRAINTS.md`. It then tests it against the actual selector. The source approximation is quantitatively valid, including every boundary/pole correction and the full canonical amplification. Combined with the hypothetical visible-zero lower, it forces an **upper** bound of cubic order on the selected predecessor cutoff. It supplies no growing lower bound on that cutoff. A related two-translate argument gives a genuine conditional cubic-degree negative trial, without changing the existing production detector.

## 1. What the actual selector says

Write N=ceil(L^4) for the existing detector degree and k=K_selected-1 for its predecessor. The exact `NativeDeepThresholdGroundData` fields give

\[
3\le K_{\rm selected}\le N,\qquad 2\le k<N.
\tag{1}
\]

When K_selected=3, the two native predecessor spaces at k=2 have dimension zero. This is explicitly supported by the source theorem; it is not assigned a fictional numerical bottom. The cutoff is the first crossing of the actual global bottom below -eta in the fixed native Fourier chain. Its earlier-cutoff lower bounds concern that chain and that same eta.

In particular (1) gives no bound k>=C L^3. The two parity predecessor spaces form the physical direct sum V, and H_L+eta is positive on V. Positivity is not asserted on the containing quartic carrier. The source-only near-null-core theorem is not a statement that its selected column span lies in V.

The exact selector and its initial case are in [NativeDeepThresholdGround](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/NativeDeepThresholdGround.lean), especially the structure at lines 37--59 and the least-crossing construction at lines 75--95. The current pinned snapshots used here are preserved in `constraint-source/`.

## 2. Fourier tails uniform in every legal source translation

Retain the fixed real even source h, its support [-S,S], S=1/2048, and its two vanishing half-pole moments. For L>=2 and S<=b<=L-S put

\[
f_b(t)=h(t-b),\qquad
e_n(t)=L^{-1/2}e^{2\pi int/L},\quad
c_n=\langle e_n,f_b\rangle
=L^{-1/2}e^{-2\pi inb/L}H(2\pi in/L).
\tag{2}
\]

The translation phase has modulus one. The source Gevrey-2 bound, including any fixed derivative offset, gives fixed constants C,c>0 such that for j=0,1,2,3,

\[
\|(I-Q_k)f_b^{(j)}\|_2\le C\exp[-c\sqrt{k/L}].
\tag{3}
\]

The constants are uniform in L>=2, k>=2, and b in the legal range. To check the rate, Parseval and integration by parts m times give a bound C[A L/(2pi(k+1))]^m(m!)^2. Choose m of order sqrt(k/L) once that ratio is large enough; enlarge the fixed C to cover the remaining bounded-ratio regime. This is an upper estimate, not a two-sided asymptotic of the actual Fourier tail.

For j=0,1,2 define E_j=sum_{|n|>k}|n|^j|c_n|. Cauchy--Schwarz and the derivative tail in (3) give

\[
E_j\le\sqrt{2/k}\,(L/(2\pi))^{j+1}
\|(I-Q_k)f_b^{(j+1)}\|_2
\le C L^{j+1}\exp[-c\sqrt{k/L}].
\tag{4}
\]

These weighted tails pay the endpoint constraints. Small L2 error alone would not pay them.

## 3. Exact correction into the actual predecessor carrier

Put beta0=L^2/(16pi^2), reserving beta for the generated detector exponent. On the complete finite Fourier coefficients, native boundary flatness and both pole conditions are equivalent to

\[
\sum c_n=\sum nc_n=\sum n^2c_n=0,
\qquad
\sum\frac{c_n}{\beta_0+n^2}=0,
\quad
\sum\frac{nc_n}{\beta_0+n^2}=0.
\tag{5}
\]

The infinite coefficients of f_b satisfy (5) exactly. The first three identities are endpoint value/first/second derivative flatness. Integrating the Fourier expansion against exp(+t/2) and exp(-t/2), then adding and subtracting the resulting reciprocal factors, gives the last two. The source half-pole moments vanish at every translation b, not only at the centered packet.

The source's even and odd coefficient parts decouple these five equations. They are the actual physical parity components, not a substitute Euclidean metric. Use only modes 0, plus/minus 1, plus/minus 2; these lie inside every k>=2.

For the even part, let m0,m2 be the negatives of its current truncated moments. First add aggregated coefficients

\[
v_0=m_0-m_2,\qquad v_1=m_2,\qquad v_2=0,
\tag{6}
\]

where v0 is the coefficient at zero and v_j/2 is placed at each of plus/minus j. This fixes moments zero and two. If p_res is its remaining even pole residual, put

\[
d=(0,1,4),\quad b_*=(1/4,-1/3,1/12),
\quad D_0=\beta_0(\beta_0+1)(\beta_0+4).
\]

The exact identities

\[
\sum b_{*,j}=\sum d_jb_{*,j}=0,\qquad
\sum\frac{b_{*,j}}{\beta_0+d_j}=1/D_0
\tag{7}
\]

show that adding the aggregated vector -p_res D0 b_* fixes the even pole without disturbing its two moments. Its physical squared norm is |v0|^2+(|v1|^2+|v2|^2)/2; no paired-mode factor is omitted.

For the odd part, put w_j/2 at +j and -w_j/2 at -j. Let m1,p1 be the negatives of its current first moment and odd pole residual. The two equations and their exact solution are

\[
w_1+2w_2=m_1,\qquad
\frac{w_1}{\beta_0+1}+\frac{2w_2}{\beta_0+4}=p_1,
\]
\[
\boxed{
w_2=\frac{(\beta_0+4)m_1-(\beta_0+1)(\beta_0+4)p_1}{6},
\qquad w_1=m_1-2w_2.}
\tag{8}
\]

The odd correction does not disturb the even equations, and conversely. No fourth-moment condition is required for this predecessor construction: V is the full pole-neutral boundary-flat direct sum. This differs from the additional moment slice used in the earlier source-core input adapter.

Let q_b be the corrected degree-k profile. It belongs exactly to V. Its zero extension is H2, since its endpoint value and first derivative are zero. The pole operator annihilates f_b, q_b, and their difference. The correction is valid even when k=2 and V is zero: then q_b=0, and the large upper bound below remains true rather than becoming a claim of good approximation.

## 4. Complete quantitative cost of the correction

Equation (4) gives |m0|<=E0, |m2|<=E2. After the first even correction,

\[
|p_{\rm res}|\le C\beta_0^{-1}(E_0+E_2).
\]

Since D0/beta0=(beta0+1)(beta0+4)=O(L^4), the whole even correction costs at most C L^4(E0+E2). Similarly |m1|<=E1, |p1|<=beta0^(-1)E1, so (8) costs at most C L^2 E1. The constants are uniform because beta0 is bounded below when L>=2.

Every correction mode has frequency at most 4pi/L. Its second-derivative norm is therefore at most (4pi/L)^2 times its coefficient norm. Combining this with (3)--(4) gives the useful uniform estimate

\[
\boxed{
\|f_b-q_b\|_2+\|(f_b-q_b)''\|_2
\le C_h L^7\exp[-c_h\sqrt{k/L}].}
\tag{9}
\]

All constants and the derivative optimization belong to the fixed source, before the center, cutoff, or aperture is selected.

## 5. Pay the actual orthogonal-projection defect and its full source image

Let P_V be the physical orthogonal projection onto V, r_b=f_b-P_V f_b, and

\[
e_b=\|(H_L+\eta)r_b\|_2.
\]

Since q_b belongs to V,

\[
\|r_b\|_2\le\|f_b-q_b\|_2,
\]
\[
\|r_b''\|_2\le\|(f_b-q_b)''\|_2
+(2\pi k/L)^2\|f_b-q_b\|_2.
\tag{10}
\]

For the second inequality, q_b-P_Vf_b=P_V(q_b-f_b), so orthogonal projection gives the norm bound with factor one. The finite Fourier derivative estimate applies to this legal vector; its weak zero-extension derivatives introduce no boundary delta.

The complete source action has a fixed-source H2 archimedean estimate and the full prime-power shift bound, so

\[
e_b\le(B_0+4Le^{L/2}+\eta)\|r_b\|_2+B_2\|r_b''\|_2.
\tag{11}
\]

This does not assert a bounded L2 operator norm for the archimedean operator. Exact pole annihilation is used, instead of paying the large pole norm. The current source-only shift bound is eta<=C_eta L^7 exp(L/2); it is proved for the actual packet in [QuarticErrorReduction](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/OPICARound4/QuarticErrorReduction.lean). Also k<N<=2L^4. Hence (9)--(11) imply the deliberately coarse but uniform bound

\[
\boxed{e_b\le C L^{14}\exp\{L/2-c\sqrt{k/L}\}}
\quad(S\le b\le L-S).
\tag{12}
\]

This is a genuine source-specific upper on the selected-space defect. It remains too large when the selected k is small.

For a prescribed fixed B>0, a sufficient cutoff condition to make (12) at most exp(-B L) is

\[
c\sqrt{k/L}\ge(B+1/2)L+14\log L+\log C.
\tag{13}
\]

Thus a sufficiently large constant times L^3 suffices for each prescribed exponential accuracy. A sequence with k/L^3 tending to infinity pays every fixed exponential eventually through this bound; k=ceil(L^3 log L) is one example. Neither statement is a necessary lower bound on the actual tail. In particular failure of (13) does not prove failure of a sharper source approximation or of the desired signed estimate.

## 6. What is genuinely necessary for input approximation

There are weaker necessary statements which do not reverse a one-sided Gevrey bound. For the full Fourier space of degree k,

\[
\|Q_k f_b\|_2^2
=\frac1L\sum_{|n|\le k}|H(2\pi in/L)|^2
\le\frac{2k+1}{L}\|h\|_1^2.
\tag{14}
\]

Since V is a subspace of this Fourier space, k=o(L) forces ||P_Vf_b|| to zero, uniformly in b, while ||f_b||=||h||>0. Such a predecessor cannot approximate the source even to a vanishing unamplified error.

More generally, if k/L remains bounded along a sequence L tending to infinity, the Riemann sum in (14) has a subsequential limit equal to a finite-band integral of |H(i xi)|^2/(2pi). Its omitted tail is strictly positive: a nonzero compactly supported h cannot also be band-limited, because its entire transform cannot vanish on a real open interval. Consequently vanishing input approximation error requires k/L tending to infinity along that approximation sequence. This statement is uniform in the translation phase.

These necessary conditions are much weaker than a cubic lower bound. No matching lower asymptotic for the particular Gevrey Fourier tail is asserted here. At k=2 the exact zero-dimensional predecessor makes the failure of source approximation immediate, but the source data do not claim that this case actually occurs at arbitrarily late generated packets.

## 7. Under the hypothetical zero, the defect upper forces a cubic UPPER cutoff bound

Use the independently derived two-translate estimate in `ACTUAL_LOADING_OPICA_CONSTRAINTS.md`. Fix a source collar c0>S, let T=L-2c0, and write

\[
\mathcal E_L=2e_{c_0}
+\int_0^T e^{-(T-t)/2}e_{c_0+t}\,dt.
\]

The uniform bound (12) pays this whole family, including the stationary translate:

\[
\mathcal E_L\le4C L^{14}\exp\{L/2-c\sqrt{k/L}\}.
\tag{15}
\]

Suppose the actual source sees an off-line zero p=delta+i gamma, 0<delta<1/2 and H(p) nonzero. The complete h*h response has transform H(z)^2-zeta'/zeta, so the inherited eventual weighted-response lower remains visible. Fix a permitted generated beta with 0<beta<delta *before* choosing packets. The two-translate result, using eta<exp(beta L)/2, forces on all sufficiently late such packets

\[
\mathcal E_L\ge c_{\rho,h}e^{\delta(L-2c_0)}.
\tag{16}
\]

Combining the lower with (15), without any pointwise single-zero-dominance assertion, gives

\[
\boxed{c\sqrt{k/L}\le(1/2-\delta)L+14\log L+C_{\rho,h,c_0},}
\]
\[
\boxed{k\le\frac{L}{c^2}
\left[(1/2-\delta)L+14\log L+C_{\rho,h,c_0}\right]^2
=O_{h,\rho}(L^3).}
\tag{17}
\]

The bracket is positive at late L because delta<1/2. If an inherited version of the response lower retains a fixed polynomial loss, its logarithm only changes the coefficient of log L, not the cubic conclusion. The exact route currently used supplies the stronger lower (16).

The horizon here is L-2c0, not the earlier centered-column convention L/2. If only that shorter horizon were used, the coefficient 1/2-delta in (17) would instead be 1/2-delta/2. The present all-translate bound legitimately uses the longer horizon.

This is a conditional **upper** restriction on the actual first crossing. Requiring the selected predecessor to grow much faster than cubic would conflict with the hypothetical detector configuration, rather than follow from it. Equation (17) neither supplies the lower cutoff needed by (13) nor contradicts the selector's existing upper bound k<N.

## 8. A genuine conditional cubic-degree detector

The same ingredients give a direct positive research result. Fix a source-only constant C_star so large that c sqrt(C_star)>1/2 in (9), and put

\[
J_L=\lceil C_{\rm star}L^3\rceil.
\tag{18}
\]

For all sufficiently large L, J_L<=ceil(L^4). Under the same visible zero, the weighted-response lower and integral_0^T exp(-(T-t)/2)dt<2 give a time t in [0,T] with

\[
|Z_{h*h}(t)|\ge\tfrac12c_{\rho,h}e^{\delta T}.
\tag{19}
\]

This is an existence deduction from the *complete* response, not a claim that one zero dominates it. Since this response vanishes for t<log(2)-2S and log(2)-2S>2S, the two translates f_{c0+t} and f_{c0} have disjoint supports. Their norms are both n_h=||h||_2, their canonical selfworks equal the fixed s_h=-<h,Ah>, and their full canonical crosswork satisfies

\[
\langle f_{c_0+t},H_Lf_{c_0}\rangle
=-Z_{h*h}(t)-\langle f_{c_0+t},Af_{c_0}\rangle,
\qquad |\langle f_{c_0+t},Af_{c_0}\rangle|\le n_h C_{A,h}.
\tag{20}
\]

All quantities are real for this real source. Choose the sign of the sum of the two translates to make its crosswork negative. The resulting vector v has norm squared 2n_h^2 and

\[
\frac{\langle v,H_Lv\rangle}{\|v\|^2}
=\frac{s_h-|\langle f_{c_0+t},H_Lf_{c_0}\rangle|}{n_h^2}
\le-c'_{\rho,h}e^{\delta T}
\tag{21}
\]

at every sufficiently late aperture.

Approximate both translates by their degree-J_L corrected native profiles from (9), and use the same sign to form q. Their combined H2 error is at most

\[
C L^7e^{-c\sqrt{J_L/L}}.
\]

The entire canonical quadratic error is bounded by a fixed polynomial in L times exp(L/2-c sqrt(J_L/L)). To see this directly, expand <q,Hq>-<v,Hv> with q=v+e, use the uniform fixed-source bound ||H v||<=C(1+L exp(L/2)), the complete H2 estimate for H e, and exact pole annihilation of v and q. Both linear error terms and the quadratic error term are retained. By the choice of C_star this error tends to zero exponentially. Also ||q|| tends to sqrt(2)n_h, so normalizing q is legitimate and preserves (21), after changing its fixed constant.

The exact physical canonical matrix correspondence therefore gives a legal, both-pole-neutral unit trial of degree J_L with negative Rayleigh depth at least c''_{rho,h} exp(delta T). At that degree at least one parity component has no greater Rayleigh quotient, because the two parity spaces are orthogonal and the form preserves reflection. This supplies an actual conditional cubic-degree detector at paper level.

For any fixed beta<delta, this depth eventually exceeds exp(beta L). In the existing selection with that beta and its own eta<exp(beta L)/2, the global bottom at J_L is below -eta. The first crossing in the same native chain must therefore occur no later than J_L. This independently confirms a cubic crossing ceiling.

This is **not** a replacement of the stored production quartic detector, its phase choices, or its generated packet data. It constructs an additional trial for a mathematical comparison. No fresh compiled theorem or modified CI recipe is claimed. It gives no positivity of the cubic carrier or of an enlarged predecessor.

## 9. Source-core containment and reordering are still unproved

The historical mixed near-null theorem permits applying its approximation statement to an arbitrary *already specified legal subspace*. It does not permit replacing the selector's predecessor by that subspace while keeping the existing positivity theorem. Nor does the source-column rank estimate identify the selected column span with a low-frequency band, or with the image of P_V. An upper rank bound is not a containment or loading bound.

Reordering a carrier to include the desired source translates first would require proving positivity of their complete mixed Gram form at the proposed starting stage. Their individual selfworks are bounded, but their crossworks are exactly the signed response in (20). Assuming positivity of that starting span would therefore assume the substantive estimate that the present route is trying to prove.

The current [CommonQuarticGround](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/OPICARound4/CommonQuarticGround.lean) synchronizes negative trials and ground constraints at the prescribed quartic cutoff while preserving the selected cutoff separately. It does not furnish predecessor positivity after adjoining a source core. The source-only norm and shift bounds read in the pinned modules give upper envelopes of order polynomial(L) exp(L/2). When beta<1/2, comparing a detector depth exp(beta L) with those envelopes gives no growing lower bound on k. No stronger source-specific lower-cutoff supplier was found in the inspected selector, inverse-budget, common-ground, or quartic-error statements.

## Disposition

**DERIVED:** the exact five-constraint correction for all source translates, the uniform general-cutoff H2 error (9), the fully amplified selected-projection defect bound (12), and, under a hypothetical visible zero and its inherited eventual response lower, the cubic selected-cutoff ceiling (17) and a source-fixed cubic-degree negative trial (18)--(21).

**OPEN:** an independent closing-rate upper for the actual defect family, or a different actual-loading restriction. The Gevrey estimate is sufficient at large cutoff; the selector and the new zero-dependent argument do not force such a large positive predecessor. They instead permit, and under the hypothetical zero constrain, an earlier crossing. No contradiction or Step 4 closure has been obtained.

### Input references

- `ACTUAL_LOADING_OPICA_CONSTRAINTS.md`: exact two-translate estimate, physical predecessor, all source defects, and T=L-2c0 horizon.
- `../step4-weighted-response-2026-11-10/INPUT_MOMENT_CORRECTION.md`: current physical coefficient convention and the earlier centered four-node correction. This note supplies a different five-constraint correction for general translates into the full predecessor.
- `../step4-weighted-response-2026-11-10/CANONICAL_COLUMN_EXTENSION.md`: complete canonical physical operator, source-fixed archimedean H2 bound, exact pole annihilation, and complete prime-shift norm.
- `../step4-signed-correlation-round5-2026-11-11/SOURCE_CORE_FRAME_COMPOSITION.md` and its source proof copies: the precise paper-level near-null/source-column scope and actual-loading distinction.
- [NativeDeepThresholdInverseBudgets](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/NativeDeepThresholdInverseBudgets.lean): actual shifted predecessor coercivity, with the empty case retained.
- [UniversalSincPhysicalBounds](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/UniversalSincPhysicalBounds.lean): fixed-source Gevrey inputs, previously fetched at the current pin.

No repository, protected source, compiler pin, detector cutoff, or acceptance policy was edited.
