# Actual-source loading through the generated positive predecessor

11 November 2026. **DERIVED paper result and bounded closure attempt. No new Lean compilation, CI qualification, repository change, or Step 4 closure.** Current source pin: `b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`. The relevant current Lean sources were fetched at this pin and preserved in `constraint-source/` beside this note.

The useful new deduction is an upper bound for the **complete arithmetic response with kernel h*h**, from the actual generated predecessor's proved positivity. It does not identify our packet with a selected eigenray. Its entire unpaid term is the actual response of the translates' selected-predecessor projection defects. The quartic source approximation does not pay those smaller-cutoff defects.

## 1. The positive space and the sharper generated shift

Fix an actual generated packet under a hypothetical off-line zero, with permitted exponent beta>0, aperture L, detector degree N=ceil(L^4), selected cutoff k+1, and D=exp(beta L). The retained state's exact fields give

\[
  D/3<\eta<D/2,\qquad 2\le k<N.
\tag{1}
\]

The last strict inequality follows from selected cutoff <=N. In particular the sharper eta upper in (1), not just the universal exp(L/2) envelope used to transport errors, is available for this packet.

Let V_e and V_o be its actual pole-neutral even and odd predecessor spaces, both at cutoff k, realized isometrically as physical functions on [0,L]. Put V=V_e direct-sum V_o and let P be the physical L2 orthogonal projection onto V. The canonical physical form commutes with reflection t -> L-t: its pole kernel, full prime-power shifts, and archimedean kernel all have this symmetry. The even/odd mixed form therefore vanishes. The two source theorems `nativeDeepThreshold_even_detector_coercive` and `nativeDeepThreshold_odd_detector_coercive` combine to give

\[
 \langle v,(H_L+\eta)v\rangle\ge g\|v\|^2\ge0
 \quad(v\in V),\qquad g=\mathrm{nativeDeepThresholdGap}(D,N)>0.
\tag{2}
\]

Inner products are antilinear in the first argument. The form in (2) is real. No positivity is asserted on the whole quartic carrier or continuum domain. If the selected cutoff is 3, k=2 and both actual predecessor spaces are zero-dimensional; P=0 and (2) still holds, without assigning a Rayleigh bottom to an empty space.

The current `CommonQuarticGround.lean` does already synchronize joint ground constraints and both negative moment-slice trials at the quartic detector cutoff. Thus the older absence of a common quartic aperture is not the present obstruction. Its theorem explicitly retains the selected cutoff separately.

## 2. Physical translates of the unchanged source

Retain the exact real even compact source h from the weighted-response route, with support [-S,S], 2S<log 2, both half-pole moments zero, and h smooth. Write

\[
 n_h=\|h\|_2>0,\qquad f_b(t)=h(t-b),
 \qquad S\le b\le L-S.
\]

Every f_b lies in the physical interval, has the two exact pole moments zero, and its zero extension is H2. Let A be the full direct-equation-(4.4) archimedean operator already identified in `CANONICAL_COLUMN_EXTENSION.md`, with

\[
 \|Af\|_2\le B_0\|f\|_2+B_2\|f''\|_2,
 \qquad C_{A,h}=B_0n_h+B_2\|h''\|_2.
\tag{3}
\]

All translated selfworks are exactly the same real number:

\[
 \langle f_b,H_Lf_b\rangle=s_h:=-\langle h,Ah\rangle.
\tag{4}
\]

The pole channel is zero, and the full prime selfwork is zero because each prime-power translation is at least log 2, larger than the support diameter 2S. This is an exact complete-source identity, not an assumed positive sign for s_h.

Define the genuine selected-predecessor defects

\[
 p_b=Pf_b,\quad r_b=f_b-p_b,\quad
 e_b=\|(H_L+\eta)r_b\|_{L^2[0,L]}.
\tag{5}
\]

These are actual physical objects. Projection is onto both parity predecessors, not just the parity of the generated detector. Explicitly f_b^+=(f_b+f_{L-b})/2 and f_b^-=(f_b-f_{L-b})/2 are its parity components; P applies the corresponding actual orthogonal projection to each. The source itself need not be a ground vector or reciprocal input.

Both p_b and r_b retain the two pole conditions. Native boundary-flat synthesis has zero value and first derivative at the endpoints; hence p_b and r_b also have H2 zero extensions. The complete source operator and all pairings below are therefore defined. There is no omitted endpoint delta.

## 3. A complete-source cross-response upper with every defect retained

Write B=H_L+eta on this domain. Self-adjointness and ||p_b||<=n_h give

\[
 |\langle f_b,Bf_b\rangle-\langle p_b,Bp_b\rangle|
 \le 2n_he_b.
\tag{6}
\]

For example, expand the difference as <r_b,Bf_b>+<p_b,Br_b>, move B across in the first term, and apply Cauchy--Schwarz. This avoids an upper bound on the unknown full source column Bf_b.

Similarly, for any b,c in the legal range,

\[
 |\langle f_b,Bf_c\rangle-\langle p_b,Bp_c\rangle|
 \le n_h(e_b+e_c).
\tag{7}
\]

Apply Cauchy--Schwarz to the positive form (2). With C_eta=|s_h|+eta n_h^2>=0, (4)--(7) imply

\[
\begin{aligned}
 |\langle p_b,Bp_c\rangle|
 &\le\sqrt{(C_\eta+2n_he_b)(C_\eta+2n_he_c)}\\
 &\le C_\eta+n_h(e_b+e_c),\\
 |\langle f_b,Bf_c\rangle|
 &\le |s_h|+\eta n_h^2+2n_h(e_b+e_c).
\end{aligned}
\tag{8}
\]

The square-root estimate uses the arithmetic/geometric mean inequality. It does not require either diagonal to have been bounded below by s_h.

Let h_2=h*h and retain the **full** Mangoldt response

\[
 Z_2(t)=\sum_{n\ge2}{\Lambda(n)\over\sqrt n}\,h_2(t-\log n).
\tag{9}
\]

For b=c+t, t>=0, the exact canonical prime pairing is

\[
 \langle f_b,P_Lf_c\rangle=Z_2(t).
\tag{10}
\]

Indeed the two shifts contribute h_2(t-log n) and h_2(t+log n). The latter is identically zero because t+log n>=log 2>2S. The former retains every prime power, including pulses clipped by the moving arithmetic cutoff; there is no cutoff approximation in (9)--(10). The pairing is taken against two complete source profiles inside the physical interval, so restricting the output to that interval discards nothing from this pairing.

Since the pole pairing vanishes and |<f_b,A f_c>|<=n_h C_{A,h}, equation (8) yields the new actual-source estimate

\[
\boxed{
 |Z_2(t)|\le C_h+\eta n_h^2
       +\eta\,|\langle f_{c+t},f_c\rangle|
       +2n_h(e_{c+t}+e_c),
}\qquad C_h=|s_h|+n_hC_{A,h}.
\tag{11}
\]

For t>2S the overlap term is exactly zero. It is retained for smaller separations; it is at most eta n_h^2, and in fact Z_2(t)=0 on 0<=t<log 2-2S. Neither small-separation compensation nor the signed arch term was dropped.

Equation (11) is a consequence of the actual generated positive predecessor and genuine compact-source selfwork. It is stronger than simply applying the full exp(L/2) operator bound when its exact selected-space defects are small.

## 4. A zero-dependent closing-rate supplier, precisely stated

Choose a source-fixed collar c0>S, for example c0=1, and put

\[
 T=L-2c_0,\qquad
 \mathcal E_L=2e_{c_0}+
    \int_0^T e^{-(T-t)/2}e_{c_0+t}\,dt.
\tag{12}
\]

Both sources remain fully inside [0,L], including at t=T. The finite-rank projection depends continuously on b, so the integral is defined. Integrating (11), and retaining the overlap by its upper bound, gives

\[
\boxed{
 A_{Z_2}(T):=\int_0^T e^{-(T-t)/2}|Z_2(t)|dt
 \le 2C_h+4\eta n_h^2+2n_h\mathcal E_L.
}
\tag{13}
\]

Here T=L-2c0, **not** L/2. We have directly measured separations of two translates across the full aperture; this does not change the earlier centered-column map's convention T=L/2. At the present horizon, the exact eta upper gives

\[
 4\eta n_h^2<2n_h^2e^{2\beta c_0}e^{\beta T}.
\tag{14}
\]

For an actual visible off-line zero p=delta+i gamma, H(p)!=0, convolution preserves visibility: the transform of h_2 is H(z)^2. All pulses of Z_2 begin after log 2-2S>0, so the same finite-history Laplace/zero-jet derivation applies without a new initial-history term. In its initial convergence half-plane the exact transform is

\[
 \mathcal LZ_2(z)=H(z)^2-\zeta'/\zeta.
\tag{15}
\]

Thus the already used centered-moment argument, applied to this unchanged complete arithmetic field with the fixed doubled source kernel, gives an eventual lower A_{Z_2}(T)>=c_rho exp(delta T). This is a paper application to h*h, not a new compiled theorem. It retains the actual zero's multiplicity and the complete other-zero contribution; it is not a single-mode dominance argument. The upstream source-visibility qualification is unchanged.

Consequently a sufficient new supplier under the hypothetical zero is:

* choose 0<beta<nu<delta first;
* obtain its actual generated packet cofinally late, retaining its own predecessor and eta;
* establish independently on cofinally many of those same packets

\[
 \boxed{\mathcal E_L\le C_{\rho,h,\beta,\nu}e^{\nu(L-2c_0)}.}
\tag{16: OPEN}
\]

Then (13)--(15) would contradict the eventual lower at those same horizons. An unconditional every-positive-rate upper is unnecessary for this route. Conversely, if the hypothetical visible zero exists, (13)--(15) force, for every beta<delta and all sufficiently late packets,

\[
 \mathcal E_L\ge c'_{\rho,h}e^{\delta(L-2c_0)}.
\tag{17}
\]

This is an actual-source restriction on its selected-predecessor complement, derived without an assumed eigenray identity. It is not an upper, and it is not yet a contradiction.

## 5. What pays a selected-space defect, and what has not been paid

The exact pole cancellation and the complete prime-operator bound give the independent sufficient estimate

\[
 e_b\le(B_0+4Le^{L/2}+\eta)\|r_b\|_2+B_2\|r_b''\|_2.
\tag{18}
\]

No full-L2 operator norm for the arch operator was assumed: its H2 estimate (3) is used explicitly. If q_b is any actual legal predecessor approximant to f_b, its Fourier degree is at most k and the L2-best-projection property yields

\[
\begin{aligned}
 \|r_b\|_2&\le\|f_b-q_b\|_2,\\
 \|r_b''\|_2
 &\le\|(f_b-q_b)''\|_2
   +(2\pi k/L)^2\|q_b-Pf_b\|_2\\
 &\le\|(f_b-q_b)''\|_2
   +2(2\pi k/L)^2\|f_b-q_b\|_2.
\end{aligned}
\tag{19}
\]

The last factor 2 is a safe triangle bound; the sharper orthogonal-projection bound is also available. The Fourier second-derivative estimate is for the difference of two legal native vectors, whose H2 zero extension has no endpoint distribution.

The existing quartic construction supplies extremely accurate approximants at N=ceil(L^4). Equations (18)--(19) instead require approximants in the **selected predecessor** k. Substituting the quartic approximant in (19) is invalid unless it belongs to that predecessor.

For scale orientation only: a certified uniform Gevrey-2 approximation of size poly(L,k) exp[-c sqrt(k/L)] in both required norms would make (18) small enough once k exceeds a sufficiently large constant times L^3. The constant must pay exp(L/2), the requested exponent nu, and every polynomial/correction factor. This sentence is conditional on an actual legal predecessor approximation; it is not a newly proved general-cutoff interpolation theorem or a claim that arbitrary L2 Fourier truncation is pole-neutral.

The inherited selector gives only 3<=k+1<=N, predecessor ground lower bounds, and an actual selected eigenvalue below -eta-g. It **does not supply k>=C L^3**, or even a growing lower bound on k. The cutoff-3 case is explicitly supported in the proved source. The necessary inequality D<=||H at selected cutoff||, combined with the existing exp(L/2) source norm envelope, does not force a growing cutoff when beta<1/2: a fixed-degree polynomial factor times exp(L/2) already exceeds exp(beta L) eventually. This is a limitation of the available bound, not an assertion that an actual bounded-cutoff crossing occurs.

The carrier cannot be chosen afterward to include the A11 source core or a desired list of translates. In the current `NativeDeepThresholdGround.lean`, lines 75--80 define `Cross K` using the actual global bottom at the fixed native Fourier cutoff K and choose `Nat.find hex`; lines 88--95 prove positivity only at earlier cutoffs in that same chain. The structure at lines 37--59 accepts no arbitrary-subspace/carrier-order parameter. At fixed L and D, changing the chosen separator eta within its allowed interval still supplies no such parameter or containment theorem. Extending V by the source core would need a fresh positivity proof for all the resulting mixed pairings, which is precisely information not supplied by the rank estimate. `CommonQuarticGround.lean` lines 478--506 joins negative trials and ground constraints at N while preserving the stored selected cutoff; lines 748--827 put those trials in moment slices but assert no positivity of the containing quartic slice.

I searched the native threshold, ground, detector and first-crossing modules for an inherited cutoff-growth supplier. The pertinent stored fields and proofs give nonemptiness and the upper cutoff comparison only. `CanonicalGroundPropagation.lean` defines the fixed-cell/global propagation propositions; it does not prove them. The source-only A11 near-null rank bound is also not a Fourier cutoff-growth theorem: its source-selected column span need not be contained in V. No rank-to-frequency substitution is valid here.

Thus the first new unpaid inequality is (16), with (18)--(19) an explicit possible way of proving it. The absence of a lower bound on k is a precise obstruction to paying it by the currently proved source approximation, rather than a reason to drop the complement.

## 6. The same unpaid loading in the actual Schur block

There is a complementary finite-dimensional calculation for the actual fixed source packet phi_N in the full detector carrier. Choose one parity, its actual predecessor embedding J and complement Q, and write the shifted detector operator in physical block coordinates as

\[
 B=H_N+\eta=
 \begin{pmatrix} A&C\\ C^*&D_0\end{pmatrix},
 \quad A>0,\quad S_\eta=D_0-C^*A^{-1}C,
 \quad\phi_N=Jx+y.
\]

Set f=Ax+Cy and u=x+A^{-1}Cy. Exact square completion gives

\[
 \boxed{\|A^{-1/2}f\|^2
 =\langle\phi_N,H_N\phi_N\rangle
   +\eta\|\phi_N\|^2-\langle y,S_\eta y\rangle.}
\tag{20}
\]

The first selfwork is the fixed source value plus its already paid quartic error. Eta has the favorable beta rate. The remaining term -<y,S_eta y> is the Schur loading of **this** source packet. The generated detector's `smoothSourceMain` and selected ground identities are about their own stored vectors; they do not supply this scalar for phi_N. Even paying (20) would leave the full complement output

\[
 QH_N\phi_N=C^*u+(S_\eta-\eta)y,
\tag{21}
\]

including its mixed terms. The two-translate estimate (13) packages the needed full response defects directly, so it does not silently use (20) as an upper for the complete column.

## 7. Why summing genuine eigenray constraints does not remove this term

General resolvents are legitimate; eigenray identification by analogy is not. At a fixed native cutoff let E,O be the full pole-neutral parity compressions, I the actual invertible index map, b the cubic compression vector, and S the corrected source row. Retain the proved displacement

\[
 OI-IE=bS.
\]

Put c=I^{-1}b. For z outside both spectra, with R_E(z)=(E-z)^{-1}, the exact rank-one resolvent identity is

\[
 R_O(z)I\phi
 =IR_E(z)\phi-
   IR_E(z)c\,{S R_E(z)\phi\over 1+S R_E(z)c}.
\tag{22}
\]

It follows by inverting I^{-1}(O-z)I=E-z+cS. The denominator also equals det(O-z)/det(E-z), with all multiplicities retained. Shared eigenvalues require the full limiting kernel/complement decomposition; (22) is not divided through a shared pole.

The special strict-odd reciprocal input is R_E(lambda_o)c, where its source normalization equals -1. Our actual phi is not that vector. Applying (22) to phi introduces the loaded numerator S R_E(z)phi and the same full spectral denominator. The input moment m(phi)=0 does not imply m(R_E(z)phi)=0 or bound S R_E(z)phi. Expanding in an orthonormal eigenbasis legitimately retains all actual loadings and phases but supplies no new upper for this numerator. The round4 native-output-moment audit identifies its leading output moments as complete clipped Mangoldt functionals, not vanished input moments.

This is the exact place where the general-resolvent attempt needs new arithmetic control. The strict-even, strict-odd and tied ground statements remain applicable to their actual rays; their normalization and ground-specific sign cannot be assigned termwise to an arbitrary source spectral decomposition.

## Disposition

**DERIVED:** (11)--(13), a complete-source translated-response bound from the actual generated positive predecessor, with all source/prime-power/collar/overlap contributions and all selected-complement defects explicit. The favorable exact eta rate is used. Under a hypothetical visible zero, (17) is a genuine necessary lower for that actual defect family.

**OPEN:** an independent cofinal upper (16), or an actual selected-cutoff/approximation theorem strong enough to imply it. The current quartic approximation, joint ground constraints, near-null rank and general resolvent identities do not establish this supplier. No coercivity of the full canonical form, no subexponential inverse budget, and no eigenray substitution was assumed. Step 4 remains open.

### Exact source links and scope

- [NativeDeepThresholdGround](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/NativeDeepThresholdGround.lean): exact eta interval, selected/earlier cutoffs, separate actual ground eigenvalue, explicit empty predecessor.
- [NativeDeepThresholdInverseBudgets](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/NativeDeepThresholdInverseBudgets.lean): both actual detector-shift predecessor coercivity theorems.
- [Step123OutputData](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/Step123OutputData.lean): retained state has D=exp(beta L), unchanged original detector and selected state.
- [CommonQuarticGround](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/OPICARound4/CommonQuarticGround.lean): current common-quartic synchronization, with the selected cutoff retained separately.
- [JointGroundConstraints](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/OPICARound4/JointGroundConstraints.lean): exact normalized even ray, distinct odd reciprocal input, and complete tied kernels/complements.
- [SchurErrorTransport](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/OPICARound4/SchurErrorTransport.lean) and [QuarticErrorReduction](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/OPICARound4/QuarticErrorReduction.lean): full detector-specific smooth expression and all transport costs; lower bounds, not the missing arithmetic upper.
- [CanonicalGroundPropagation](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/CanonicalGroundPropagation.lean): propagation is defined as an open proposition, not provided as a theorem.

The complete canonical physical extension, its fixed-source H2 bound and exact prime pairing are paper constructions already recorded in the round1/round3 notes. The new estimate uses those constructions at that same DERIVED scope. Reading a current Lean declaration here verifies its statement and hypotheses; no new compiler evidence is claimed.
