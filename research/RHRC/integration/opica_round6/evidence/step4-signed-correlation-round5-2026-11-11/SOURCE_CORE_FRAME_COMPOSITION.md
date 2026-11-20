# From the source-only near-null core to a finite rough-response frame

11 November 2026. **DERIVED paper composition, pending review. No Lean compilation, CI qualification, repository edit, coercive arithmetic bound, or Step 4 closure.** The exact source baseline remains PR299 `b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`.

The new result is a justified finite-dimensional reduction of the full rough-family problem, with outside-core amplification paid. It requires an explicit affine reconstruction built below; the earlier norm inequality is not silently treated as a linear inverse. The remaining inequality is an explicit source-defined finite frame bound, stronger than necessary if required on the whole core.

## 1. An actual linear reconstruction modulo the pole

Retain all definitions and constants of `OUTPUT_RECOVERY.md`: T=L/2, K=ceil(L^4), m=ceil(L/log L), epsilon=beta/K^2, the actual native slice S, and the actual measured vector

\[
z_g=\Pi_SQ_Kg_L.
\]

That note proves, on the measured high band and the whole Fourier tail,

\[
c_n=p(x_n)+R_n,\quad x_n=(K/n)^2,\quad
\|(R_n)_{|n|\ge\lceil K/2\rceil}\|_2\le\rho_L,
\quad\rho_L=\exp((-3/2+o(1))L).
\]

Its retained coefficients have the exact decomposition

\[
(Q_Kg)_n=(z_g)_n+\alpha_0+\alpha_1n^2+\alpha_2n^4
\quad+c/(\beta+n^2).
\]

The following gives a linear map D_L on every vector z in S; its reconstruction error is asserted only for the actual z_g.

1. At the fixed degree-(m+3) high-band sample nodes of the recovery proof, interpolate the values x^2(1+epsilon x)z_n by a polynomial q_z.
2. Read its first three coefficients and solve the same triangular equations q_0=-a_2, q_1=-a_1-epsilon a_2, q_2=-a_0-epsilon a_1. Put N_z(n)=a_0+a_1 n^2/K^2+a_2 n^4/K^4 and W_z(n)=z_n+N_z(n), |n|<=K.
3. At fixed degree-m high-band sample nodes, interpolate the values (1+epsilon x)W_z(n)/x by a degree-m polynomial t_z(x). Put s_z(x)=x t_z(x). This enforces s_z(0)=0 exactly.
4. Define D_L z by Fourier coefficients W_z(n) for |n|<=K and s_z(x_n)/(1+epsilon x_n) for |n|>K, with both frequency signs retained.

All these operations are linear and use observed coordinates only. The tail is square summable since s_z(0)=0. No derivative values of a hypothetical core output are requested.

To verify the bounds, put B_L=1+480 sqrt(2K+1)16^(m+3). The first interpolation gives ||W_z||<=B_L||z||. For actual z_g, it differs from the retained coefficients of w_L=g_L-bv_L by at most (B_L-1)rho_L. The second interpolation gives coefficient error at most 5*16^m B_L rho_L for s_z-s. The tail estimate sum_{|n|>K}(K/n)^4<=2K/3 then proves

\[
\boxed{\|D_L\|\le F_L,\qquad
\|D_Lz_g-(g_L-bv_L)\|_2\le F_L\rho_L,}
\tag{1}
\]

using the already larger constant F_L=C_L(B_L+1) from the recovery note. In particular log(F_L)=o(L). The omitted Fourier remainder is included in (1). Interpolating s/x, rather than s with an uncontrolled constant term, is essential for the infinite tail.

## 2. An affine whole-field reconstruction using the genuine completion

Write v(t)=cosh(t/2) on [0,T], A_Tf=a*f restricted to that prefix, and kappa=2/9. The previously proved literal pole estimate is

\[
\|A_Tv\|_2\ge(\kappa/\sqrt2)\|v\|_2,
\quad \|A_T\|\le2.
\]

Use the inner product antilinear in its first slot. Define the actual bounded linear operator

\[
\mathcal T_T f=f-v\frac{\langle A_Tv,A_Tf\rangle}{\|A_Tv\|^2},
\qquad \|\mathcal T_T\|\le C_a:=1+2\sqrt2/\kappa.
\]

If Z=dv+r and A_TZ=W on the prefix, then exactly

\[
Z=\mathcal T_T r+v\frac{\langle A_Tv,W\rangle}{\|A_Tv\|^2}.
\]

The genuine column identity supplies r=-(g_L-bv_L)(T+.)-Ah. Therefore set

\[
\mathcal R_L z=-\mathcal T_T[(D_Lz)(T+.)],
\]
\[
\eta_T=-\mathcal T_T(Ah)
\quad+v\frac{\langle A_Tv,W\rangle}{\|A_Tv\|^2}.
\]

These are source-defined. The offset eta_T may depend on the horizon but has the fixed bound

\[
\|\mathcal R_L\|\le G_L:=C_aF_L,
\qquad\|\eta_T\|_2\le C_aC_{\rm arch,h}
\quad+(\sqrt2/\kappa)\|W\|_2.
\]

Let m_L=M_L phi_L be the actual native column. The previous input adapter gives ||z_g-m_L||<=epsilon_L. Combining these exact maps and (1) proves

\[
\boxed{Z=\mathcal R_Lm_L+\eta_T+e_L,
\qquad\|e_L\|_2\le G_L(\rho_L+\epsilon_L).}
\tag{2}
\]

The equation is an approximation only for the genuine source. Although the explicitly constructed map R_L is defined on arbitrary core vectors, no such vector is declared an actual arithmetic field or a solution of the completion equation. The use of W is retained in eta_T, not discarded as a small output after inversion.

## 3. The inherited near-null estimate pays the full output complement

The operator-identification requirement is explicit. Let H be the literal self-adjoint finite physical canonical operator to which the inherited near-null theorem applies. Let J embed the actual native slice isometrically in that carrier, with

\[
M_L=J^*HJ.
\tag{3}
\]

This identity is available for the present physical objects. At the pinned b3afa611 source, `CanonicalPoleNeutralGeometry.lean:192` defines `poleNeutralEvenCompressedCanonical` by the inherited orthogonal projection of `evenCompressedCanonical`. `MomentSlices.lean:49` defines `evenMomentSlice` as the fourth-moment kernel inside that pole-neutral carrier. The subtype inclusion J is an isometry for the inherited physical Euclidean norm (`CanonicalPoleNeutralGeometry.lean:61`). Consequently, taking H to be this pole-neutral compression gives M_L=J*HJ by nested orthogonal compression. Equivalently one may apply the inherited theorem directly to the moment slice and take H=M_L, J=I. No preservation of the slice by P is assumed, and no raw coordinate matrix is substituted for H.

The exact historical `NEAR_NULL_CORE_THEOREM.md` (archived SHA256 `946514e752ef474963c25b8c95957ffc220520db17b9567547939cd53abc2932`) states its mixed operator estimate for **any** linear subspace U of the legal degree-K boundary-flat carrier. Both choices above meet that scope. Its mixed Weil and physical-norm identification is supplied by `canonicalPhysicalSynthesis_mixed_Weil`, `canonicalNativePhysicalSynthesis_mixed_Weil`, and `canonicalPhysicalValue_norm`. These bridges, and the central zero-count file `RvM/LocalCount.lean`, were freshly read at b3afa611 and their entire returned text compared equal to the historically inspected 9c517db0 versions. The four current snapshots are retained in `source-core/`. This verifies source identity, not a new compilation of the paper near-null proof.

Suppose its source-only orthogonal projection P satisfies

\[
\operatorname{rank}P\le q,\qquad\|H(I-P)\|\le\delta.
\]

Self-adjointness gives ||(I-P)H||<=delta. Let C_L=range(J*P) and let R be its physical orthogonal projector. Then dim(C_L)<=q and

\[
\boxed{\|(I-R)m_L\|
=\|(I-R)J^*(I-P)HJ\phi_L\|
\le\delta\|\phi_L\|.}
\tag{4}
\]

The equality uses (I-R)J*P=0. This output-only compression needs no factor two and no commutation hypothesis.

Define a source-only function space on the complete response prefix by

\[
\mathcal K_L=\mathcal R_L(C_L)+\operatorname{span}\{\eta_T\},
\qquad \dim\mathcal K_L\le q+1.
\tag{5}
\]

The known affine offset is included as an extra direction. Dropping it before applying a rough filter would be invalid because that filter can amplify a merely bounded input.

The actual vector v_L=R_L(Rm_L)+eta_T belongs to K_L and satisfies

\[
\boxed{\|Z-v_L\|_{2,[0,T]}\le d_L,
\qquad d_L:=G_L(\delta\|\phi_L\|+\rho_L+\epsilon_L).}
\tag{6}
\]

The actual packet norm is source-fixed up to its already paid approximation. Choosing delta=exp(-L) adds only O(L) to the inherited q=O(L^3 log L+L+log^+(1/delta)) estimate. Thus q remains O(L^3 log L). Since G_L=exp(o(L)), rho_L=exp((-3/2+o(1))L) and epsilon_L decays faster than every fixed exponential, eventually

\[
d_L\le e^{-3L/4}.
\tag{7}
\]

The arbitrary tolerance is supported by a written estimate, not extrapolation from the finite L5 certificate. In the historical proof, put Omega=2pi K/L, Theta=D Omega for fixed D>1, and B_tail=8 C_N L exp(L/2) Theta log(Theta+3). Its mixed residual is at most B_tail D^(-r). If the physical carrier dimension is N, choose

\[
r=\max\{3,\lceil\log(NB_{\rm tail}/\delta)/\log D\rceil\}.
\]

Then the singular-value tail is at most delta/N. The determinant/column-selection argument in `SOURCE_COLUMN_CORE_AND_CLOSURE_CONTRACT.md` (archived SHA256 `7ab4afb26f3ee6a2bb662b0d90832446fd66fa2aac806eb942ff330438217803`, section 2) supplies source-only columns with Frobenius residual at most sqrt((q+1)(N-q)) delta/N<=delta. If the codimension bound reaches N, take all independent columns. Since N=O(L^4), the selection factor costs only O(log L) extra jets. This proves the stated arbitrary-delta rank cost at the **DERIVED paper** level. Neither a Lean near-null theorem nor an all-aperture compiler certificate is asserted; the finite L5 response certificates have a different, strictly finite scope.

## 4. Every outside-core rough-filter cost is explicit

For the full-prefix rough operator N_y and any L2 input on [0,T], causal shifts are contractions and

\[
\|N_y\|_{2\to2}
\le\sum_{d\le e^T}d^{-1/2}\le2e^{T/2}.
\tag{8}
\]

This bound is uniform in y and includes the unit term. Hence the core error obeys

\[
\|N_y(Z-v_L)\|_2\le2e^{T/2}d_L,
\]

which is at most 2 exp(-L/2) under (7) and T=L/2. Prehistory is included in the norm on the entire prefix. No error is charged only on the late half.

Choose any prescribed source-only collection of cutoffs 2<=y_j<=Y_T=floor(T/(8 log(T+2))) and nonnegative weights summing to one. The genuine completed fields satisfy ||N_yZ||_2<=||U||_2 exp(2 sqrt(y)). Therefore

\[
\boxed{
\sum_jw_j\|N_{y_j}v_L\|_2^2
\le\mathcal B_L^2:=2\|U\|_2^2e^{4\sqrt{Y_T}}
\quad+8e^T d_L^2.}
\tag{9}
\]

The second term is exponentially small. This proves that moving to the finite core loses no unpaid rough-filter amplification.

## 5. The exact finite matrix inequality still required

If K_L has dimension zero, then v_L=0 and (6) already gives E_Z(T)<=d_L^2; no minimum eigenvalue or inverse is introduced. In the remaining case choose a physical orthonormal basis f_1,...,f_r of K_L, 1<=r<=q+1. Any redundant source-defined columns are removed before choosing the basis; no Euclidean coordinate norm or unpriced Gram condition number is substituted. Define the source-only matrix

\[
\Gamma_L(a,b)=\sum_jw_j
\langle N_{y_j}f_a,N_{y_j}f_b\rangle_{[0,T]}.
\tag{10}
\]

For the actual coefficients u_L of v_L, (9) says exactly

\[
u_L^*\Gamma_Lu_L\le\mathcal B_L^2,
\qquad \|v_L\|_2^2=\|u_L\|^2.
\tag{11}
\]

Each finite-prefix N_y has a terminating triangular Mobius inverse, since its minimum nonunit delay is positive. Thus Gamma_L is positive definite on any nonzero K_L when at least one weight is positive. This gives no quantitative lower eigenvalue uniform in the aperture.

A sufficient all-core estimate would be, at common cofinal apertures for every requested eta>0,

\[
\boxed{\Gamma_L\succeq c_{h,\eta}e^{-\eta T}I_r,
\qquad T=L/2.}
\tag{12}
\]

The constant and all thresholds must precede the horizon selection. The weaker actual-loading inequality

\[
u_L^*\Gamma_Lu_L\ge c_{h,\eta}e^{-\eta T}\|u_L\|^2
\tag{13}
\]

would suffice; (12) is stronger because arbitrary core combinations need not be genuine source fields or satisfy the actual completion equation. The core could contain nearly unstable directions whose actual loading is absent or controlled. Thus an unsuccessful all-core frame bound would not by itself refute the weaker actual-loading route.

Writing gamma_L=lambda_min(Gamma_L), the unconditional finite inequality is only

\[
E_Z(T)\le 2\mathcal B_L^2/\gamma_L+2d_L^2.
\tag{14}
\]

Its inverse cost remains explicit. Under (12), or under (13) on the actual loading, (9) and (7) make that cost and the amplified error subexponential at any requested closing rate by choosing eta smaller first. Without (12)/(13), the small unfiltered or filtered core error cannot be promoted through an arbitrarily bad finite inverse. Positivity of Gamma_L and its low dimension do not prove the rate.

**Outcome:** the output-recovery proof does support an explicit affine reconstruction, so a missing linear map is not a permanent obstruction. The inherited paper theorem's legal-carrier scope matches the exact physical H in (3), and the complete rough-family target reduces legitimately at that authority level to a source-only core of dimension at most q+1, with the offset and all outside-core rough-filter amplification paid. The remaining independent arithmetic input is the quantified finite frame inequality (12), or its weaker actual-source loading form (13). Neither was proved here. Step 4 and RH remain OPEN.

### References and scope

- See `OPICA_Round2_OUTPUT_RECOVERY.md` in the [research collection survey](../../DRIVE_SOURCE_SURVEY.json), sections 3--8: sample nodes, rational tail, literal pole recovery and physical norms. This note constructs an additional linear map instead of inferring one from its final norm inequality.
- See `102_A11_NEAR_NULL_TO_FIXED_SPLIT_RESPONSE_BUDGET.md` in the [research collection survey](../../DRIVE_SOURCE_SURVEY.json). The report records the historical source-only mixed near-null estimate and rank cost.
- The [research collection survey](../../DRIVE_SOURCE_SURVEY.json) lists `OPICA_Complete_Source_Core_Round5_2026-11-11.zip`. Its `source-core/` directory contains `NEAR_NULL_CORE_THEOREM.md` and `SOURCE_COLUMN_CORE_AND_CLOSURE_CONTRACT.md`. The archive member `source-core/SOURCE_CORE_INPUT_PROVENANCE.json` gives their original archive locations and verified hashes.
- [Filter family attempt](FILTER_FAMILY_ATTEMPT.md), sections 1 and 2: complete Gram-family bound and actual rough-prefix operators.
- [Rough echo native pairing](../step4-complete-residual-round4-2026-11-10/ROUGH_ECHO_NATIVE_PAIRING.md): prehistory, actual native rows, and full complement constraints.
