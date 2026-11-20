# Complete rough-echo pairing and the exact native complement

11 November 2026. **DERIVED paper result, pending independent review.** This combines the complete recurrence with the literal canonical source rows. No repository edits, Lean compilation, CI qualification, or Step 4 closure are claimed. Mathematical baseline: PR299 `b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`.

There is a new independent bound on a complete signed arithmetic quadratic: its growth is subexponential at the prescribed rough cutoff. The bound is on energy **plus all rough-history cross terms**, not on energy alone. The first unpaid term and the exact native-row complement are identified below.

## 1. A source-specific full-prefix quadratic bound

Retain the full Mangoldt field Z, full integer drive U, and the causal operators from `COMPLETE_RESIDUAL_RECURRENCE.md`. Freeze y>=2 and the common horizon T. Write

\[
F_y=M_{\le y}*U=N_{>y}*Z,
\qquad
M_{\le y}=\sum_{d\mid\mathcal P_y}\mu(d)d^{-1/2}S_{\log d}.
\]

Both U and Z vanish before t0=log(2)-S>0. The elementary Chebyshev estimate for the actual complete source gives a fixed C_Z with

\[
|Z(t)|\le C_Ze^{t/2}\quad(t\ge0).
\]

The already established fixed-source drive envelope implies

\[
I_U:=\int_0^\infty e^{s/2}|U(s)|\,ds<\infty.
\tag{1}
\]

For example, the envelope C(1+s)e^{s/2}exp(-c e^{s/2}) bounds I_U by the finite constant
2C integral_1^infinity (1+2 log r) r exp(-cr)dr. No property of the prime error or inverse operator enters this constant.

Expand the finite small-prime filter before estimating. Causality and s=t-log(d) give

\[
\begin{aligned}
\int_0^T |Z(t)F_y(t)|\,dt
&\le\sum_{d\mid\mathcal P_y}d^{-1/2}
\int_0^T|Z(t)U(t-\log d)|\,dt\\
&\le C_Z\sum_{d\mid\mathcal P_y}
d^{-1/2}e^{\log(d)/2}
\int_0^{\max(T-\log d,0)}e^{s/2}|U(s)|\,ds\\
&\le C_Z I_U\,2^{\pi(y)}.
\end{aligned}
\tag{2}
\]

If log(d)>T, its actual integral is zero. Thus the displayed max convention does not add a boundary contribution. The cancellation d^{-1/2}exp(log(d)/2)=1 is exact. All squarefree divisors of the primorial are included, with all actual integer-drive ages retained.

For the existing choice y_T=floor(T/(8 log(T+2))), this proves the uniform source-fixed estimate

\[
\boxed{
\int_0^T |Z(t)(N_{>y_T}*Z)(t)|\,dt
\le C_ZI_U\exp\!\left(\frac{(\log2)T}{8\log(T+2)}\right)
=\exp(o(T)).}
\tag{3}
\]

Only pi(y)<=y was used in the last inequality. More generally (2) holds for every finite y and every horizon. This is an independently bounded complete arithmetic expression, not a positive majorant imposed on unrelated coefficients.

## 2. The exact energy and rough-history identity

Define the full-prefix signed rough correlation

\[
\mathcal C_{y,T}:=
\sum_{\substack{2\le d\le e^{T-t_0}\\P^-(d)>y}}
d^{-1/2}\int_{\log d}^{T}Z(t)Z(t-\log d)\,dt.
\tag{4}
\]

The integrand is zero unless t-log(d)>=t0. Using the lower limit log(d), rather than discarding any earlier history, is therefore exact. Every rough integer and every prime-power multiplicity is retained; the rough sum is not squarefree. For real Z,

\[
\boxed{
E_Z(T)+\mathcal C_{y,T}
=\int_0^T Z(t)F_y(t)\,dt.}
\tag{5}
\]

In particular (3) bounds the absolute value of the whole left side at y=y_T. It does not bound either summand separately.

The rough correlation also has the explicit complete arithmetic expansion

\[
\mathcal C_{y,T}
=\sum_{\substack{d\ge2\\P^-(d)>y}}
\sum_{m,n\ge2}
\frac{\Lambda(m)\Lambda(n)}{\sqrt{dmn}}
k_T(\log m,\log(dn)).
\tag{6}
\]

All sums here are finite by causal support. The same clipped k_T as in the covariance note is used. This includes the echo diagonals m=dn, every other cross term, and all original prime powers; no coprimality condition on d and n is introduced.

For a late interval [a,T], the identical argument gives

\[
\int_a^T Z(t)^2dt+
\sum_{d\ge2,\,P^-(d)>y}d^{-1/2}
\int_a^T Z(t)Z(t-\log d)dt
=\int_a^T Z(t)F_y(t)dt.
\tag{7}
\]

The delayed Z arguments below a remain in (7). With a=T/2, the existing superexponentially small late forcing makes the right side superexponentially small after the elementary bound on Z. This is exact late anti-alignment, not a homogeneous equation for a freshly restarted field.

If one splits the delay sum into internal and prehistory terms, the latter are exactly

\[
\mathcal H_{y,a,T}:=
\sum_{d\ge2,\,P^-(d)>y}d^{-1/2}
\int_a^T\mathbf1_{0\le t-\log d<a}
Z(t)Z(t-\log d)\,dt.
\tag{8}
\]

They have not been priced by a small early weighted norm. Removing them would change the source equation.

The complete original covariance is O_T=E_Z(T)-D_T. Hence (5) gives

\[
O_T=\int_0^T ZF_y-\mathcal C_{y,T}-D_T.
\tag{9}
\]

The pairing and diagonal in (9) are now independently subexponential and polynomial respectively. The first unproved arithmetic inequality is a closing-rate **lower** bound on the full signed rough correlation, namely C_{y_T,T}>=-C_eta exp(eta T) at the common cofinal horizons. This is equivalent to the desired upper after the paid terms. Taking absolute values of individual correlations cannot establish it.

## 3. What the actual native rows see, with the full complement retained

Use the physically normalized source rows of `NATIVE_OUTPUT_MOMENTS.md`: r is the corrected cubic source row and v=Pi_E(n^4). They are orthogonal because r lies in the removed even normal span and v lies in the retained even carrier. Their physical profiles, centered at T=L/2, are J_r and J_v. They are real and even in the centered variable. On [0,T], therefore,

\[
\rho_r=\frac{\sqrt2 J_r}{\|r\|},\qquad
\rho_v=\frac{\sqrt2 J_v}{\|v\|}
\tag{10}
\]

are an orthonormal pair. No raw coefficient norm replaces their physical norms. The exact native column connection gives

\[
\langle\rho_r,Z\rangle
=-\frac{S(\phi_L)+A_r-e_r}{\sqrt2\|r\|},\qquad
\langle\rho_v,Z\rangle
=-\frac{m(E\phi_L)+A_v-e_v}{\sqrt2\|v\|}.
\tag{11}
\]

Here A_r,A_v are the full arch contributions and the input-correction errors satisfy |e_j|<=||j|| epsilon_L. Thus (11) retains precisely the same arch term, quartic correction and output row normalization as the preceding source-column calculation.

On L2[0,T], with zero extension before zero, define

\[
B_y f(t)=\sum_{d\ge2,\,P^-(d)>y}d^{-1/2}
\mathbf1_{t\ge\log d} f(t-\log d),\qquad
\mathcal A_{y,T}=I+\tfrac12(B_y+B_y^*).
\]

Then the actual complete quadratic in (5) is exactly <Z,A_{y,T}Z>. Let Z_parallel be the orthogonal projection of Z onto the two profiles in (10), and Z_perp=Z-Z_parallel. The full decomposition is

\[
\langle Z,\mathcal A_{y,T}Z\rangle
=\langle Z_\parallel,\mathcal A_{y,T}Z_\parallel\rangle
\quad+2\operatorname{Re}\langle Z_\parallel,\mathcal A_{y,T}Z_\perp\rangle
\quad+\langle Z_\perp,\mathcal A_{y,T}Z_\perp\rangle.
\tag{12}
\]

The existing even/odd displacement identity determines the scalar expression

\[
\|OI\phi_L\|^2-\|IE\phi_L\|^2
=2\operatorname{Re}(\overline{S(\phi_L)}m(E\phi_L))
\quad+|S(\phi_L)|^2\|b\|^2.
\tag{13}
\]

Its two output functionals are exactly those in (11), but (13) does not evaluate the last two complete terms of (12), or supply a lower bound for them. Even a small projection onto the two rows would not remove the mixed or complementary quadratic. The growing norm of B_y also means one cannot silently price its action on a small row projection as a bounded operator. No assertion that the source is a ground eigenray, no unknown ground gap, and no positivity of the canonical form has been inserted.

This is the precise remaining comparison needed for this synthesis: a source-specific lower estimate on the full rough-delay quadratic on the actual complementary output, with its mixed term, sufficiently strong to turn (3) into an upper for ||Z||^2. The rank-one displacement equality alone does not state that estimate.

## 4. The natural adjoint pairing exposes the same arithmetic cost

The actual finite-prefix adjoint is

\[
B_y^*g(s)=\sum_{d\ge2,\,P^-(d)>y}d^{-1/2}
\mathbf1_{s+\log d\le T}g(s+\log d).
\tag{14}
\]

Thus there is no lost terminal observation in an adjoint move. For either specific native profile rho in (10), the unique algebraic finite-prefix preimage under I+B_y^* is

\[
w_{y,T,\rho}(s)=
\sum_{\substack{d\le e^{T-s}\\P^-(d)>y}}
\mu(d)d^{-1/2}\rho(s+\log d),
\qquad (I+B_y^*)w_{y,T,\rho}=\rho.
\tag{15}
\]

This inverse is a finite causal inverse, not an assumed norm bound: the minimum positive delay makes its formal triangular series terminate. The displayed Mobius coefficients are the exact inverse of the rough-integer convolution, including the d=1 term. Therefore

\[
\langle\rho,Z\rangle=\langle w_{y,T,\rho},F_y\rangle.
\tag{16}
\]

For the actual finite Fourier native profile rho(s)=sum_n c_n exp(i omega_n s), (15) reads

\[
w_{y,T,\rho}(s)
=\sum_n c_n e^{i\omega_ns}
\sum_{\substack{d\le e^{T-s}\\P^-(d)>y}}
\frac{\mu(d)}{d^{1/2-i\omega_n}}.
\tag{17}
\]

The coefficients c_n include the actual center phases and row normalization. Their exact normal-moment cancellations do not establish a closing upper for these truncated, twisted rough Mobius sums or for their complete signed combination. Multiplying the rough inverse back by M_{<=y} reconstructs the original full Mobius inverse, with the same product cutoffs. Accordingly (16) does not replace the actual arithmetic observation by an independently cheap adjoint vector. The first unpaid quantity in this particular adjoint tactic is explicit in (17), rather than an unspecified inverse norm.

## 5. The family preserves the common zero obstruction

For each y frozen at its horizon, the rough characteristic transform, initially in its convergent half-plane, is

\[
\widehat N_{>y}(z)=\zeta(z+1/2)
\prod_{p\le y}(1-p^{-(z+1/2)}).
\tag{18}
\]

Every finite Euler factor is nonzero at a hypothetical rightward zero shift z=rho-1/2 with Re z>0. Meromorphic continuation therefore retains the same zero and its multiplicity for every member of this family. This is not an interchange of an infinite Euler product at a zero. Nor is an isolated exponential substituted into a divergent infinite delay sum.

The genuine forcing is filtered by the same finite factor. Thus the full transformed quotient returns exactly the same genuine source response, with all its local pole jets. The new family of bounded quadratic pairings is an additional valid arithmetic restriction, but shared finite factors do not establish a coercive norm comparison or eliminate that local zero mechanism.

**Outcome.** Equation (3) is a new independently bounded complete-source rough-echo quadratic at subexponential cost. Its exact energy identity, complete prehistory, all arithmetic correlations and native complementary terms are retained. Equations (9), (12) and (17) locate the unpaid quantities in the signed-correlation, native-complement and adjoint tactics respectively; separate control of the two row observations would still not control the full column. No closing estimate was proved in this bounded attempt. Step 4 and RH remain OPEN.
