# Weighted discrepancy: exact double Abel identity, origin gain, and terminal response

11 November 2026. **DERIVED paper mathematics. No repository edit, new Lean compilation, CI qualification, independent closing signed upper, or Step 4 closure.** This is a bounded continuation of the unchanged source at PR299 `b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`.

The new deductions are: an exact double-Stieltjes/Abel formula for the complete weighted discrepancy; an improved `epsilon^(1+gamma)` bound for every omitted origin boundary term; the exact rank-one terminal term in the kernel's dilation identity; and the five local counting-error trends annihilated by the actual source. The quadratic dependence on marginal discrepancy is genuine. It does not improve the exponential rate already obtained by applying the same marginal estimate to the response and then squaring.

## 1. The unchanged weighted target and source

Fix `0<gamma<1` before the horizon. Retain the complete Mangoldt field

\[
Z(t)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}h(t-\log n),
\qquad
W_\gamma(T)=\int_0^T e^{-\gamma(T-t)}|Z(t)|^2dt.
\]

The source is the real even nonzero compact profile

\[
h=(D^2-1/4)^2(q*q),\quad \operatorname{supp}h\subset[-S,S],
\quad S=1/2048,
\]

with transform

\[
H(z)=\int e^{-zv}h(v)dv=(z^2-1/4)^2Q_0(z)^2.
\tag{1}
\]

The half-pole moments and their first derivatives vanish. Every prime power remains, and `Z(t)=0` before `t0=log(2)-S>0`.

Set `X=exp(T)` and

\[
\nu_X=X^{-1}\sum_{n\ge2}\Lambda(n)\delta_{n/X},\quad
\Delta_X=\nu_X-dr,\quad
D_X(r)=\Delta_X((0,r])=\frac{\psi(Xr)-Xr}{X}.
\]

The centered measure and its cumulative discrepancy are different objects. In particular `D_X` is not assumed differentiable. Chebyshev gives a fixed constant A with

\[
\nu_X((0,r])\le Ar,\qquad |D_X(r)|\le(A+1)r.
\tag{2}
\]

For the fixed clipped kernel

\[
F_\gamma(r,s)=(rs)^{-1/2}\int_{-\infty}^{0}
e^{\gamma u}h(u-\log r)h(u-\log s)du,
\tag{3}
\]

the independently reviewed preceding identity is

\[
\mathfrak C_\gamma(X):=\iint F_\gamma\,d\Delta_Xd\Delta_X
=\frac{W_\gamma(\log X)}X\ge0.
\tag{4}
\]

The complete continuum row and column vanish exactly by `integral exp(-v/2)h(v)dv=0`. The continuum is the whole positive half-line. The upper time endpoint is retained; the lower extension to minus infinity changes no actual prime-power summand because all literal pulses start after zero.

## 2. Double Abel summation with every boundary paid

Put

\[
g(v)=h'(v)+\tfrac12h(v).
\]

Direct differentiation of the smooth kernel, at positive r,s, gives

\[
\partial_rF_\gamma(r,s)
=-r^{-3/2}s^{-1/2}\int_{-\infty}^0
e^{\gamma u}g(u-\log r)h(u-\log s)du,
\]

\[
\boxed{J_\gamma(r,s):=\partial_r\partial_sF_\gamma(r,s)
=(rs)^{-3/2}\int_{-\infty}^0
e^{\gamma u}g(u-\log r)g(u-\log s)du.}
\tag{5}
\]

These kernels vanish unless `r,s<=exp(S)` and `exp(-2S)<=r/s<=exp(2S)`. On their common support, the time variable obeys `u<=log(r)+S` and `u<=log(s)+S`. Therefore the new weight supplies an additional small-coordinate power. With fixed source/gamma constants,

\[
|F_\gamma(r,s)|\le C r^{\gamma-1},\quad
|\partial_rF_\gamma|+|\partial_sF_\gamma|\le C r^{\gamma-2},\quad
|J_\gamma(r,s)|\le C r^{\gamma-3},
\tag{6}
\]

whenever `s/r` lies in the stated fixed compact interval. The same bounds with r and s exchanged hold. They follow from Cauchy for the two compact profiles; no assumption on a prime discrepancy is used.

Choose `R0>exp(S)` and a positive epsilon that is not an atom location of nu_X. Two finite Stieltjes integrations by parts give exactly

\[
\begin{aligned}
\iint_{(\epsilon,R_0]^2}F_\gamma\,d\Delta_Xd\Delta_X
={}&F_\gamma(\epsilon,\epsilon)D_X(\epsilon)^2\\
&+D_X(\epsilon)\int_\epsilon^{R_0}
\partial_sF_\gamma(\epsilon,s)D_X(s)ds\\
&+D_X(\epsilon)\int_\epsilon^{R_0}
\partial_rF_\gamma(r,\epsilon)D_X(r)dr\\
&+\iint_{[\epsilon,R_0]^2}J_\gamma(r,s)D_X(r)D_X(s)drds.
\end{aligned}
\tag{7}
\]

All upper-boundary terms vanish because the source and all its derivatives are zero beyond the compact support. The three displayed lower-boundary terms are **each** `O_(h,gamma)(epsilon^(1+gamma))`, uniformly in X. For the side terms the other coordinate is comparable to epsilon, its integration range has length `O(epsilon)`, and (2),(6) give precisely that power. The corner gives the same power.

The integral of `|J_gamma D_X D_X|` over `r<=epsilon or s<=epsilon` has the same bound. For instance its r-small contribution is bounded by

\[
C\int_0^\epsilon r^{\gamma-3}r\left[
\int_{e^{-2S}r}^{e^{2S}r}s\,ds\right]dr
\le C'\epsilon^{1+\gamma}.
\tag{8}
\]

The original signed-measure integral also has this improved small-coordinate bound. Its total variation is dominated by `(nu_X+dr)` in each variable; using the refined F bound and the cumulative estimate yields `C integral_(0,epsilon] r^gamma d(nu_X+dr)<=C'epsilon^(1+gamma)`.

Letting epsilon decrease through nonatom values therefore proves the exact, absolutely meaningful identity

\[
\boxed{\mathfrak C_\gamma(X)
=\iint_0^\infty J_\gamma(r,s)D_X(r)D_X(s)\,drds.}
\tag{9}
\]

The improvement from an origin error of order epsilon to order `epsilon^(1+gamma)` is genuine. It prices that region more sharply; it is not a bound on the main signed correlation in (9).

## 3. The second-order gain and its exact limitation

Let

\[
\Omega(Y)=\sup_{x\ge Y}\frac{|\psi(x)-x|}{x}.
\]

For sufficiently large Y it is finite and tends to zero by ordinary PNT. On `r,s>=epsilon`,

`|D_X(r)|<=r Omega(X epsilon)` and similarly for s. The integral of `|J_gamma(r,s)|rs` is finite by (6) and comparability. Combining this with the paid origin gives the independent estimate

\[
\boxed{0\le\mathfrak C_\gamma(X)
\le C_{h,\gamma}\left[\epsilon^{1+\gamma}
+\Omega(X\epsilon)^2\right],\quad0<\epsilon<1.}
\tag{10}
\]

Thus the complete discrepancy really is quadratic in the marginal counting error after all deterministic and linear terms cancel. No first-order discrepancy term remains hidden. However this is the same square already produced by a marginal estimate on Z followed by an energy estimate; it is not an additional squaring of the arithmetic saving.

To verify the rate explicitly, suppose an independently supplied marginal bound has the form

\[
|\psi(x)-x|\le Cx^\theta(1+\log x)^b\quad(x\ge x_0),
\qquad \tfrac12\le\theta<1,\ b\ge0.
\tag{11}
\]

This is a conditional benchmark, not a newly assumed estimate for the actual source. In (9), the range where either coordinate is below `x0/X` costs `O(X^(-1-gamma))`. On the rest, comparability and (6) reduce the bound to a constant times

\[
X^{2\theta-2}(1+\log X)^{2b}
\int_{x_0/X}^{e^S}r^{\gamma+2\theta-2}dr.
\]

The integral is uniformly finite because `gamma+2theta-1>0`. Hence

\[
\boxed{W_\gamma(T)
\le C e^{(2\theta-1)T}(1+T)^{2b}+C'e^{-\gamma T}.}
\tag{12}
\]

The exact initial-origin contribution is paid in the second term. The rate is `2theta-1`, exactly the response marginal bound's energy rate. A fixed theta greater than one half therefore still leaves a fixed positive rate. Applying absolute values to the double-Abel formula does not bootstrap that rate to every positive exponent. A stronger source-specific **signed** estimate of the product discrepancy in (9) would be new information; it has not been proved here.

Ordinary PNT alone still gives `W_gamma(T)=o(exp(T))`. The fixed-source/cutoff identities do not upgrade its unspecified little-o error to a power saving. The PNT input is [DLMF 25.16.3](https://dlmf.nist.gov/25.16.E3), also checked in the preceding round; no stronger external zero theorem is inferred.

## 4. Dilation exposes the exact terminal response, not an extra coercive identity

Let the physical terminal profile in multiplicative coordinates be

\[
b_h(r)=r^{-1/2}h(-\log r).
\]

It has support `[exp(-S),exp(S)]`. Integration by parts in the time variable of (3) gives the exact simultaneous-dilation identity

\[
\boxed{\left(r\partial_r+s\partial_s-(\gamma-1)\right)
F_\gamma(r,s)=-b_h(r)b_h(s).}
\tag{13}
\]

The term on the right is the upper endpoint at time zero in the scaled kernel. It is nonzero in general. Discarding it would change the clipped source to a different object. This b_h is a physical terminal profile; it is **not** identified with the corrected native source row r or the cubic normal b. No map establishing such an identification has been supplied.

The centered arithmetic measure changes with X. For a smooth compactly supported test function f away from zero, direct differentiation of the finite Mangoldt sum gives

\[
X\frac d{dX}\int f(r)d\Delta_X(r)
=-\int\bigl[f(r)+rf'(r)\bigr]d\Delta_X(r).
\tag{14}
\]

The continuum term in this equality is zero because `integral(f+rf')dr=[rf]_0^infinity=0`. For the quadratic kernel one may either use the paid origin truncation above or differentiate the locally finite actual prime-power representation; flat support endpoints make the latter differentiation legitimate. Applying the product rule to **both** centered measures and using (13) gives

\[
\boxed{X\mathfrak C_\gamma'(X)
=-(\gamma+1)\mathfrak C_\gamma(X)
+\left(\int b_h\,d\Delta_X\right)^2.}
\tag{15}
\]

There is no frozen-measure assumption here. The last scalar has the exact arithmetic value

\[
\int b_h\,d\Delta_X
=\int b_h\,d\nu_X
=X^{-1/2}Z(\log X),
\tag{16}
\]

because the continuum integral of b_h is the vanishing half-pole moment. Since `W_gamma(T)=exp(T) C_gamma(exp(T))`, (15) becomes exactly

\[
\boxed{W_\gamma'(T)+\gamma W_\gamma(T)=Z(T)^2.}
\tag{17}
\]

This is the direct differentiation identity for the weighted energy. The kernel calculation explains the terminal term and preserves all arithmetic scale dependence; it does not supply an independent differential inequality. The unpaid quantity is the actual terminal response squared, not an omitted geometric correction. Neither (13) alone nor a fictitious X-independent Delta_X makes it small.

## 5. What the actual higher source moments remove

The double-Abel profile g has transform

\[
G(z)=\int e^{-zv}g(v)dv=(z+\tfrac12)H(z)
=(z+\tfrac12)^3(z-\tfrac12)^2Q_0(z)^2.
\tag{18}
\]

The exact single-Abel formula, for the full counting error `E_psi(x)=psi(x)-x`, is

\[
Z(t)=e^{-t/2}\int_{-S}^S e^{v/2}g(v)E_\psi(e^{t-v})dv.
\tag{19}
\]

It follows from (18), including its multiplicities, that this local functional annihilates each of the five trends

\[
\mathcal V=\operatorname{span}\{1,\log x,(\log x)^2,x,x\log x\}.
\tag{20}
\]

For verification, its value on `x^a(log x)^j` is the j-th a-derivative of `exp((a-1/2)t)G(a-1/2)`. At a=0 the transform has a triple zero, and at a=1 it has a double zero. This statement uses the actual h, not an arbitrary kernel satisfying only one moment condition.

At each **same** time t, one may subtract any `P_t` in this fixed finite-dimensional space inside (19). Its coefficients may be chosen from that local window because no t-derivative of P_t is being taken. Therefore, with

\[
\mathcal E_{\mathcal V}(t)=
\inf_{P\in\mathcal V}\sup_{x\in[e^{t-S},e^{t+S}]}
|E_\psi(x)-P(x)|,
\]

one obtains the new explicit sufficient bound

\[
|Z(t)|\le C_g e^{-t/2}\mathcal E_{\mathcal V}(t),
\qquad C_g=\int_{-S}^S e^{v/2}|g(v)|dv,
\tag{21}
\]

and hence

\[
W_\gamma(T)\le C_g^2 e^{-\gamma T}
\int_0^T e^{(\gamma-1)t}\mathcal E_{\mathcal V}(t)^2dt.
\tag{22}
\]

This isolates a local discrepancy modulo exactly these paid elementary trends. No independent bound on that residual is obtained. The subtraction is performed only inside the true compact local window. Extending arbitrary constants or log-polynomials down to r=0 in the fixed two-variable Abel formula can destroy absolute integrability; such an extension is not used. The origin proof in Section 2 continues to use the actual D_X and its linear bound.

### Falsification of an automatic exponent gain from these moments

For a complex power trend `x^rho`, with `rho` different from zero and one, (19) is exactly

\[
e^{(\rho-1/2)t}G(\rho-1/2).
\tag{23}
\]

When the source visibility gives `H(rho-1/2)!=0`, this is nonzero. On the fixed multiplicative window, its best complex-valued approximation by (20) also has a fixed positive relative error: after `x=e^t y`, the trend space maps to itself, while `y^rho` does not belong to that finite-dimensional closed space. Thus its distance is a positive source/rho constant, multiplied by `exp(Re(rho)t)`. Source moments may reduce a coefficient, but do not change that exponent.

For an actual hypothetical visible zero rho of multiplicity m, the isolated explicit-formula counting-error channel is `-m x^rho/rho`. Its response in (23) is `-m H(rho-1/2)exp((rho-1/2)t)`, exactly the surviving visible response channel. This is a **local-mode compatibility check**, not a global asymptotic for the full prime field, not a dominant-zero selection, and not an upper or lower obtained by deleting its full complement. It shows why the five valid source cancellations do not themselves remove the channel that the arithmetic estimate must exclude.

## 6. Canonical constraints retained in their actual scope

The corrected canonical packet satisfies the exact native even, pole and moment constraints, with its previously paid quartic approximation error. Those constraints transport this same source and response into the physical native column; they do not alter the arithmetic D_X or give a new estimate of (9).

In particular the native elementary negative-average theorem has a zero central Fourier coordinate premise. The actual source has integral `1/16`, and the corrected packet's central coordinate is `1/(16 sqrt(L))` up to the already tiny input error. That theorem therefore cannot be applied to this packet without a different input construction and its paid output error. No such change is made here.

Similarly, vanishing input fourth moment does not imply vanishing output fourth moment. The explicit corrected row and projected output row in the preceding round remain their actual physically normalized observations, with all arch terms and inverse-Gram normalization intact. There is no proved identification between either of those rows and b_h in (13). The source-specific shape and finite normal constraints have already entered the identities above; importing a further sign or coercivity claim from their names would add an unproved premise.

## 7. Exact remaining signed correlation

The outstanding sufficient estimate is, for fixed h and gamma,

\[
\boxed{\forall\eta>0\ \exists C_{h,\gamma,\eta}<\infty\
\forall R>1\ \exists X\ge R:\quad
\iint J_\gamma(r,s)D_X(r)D_X(s)drds
\le C_{h,\gamma,\eta}X^{-1+\eta}.}
\tag{24}
\]

Every occurrence of D_X and both coordinates belongs to the same scale X. No running maximum or stronger eventual statement is substituted. The double-Abel formula prices all boundaries and removes all deterministic and first-order continuum terms, but leaves the complete correlation of the remaining counting error. Its absolute marginal estimate gives only (12). The local-trend version (22) supplies another precise sufficient target, with its actual local discrepancy still unbounded at the required rate.

If (24) were proved independently, the existing weighted Cauchy inequality would bound the original A_Z at common cofinal horizons, contradicting its eventual visible-zero lower at a sufficiently small chosen exponent. That closing arithmetic line has **not** been discharged in this pass.

### Preservation and source trail

- `../step4-complete-residual-round4-2026-11-10/WEIGHTED_TARGET_TRANSFER.md` and `PAIRING_WEIGHTED_REVIEW.md`: exact weighted target, continuum subtraction and all-power transfer.
- `../step4-complete-residual-round4-2026-11-10/COMPLETE_COVARIANCE_ATTEMPT.md` and `COVARIANCE_REVIEW.md`: complete clipped sign masses and prior origin control.
- `../step4-complete-residual-round4-2026-11-10/NATIVE_OUTPUT_MOMENTS.md`, `SOURCE_BOUND_AUDIT.md`, and `OUTPUT_MOMENT_SOURCE_REVIEW.md`: literal native rows, output moments and the central-coordinate hypothesis mismatch.
- `../step4-signed-amplitude-round3-2026-11-10/CANONICAL_TRANSLATION_ATTEMPT.md`: actual-source exponential terminal collar and prohibition on replacing the clipped kernel by a whole-line overlap.
- `../step4-signed-response-round2-2026-11-10/OUTPUT_RECOVERY.md` and `NATIVE_SIGNED_TARGET.md`: paid physical source/output connection and the original weighted closing consumer.

**Outcome:** stronger origin control, an exact cumulative-discrepancy correlation formula, explicit terminal dilation accounting, and five paid local source cancellations. No new closing exponent or independent signed-response upper. **Step 4 and RH remain OPEN.**
