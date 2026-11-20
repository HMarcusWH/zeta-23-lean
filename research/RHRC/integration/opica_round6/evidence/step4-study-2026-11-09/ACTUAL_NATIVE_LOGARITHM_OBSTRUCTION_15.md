# The actual finite logarithm is exponentially large on the legal native slice

9 November 2026. Immutable repository source: `b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`, tree `d0a6b1ad78523c23834eb01f57f4910a22e30d3b`. **DERIVED paper argument; no new Lean compilation, repository mutation or CI qualification.** This result concerns a genuine legal test vector and the unchanged prime coefficients. It does not establish or refute PG, SB, Step 4 or RH.

## Result and its limited implication

Write (Z_L) for the complete finite integer translate operator on (L^2[0,L]), (W_L=\log Z_L) for its finite nilpotent logarithm and (Y_L=W_L-W_L^*). There are absolute constants (c>0,L_*>2) and, at every real (L\ge L_*), a real unit vector (f_L) in the actual **even native moment slice** at (K=\lceil L^4\rceil) such that

\[
 \boxed{\|Y_Lf_L\|_2\ge c e^{L/2}L^{-21/2}.} \tag{1}
\]

The vector has Fourier degree four, the required endpoint jets and the literal elementary-pole condition. Thus a polynomial or all-positive-rate subexponential norm bound for the logarithm on the closing carrier is false, even after imposing those exact source-domain restrictions. This improves the earlier whole-space logarithm obstruction, whose constant test vector was illegal on that carrier.

It does **not** prove that the complete signed pairing is large or has the wrong sign. The prime contribution is

\[
 \langle f,(B_L+B_L^*)f\rangle
 =2\operatorname{Re}\langle X_cf,Y_Lf\rangle,
 \qquad X_c=t-L/2.
\]

The native floor needs an **upper** for this pairing relative to the complete Archimedean term. On the terminal interval used to prove (1), our pairing actually has negative sign. The rest of the interval remains in the exact expression. No complement has been dropped.

## 1. Complete finite arithmetic, reused rather than claimed as new

For the zero-extended shift (S_uf(t)=\mathbf1_{t\ge u}f(t-u)),

\[
 Z_L=\sum_{n\le e^L}n^{-1/2}S_{\log n},\qquad
 Z_L^{-1}=\sum_{n\le e^L}\mu(n)n^{-1/2}S_{\log n}.
\]

The sums are finite; shifts by at least (L) vanish almost everywhere. Since (Z_L-I) is nilpotent, its polynomial logarithm is exactly

\[
 W_L=\sum_{p^k\le e^L}\frac{1}{k p^{k/2}}S_{k\log p}
 =\sum_{2\le n\le e^L}\frac{\Lambda(n)}{\sqrt n\log n}S_{\log n}. \tag{2}
\]

The divisor law and the derivation ([X,S_u]=uS_u) give

\[
 B_L=\sum_{n\le e^L}\frac{\Lambda(n)}{\sqrt n}S_{\log n}
     =Z_L^{-1}[X,Z_L]=[X,W_L]. \tag{3}
\]

Reflection (Rf(t)=f(L-t)) gives (RW_LR=W_L^*), hence (Y_L) reverses parity and

\[
 B_L+B_L^*=[X_c,Y_L]. \tag{4}
\]

These are the already derived identities in `SOURCE_TRACE_ATTEMPT.md`, Sections 2–4. They use actual Möbius/von Mangoldt coefficients and all integer histories, rather than a replacement convolution. The current Lean `native_weighted_dirichlet_identity` and `nativeIntegerTranslateAction_primeField_eq_integerDriveField` certify the underlying unchanged arithmetic coefficients and local source compatibility; this paper does not attribute the finite-operator logarithm statement to those narrower declarations.

## 2. An explicit vector in the exact closing carrier

Set

\[
 g_L(t)=\sin^8(\pi t/L),\qquad
 F_L(t)=g_L''(t)-\tfrac14g_L(t),\qquad
 f_L=F_L/\|F_L\|_2,\quad 0\le t\le L. \tag{5}
\]

Use zero extension outside the interval for all physical operators. The analytic trigonometric formula is used only inside the interval and for checking its endpoint jets.

The function (g_L) has degree four in the modes (e^{2\pi int/L}), is reflection-even and vanishes to order eight at both endpoints. Therefore (F_L) is degree four, reflection-even and vanishes to order six. Its Fourier coefficients (u_n), in the repository normalization (L^{-1/2}e^{2\pi int/L}), satisfy

\[
 \sum_n n^j u_n=0\quad(j=0,1,2,4).
\]

In fact all endpoint derivative moments through order five vanish. The first three are the literal `BoundaryFlatCoefficients`; the fourth is `evenPhysicalMoment ... 4`, whose kernel defines `evenMomentSlice`.

For either sign, integration by parts twice, with the actual endpoint values (g_L=g_L'=0), gives

\[
 \int_0^L e^{\pm t/2}F_L(t)\,dt=0. \tag{6}
\]

This is the actual pole functional, not just a similarly named moment. If (F_L=L^{-1/2}\sum_{n=-4}^4u_ne^{2\pi int/L}) and (u_{-n}=u_n\in\mathbb R), then, with (\omega_n=2\pi n/L),

\[
 \int_0^L e^{-t/2}F_L(t)dt
 =\frac{1-e^{-L/2}}{2\sqrt L}\sum_n\frac{u_n}{1/4+\omega_n^2}
 =2\sqrt L(1-e^{-L/2})\sum_n\frac{L u_n}{L^2+16\pi^2n^2}. \tag{7}
\]

The final sum is precisely `canonicalPoleEvenFunctional` with `poleEvenProfile`. Thus (6) puts the physical Fourier vector in `poleNeutralEvenSubspace`; the fourth moment puts it in its `evenMomentSlice`. Centered zero extension from degree four to (K=\lceil L^4\rceil\ge16) preserves these conditions. Parseval makes the inherited Euclidean norm equal to the physical (L^2) norm. No (D^2)-coordinate reweighting or change of physical norm is involved.

The seed is a test vector in an all-vector closing carrier. It is **not identified with a source-selected eigenray, an odd ground state, or the moving geometry normal**. Their additional hypotheses cannot be attached to it.

For (G(v)=\sin^8(\pi v)), integration by parts also gives the exact norm formula

\[
 \|F_L\|_2^2
 =\frac L{16}\int_0^1G^2
   +\frac1{2L}\int_0^1(G')^2
   +\frac1{L^3}\int_0^1(G'')^2.
\]

Consequently

\[
 \frac{\|F_L\|_2}{\sqrt L}\longrightarrow
 \eta:=\frac14\sqrt{\int_0^1\sin^{16}(\pi v)dv}>0. \tag{8}
\]

## 3. The canceled moment and the first surviving logarithmic moment

Let (A_L=\int_0^L e^{-s/2}g_L(s)ds). In addition to the exact cancellation in (6), integrating against (s e^{-s/2}) gives

\[
 \int_0^L s e^{-s/2}F_L(s)ds=-A_L. \tag{9}
\]

Indeed ((D^2-1/4)(s e^{-s/2})=-e^{-s/2}), and every integration-by-parts boundary term vanishes. Dominated convergence, using (L^8\sin^8(\pi s/L)\le\pi^8s^8), proves

\[
 A_L\sim C_0L^{-8},\qquad C_0=\pi^8\int_0^\infty e^{-s/2}s^8ds
 =\pi^8\,8!\,2^9>0. \tag{10}
\]

There is also a uniform bound, for (L\ge2) and (0\le s\le L),

\[
 |F_L(s)|\le C L^{-8}(s^6+s^8). \tag{11}
\]

To see it, write (\kappa=\pi/L):

\[
 g_L''=56\kappa^2\sin^6(\kappa s)\cos^2(\kappa s)
         -8\kappa^2\sin^8(\kappa s).
\]

Together with (|\sin(\kappa s)|\le\kappa s), this proves (11). In particular every fixed weighted absolute moment (int_0^L e^{-s/2}s^j|F_L(s)|ds) is (O_j(L^{-8})). Separately, the elementary fixed-degree formulas give uniform bounds for (|F_L|_\infty+|F_L'|_\infty) when (L\ge2).

## 4. The actual prime contribution and its uniform asymptotic

Fix (a\in(0,\log2)). All following estimates are uniform for (t\in[L-a,L]) as real (L\to\infty). The ordinary-prime part of (W_LF_L(t)) is

\[
 \sum_{p\le e^t}p^{-1/2}F_L(t-\log p).
\]

The required arithmetic input is the **effective unconditional PNT**, not qualitative PNT at a shrinking scale. It supplies (\vartheta(x)=x+O(xe^{-c\sqrt{\log x}})) for a positive constant (c). This follows from the classical prime-counting remainder in [NIST DLMF 27.12.E5](https://dlmf.nist.gov/27.12.E5) by partial summation; passing from primes to prime powers is not hidden in this use.

Finite Stieltjes integration with

\[
 w_{L,t}(x)=\frac{x^{-1/2}}{\log x}F_L(t-\log x)
\]

replaces the prime sum by

\[
 I_L(t)=\int_{\log2}^t\frac{e^{u/2}}uF_L(t-u)du
       =e^{t/2}\int_0^{t-\log2}\frac{e^{-s/2}F_L(s)}{t-s}ds. \tag{12}
\]

Here are sufficient uniform error bounds. The primes and integral with (x\le e^{t/2}) are each (O(e^{t/4})), by boundedness of (F_L), integer counting and (log x\ge\log2). On (e^{t/2}\le x\le e^t),

\[
 |w_{L,t}(x)|\le Cx^{-1/2}/t,
 \qquad |w_{L,t}'(x)|\le Cx^{-3/2}/t.
\]

The PNT remainder and its Stieltjes boundary terms are therefore bounded by

\[
 O\left(e^{t/2}e^{-c'\sqrt t}/t\right)+O(e^{t/4}). \tag{13}
\]

The upper endpoint is actually zero since (F_L(0)=0), but that saving is unnecessary. The lower endpoint, any prime exactly at an endpoint and the complete small-prime range are all covered by these bounds. Formula (13) is (o(e^{t/2}L^{-10})) uniformly on the stated terminal interval.

It remains to evaluate the continuum expression rather than bound it absolutely. On (0\le s\le t/2),

\[
 \frac1{t-s}=\frac1t+\frac s{t^2}+\frac{s^2}{t^2(t-s)}.
\]

Replace the first two truncated moments by their complete moments (6) and (9). Their tails are exponentially small by boundedness of (F_L). By (11), the remainder is (O(L^{-8}t^{-3})). On (t/2\le s\le t-\log2), the denominator is at least (log2), so this entire part costs (O(e^{t/4})) after the outer exponential. Thus

\[
 I_L(t)=-\frac{e^{t/2}A_L}{t^2}
         +O(e^{t/2}L^{-11})+O(e^{t/4}(1+t)),
\]

and hence

\[
 I_L(t)\sim -C_0e^{t/2}L^{-10}. \tag{14}
\]

In particular, the exact pole cancellation removes the (1/t) term but leaves the (1/t^2) term. The surviving coefficient has been computed from the actual legal test; it is not an unspecified inverse constant.

## 5. All proper prime powers remain, and the adjoint vanishes exactly here

The part of (2) with (k\ge2) has polynomial total absolute coefficient mass. For squares,

\[
 \sum_{p^2\le e^L}\frac1{2p}
 \le\frac12\sum_{2\le n\le e^{L/2}}\frac1n=O(1+L).
\]

For (k\ge3),

\[
 \sum_{k\ge3}\frac1k\sum_p p^{-k/2}
 \le \frac1{1-2^{-1/2}}\sum_{n\ge2}n^{-3/2}<\infty.
\]

Since (|F_L|_\infty=O(1)), their complete contribution is (O(1+L)), negligible relative to (14). Combining (10)–(14), with all powers still present, gives

\[
 \boxed{W_LF_L(t)\sim -C_0e^{t/2}L^{-10}}
 \quad\text{uniformly for }t\in[L-a,L]. \tag{15}
\]

There is no shift of length less than (log2) in (W_L). For (t\in[L-a,L]), every adjoint shift (f(t+\log n)), (n\ge2), is outside the interval. Therefore

\[
 W_L^*F_L(t)=0 \tag{16}
\]

exactly, apart from irrelevant endpoint conventions. Normalize using (8), and integrate the squared lower bound from (15) on this interval. Since (int_{L-a}^Le^tdt=(1-e^{-a})e^L), there are (c,L_*>0) such that (1) holds at **every** (L\ge L_*). These constants are selected before (L); no subsequence or numerical extrapolation is used.

## 6. The one-sided action and source constraints remain distinct

The theorem rules out the following attempted proof step on the actual even PG/SB slice:

> Replace the complete one-sided prime pairing by (L|Y_Lf|_2|f|_2), and pay it with a polynomial or subexponential norm bound for (Y_L) on that carrier.

It also rules out that norm bound for (W_L), by (15). It does not rule out exploiting its sign in the **integrated** action. Indeed, uniformly for fixed (0<r\le a),

\[
 F_L(L-r)=\pi^8L^{-8}\bigl(56r^6-r^8/4+O(L^{-2})\bigr)>0
\]

for sufficiently large (L) (the error can equivalently be written relative to (r^6), uniformly down to zero). On the same interval (Y_LF_L<0) and (X_c>0). The observed large terminal logarithm therefore gives a **negative** local contribution to (2\langle X_cf_L,Y_Lf_L\rangle), which is favorable for the Weil floor. Reflection gives the same sign near the other endpoint. No conclusion about the remaining signed integral follows by deleting it.

The exact current even, odd and tied-ground constraints apply to particular eigenrays or reciprocal inputs. Membership of our seed in the legal slice does not establish any of those additional hypotheses. Conversely, those conditional identities alone do not supply an upper for the complete paired action over the whole slice. This pass makes no new identification of the seed with a ground or source history.

The existing supplier map remains unchanged: PG needs one fixed parity and a polynomial whole-slice floor at every sufficiently large aperture; SB needs one finite whole-slice floor at cofinally many apertures, with parity chosen per aperture. A direct signed upper could still satisfy either consumer without a full inverse or logarithm norm estimate. **No such upper was proved here. Step 4 and RH remain OPEN.**

## Reading and authority limits

Actual definitions/proofs reread for the carrier: `MomentSlices.lean` in full; `BoundaryFlatFiniteSpace.lean` and `CanonicalPoleNeutralCarrier.lean` in full; relevant definitions in `CanonicalPoleNeutralGeometry.lean` and `ConstrainedParityGeometry.lean`. Actual coefficient/local-source compatibility reread: `NativeIntegerPrimeSource.lean` and `NativeIntegerPrimeConvolution.lean` in full. Source hashes, precise partial ranges and prior cache provenance are recorded in the companion reading receipt. The paper finite-operator identities are not silently promoted to current Lean declarations.

No archived program was executed. No formal declaration, artifact gate or compiler result was created in this pass. The effective PNT input is standard unconditional analysis, with its precise use separated from the current project's proof authority.
