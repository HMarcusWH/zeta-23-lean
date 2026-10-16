# Mathematical amendment to the Step 1–3 output specification

**13 October 2026 · Proposed only · RH OPEN**

This is an addendum arising from the Argon review. It does not replace the accepted build specification, weaken the K3 D2 obligation, create a PR, or claim that the new statements are compiled. No original specification file was edited.

## A. Correct the semantic and type guards

1. **Two spectral parameters.** Store `eta` and the actual selected `lam` separately. Bind the ground branch and secular normalization at `lam`, with a proof `lam ≤ -eta - g`. Bind the detector Schur block at `-eta`. A ground package at `-eta` must not be constructed from the threshold selector.
2. **Two inverse bounds.** The detector predecessor inverse uses `12 * (Kd - 1) / D`; the ground-level predecessor inverse uses `6 * (Kd - 1) / D`. Record which shifted operator every numeric bound encloses.
3. **Separate negative depth and parity gap.** No rule derives `oddBottom - lam ≥ D/3` from strict-even selection and negative depth. Carry actual `delta`; test a strict-even state whose two bottoms are both negative.
4. **Separate legal and neutral compression.** The v4 identity for a neutral input returns legal outputs. It does not prove output neutrality. The neutral continuum defect is `g0 * (-b * alphaP)`, not zero.
5. **No simple-product-zero assumption.** Preserve the universal detector's imaginary/real-axis zero location but allow coincident factor multiplicities. Elementary pole zeros remain separately simple/double as appropriate.
6. **Domain guards.** Construct the causal equality before any assertion that `X_epsilon` lies in the Hilbert space. Native input `Y_epsilon` is stable; native output `X_epsilon` is not assumed stable.
7. **Do not merge source identities.** Original source, finite approximation, selected ground and continuous contact retain different identifiers and explicit transports. History estimates on the original two lobes cannot silently attach to a selected ground.

## B. Corrected finite observable

For any fixed native aperture/cutoff whose eligible pole-neutral even ground and source-root conditions have been established, output

\[
 \alpha_P(u),\quad S_{P,0}(u),\quad S_{C,0}(u),\quad M_4(u),\quad
 \mathcal B_P(u),\quad
 \mathcal A_C(u):=-\Re(\overline{S_{C,0}(u)}M_4(u)).
\]

The exact expected identity is

\[
 \mathcal A_C(u)-\mathcal B_P(u)
 =\langle(B_{M,0}-\lambda I)D_0u,D_0u\rangle.
\]

A positive native ground is useful for checking this equality but is not a hypothetical RH counterexample. The identity itself is blind to a common scalar spectral shift and is not a negative-energy discriminator. A claimed closing estimate must include the additional native premise that makes it distinguish the prohibited state.

The product formula for `B_P` requires the explicit source-divisor condition. When that condition is not established, output the directly defined pairing `-Re(conj(S_P0(u))*M4(u))` with its ordinary resolution status, not a falsely certified positive product.

Potential supporting modules, **names proposed, not asserted to exist**:

- `Zeta23/CCM/CanonicalPoleNeutralPoisson.lean`: actual projections, non-invariance, corrected defect, the exact K3 control.
- `Zeta23/CCM/CanonicalNeutralRootBudget.lean`: rational source function, a conditional root-divisor budget theorem, and strict-even/tie consequences. A conditional theorem about a supplied divisor does not prove that the Step 1–3 producer supplies that divisor.

These are candidate extensions, not silently added mandatory work packages. The source-divisor producer's analytic/zero-flip authority must remain explicit.

## C. Improve the native angle report

For each fixed positive damping, retain the exact first-prime interval, the original `R = 0` history convention, and the fixed positive constant `A_epsilon`. Report

\[
 \mathcal E(T),\quad \|Z\|_{\epsilon,[0,T]}^2,\quad c_T,
 \quad\mathcal E(T)(1-c_T),\quad
 \det G_T/\mathcal E(T),\quad\lambda_{\min}(G_T).
\]

The proposed PAPER limiting values, assuming divergent energy and the exact stable-difference decomposition, are respectively

\[
 \tfrac12\|Z\|_\epsilon^2,\qquad\|Z\|_\epsilon^2,
 \qquad\tfrac12\|Z\|_\epsilon^2.
\]

Do not call near-unit normalized correlation a vanishing unnormalized Gram mode. Do not count the angle and mixed-energy quiet criteria as independently established restrictions merely because both are displayed.

## D. Improve the range report

Record the actual ratios

\[
 \kappa_n=\|A_\epsilon^*e_n\|^2/\|e_n\|^2
\]

and the residual norm separately. The divergent-sum condition is equivalent to a zero limiting residual under the contraction hypothesis; it remains a closing obligation. A fixed finite discretization can converge to zero even when the infinite problem has a nonzero stationary residual. A source-tail and discretization estimate must precede any infinite-range interpretation.

## E. Required new falsifiers and proof-state guards

Retain the supplied exact continuum K3 example, the shifted-inverse counterexample, the arbitrarily small parity gap example, the coincident sinc-product zero examples, the modified-prime root-pattern control, and the finite-section shift control. Their successful replay means their specified incorrect inferences remain falsified, not that RH is proved.

All proposed new claims stay PAPER/OPEN until their exact Lean statement and source producer are compiled with permitted axioms and the usual complete gates. K3 D2 remains independently OPEN until its original continuous both-parity requirement is satisfied.
