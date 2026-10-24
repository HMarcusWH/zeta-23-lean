# Actual auxiliary stable input: supporting Post-Green pass

## What became formally true

PROVED locally in the exact external source `NativeAuxiliaryStableInput.lean`: the literal signed convolution `y_k,d(t)=integral c_k(s) U_d(t-s) ds` has a genuine causal complex L2 vector, that vector agrees almost everywhere with the literal integral, the literal integral has MemLp2, and its norm is at most `L1(c_k)*L2(U_d)`, hence at most `2/(k+1)!*L2(U_d)`. The Bochner integrand is proved integrable, so the construction does not exploit a default integral. This holds for all natural k,d. Source/hash/log/standard axiom closures are in `STABLE_INPUT_STATUS.json`.

The U_d here is the actual log-weighted drive, with coefficient `log(n)/sqrt(n)`, not the unweighted integer translate of the source. The actual completion equation with F_d is a separate next obligation. None of the three remaining primary roots has been declared or promoted. The external source has not yet been saved as a module or independently imported by a consumer.

## Workflow harvest

Only a local direct Lean source check was run. It finished exit0, warning-free, with four printed closures containing only propext, Classical.choice, Quot.sound. No new GitHub workflow or aggregate result is asserted; all global completion/RH/Step4 claims remain OPEN.

## What changed

The abstract norm estimate now applies to the actual physical signed c_k and log-weighted U_d, with an actual representative proof. c_k may change sign. No global L2 or range membership of the prime field F_d appears among the premises. The former obstacle was the L2 representative/Fubini bridge, rather than Young's inequality itself.

## Upstream implications

The strong L2 convolution proof is generic in a measurable signed real c with L1 and L2 and a causal L2 vector. Its L1 norm bound and causality use fewer hypotheses than its current representative proof. A later generic Young theorem could remove the extra L2 assumption on c from the representative step; the actual c_k already satisfies it, so that generalization is not needed for the current root.

## Downstream implications

The actual y has an analytic Laplace transform throughout Re z>0 and all exponentially weighted polynomial moments there by established parent causal-L2 calculus. Combined with the genuine initial transform, connected analytic continuation can identify it with r_k times the entire continued drive. Actual zero multiplicity should then give exactly m-1 vanishing order and the unnormalized top derivative. These implications are still being checked, not yet recorded as proved native roots.

## Resurrected routes

The native moment route no longer requires a global prime-field Hilbert-space assumption. A finite-truncation approach remains appropriate: actual arithmetic completion identifies a_k*F_d with this stable y before any global F_d norm assertion. The missing completion-equation prerequisite is currently being built by the integrating owner.

## New RH-relevant clues

LEAD: the stable y is a natural target for the actual adjoint zero-moment witnesses, and its bounded norm contrasts with exponentially growing finite-truncation residual lower bounds. This can constrain terminal memory when paired with the genuine Laguerre norm. It gives no RH conclusion by itself because the native residual identity and memory upper estimate must still be proved.

## Falsification checks

The zero kernel, k=0, d=0 and negative-time cases remain covered. Signed c is handled through absolute norms, not positivity. The log-weighted U_d has transform -J_d*zeta-prime; replacing it by an unweighted integer source would change zero order from m-1 to m and is invalid. A raw totalized multiplier at the removable elementary point cannot substitute for the analytic continuation. A global L2 assumption on F_d would circularly remove the intended obstruction and is not allowed.

## Highest-leverage next moves

Finish exact safe convolution transform and connected continuation; derive all lower moments and the phase-correct unnormalized top moment at every actual right zero; instantiate actual NativeCompletionEquation arithmetic commutation; then define the actual finite truncation/residual and use the already verified Laguerre norm. Keep all native primary names absent until actual source, integral and domain clauses are independently consumed.
