# Native multiplicity continuation boundary

Stable main files owned by theory: `Zeta23/OPICAFollowup/MultiplicityTail.lean` and `research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedMultiplicity.lean`. Their final narrow save/consumer passed. Do not alter these bytes during the integrating owner's checkpoint. New work is external until separately green. No ledger, validation, docs, commit or push is owned by theory.

The original remaining roots are `native_auxiliary_top_moment`, `native_auxiliary_tail_residual_lower` and `native_terminal_memory_lower`. Required definitions `nativeTruncatedResidual` and `tailMemory` remain absent. Preserve all100 contracts.

Paper authority: frozen final audited paper, Part II.3, lines192-223. Actual y_k,d=c_k*U_d, with a_k*F_d=y_k,d and norm(y)<=L1(c_k)*L2(U_d). At an actual right zero rho=1/2+p of multiplicity m>=1, all moments below m-1 vanish and the top is `(-1)^m r_k(p) J_d(p) iteratedDeriv m zeta rho` (no extra m!). For the actual finite truncation f_T=F_d 1_[0,T], the stable residual y-a_k*f_T is supported in [T,infinity). Its norm is at least `D_rho,d |r_k(p)| exp(delta T)`, D=`(2delta)^(m-1/2)|J_d(p) zeta^(m)(rho)|/(m-1)!`. A6 is `tailMemory >= sqrt(2alpha_k)/A_k * max(D|r_k|exp(delta T)-norm(y),0)`. These must be conclusions about actual objects.

Useful proved interfaces:

- AuxiliaryCompletions: `auxCompletionFilter_integrable`, `auxCompletionFilter_L1_bound`, measurable causal c_k; `aux_completion_uniform_decay`; full filled transform and weighted-L2 kernel facts.
- UniformSourceBounds: actual `integerDriveFamily_sq_integrable`, `integerDriveFamily_memLp_two`, `integerDriveFamilyL2`, `integerDriveFamilyL2_norm_eq`, exact source-order budgets.
- NativeCompletionEquation: `nativeIntegerTranslate_causal_convolution_comm`, generic in any actual causal integrable left filter and continuous causal right field. This is the correct local Fubini identity; no global prime-field L2 premise.
- NativeDampedCompletionOperator: `nativeCompletionL2Delay`, `_norm`, `_coeFn`, `_continuous`, closed actual `nativeCompletionCausalL2`. Generalize its strong-integral construction to c_k; norm of integral gives exact Young L1*L2 constant.
- NativeDampedCompletionPointwiseBridge: proof template for actual L2 representative equality, using L2 pointwise integrability, finite-measure test-set Fubini, indicator inner products and local integral uniqueness. Module object is missing initially; its proof can be generalized externally without importing the fixed-kernel theorem.
- OPICA.WeightedLaplace: actual WeightedL2Data, actual Laplace moment equality/analyticity and `weightedLaplace_iteratedDeriv`.
- CCM.NativeCausalLaplaceMoments / Derivatives: integrability of all exponential-polynomial L2 pairings, exact derivative signs and analytic order criterion.
- NativeSourceTransforms: actual U_d transform on Re>.5 is -J_d zeta'; actual entire forward representative at ell0. Continue the stable input's genuine transform through a connected positive half-plane; retain the removable-point firewall.

Compiler boundary: pinned Lake `C:/Users/macka/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lake.exe`; isolated checkout `work/opica-audit28`, LEAN_NUM_THREADS1, maxHeartbeats800000. All own verification sessions ended. Root's broad NativeJetAdapter writer is active and its transitive closure contains NativeCompletionEquation; wait for root notification before any parent object write. No package updates, reset or broad build is authorized by theory.

## Later external supporting result

`NativeAuxiliaryStableInput.lean` now compiles exit0 without warnings; four printed transitive axiom closures contain only propext/Classical.choice/Quot.sound. See `STABLE_INPUT_STATUS.json`. It proves the actual signed convolution has a genuine causal L2 vector and representative, literal physical MemLp2 and the L1-by-L2/factorial norm bounds. No primary root is promoted, and no imported consumer or saved external olean is claimed.

The actual drive is explicitly log-weighted: `integerDriveFamily d := nativeIntegerDriveField (sourceOrderFamily d)` with `nativeIntegerDriveCoefficient n := Real.log n / Real.sqrt n`. This is distinct from unweighted `nativeIntegerTranslateAction (sourceOrderFamily d)`. The actual safe transform is `-sourceFamilyLaplace d z * deriv riemannZeta (z+1/2)`, giving moment order m-1. Genuine arithmetic commutation `a_k*F_d=c_k*U_d` remains a separate obligation until NativeCompletionEquation is available and instantiated. No global square-integrability of F_d is used.

Current external continuation candidate `NativeAuxiliaryMoments.lean` checks the initial actual Laplace product and connected right-half-plane analytic continuation. First pass exposed only convolution notation/type elaboration details; second pass is pending. `NativeAuxiliaryZeroMomentsSuffix.lean` is an unverified next fragment for all actual lower/top moments, preserving the unnormalized mth zeta derivative and phase (-1)^m. These suffixes are not current accepted source.
