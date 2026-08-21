# RHRC obstruction ledger

## OBS-001 — TightMult information wall

**Status:** FORMAL / UNCONDITIONAL.

At `c = 2`, the inherited Zeta23 certificate based on trace, Frobenius norm, online multiplicity atoms and a positive-index bound is simultaneously extremal for an online double zero and a tight off-line pair. A proposal that only computes another function of those same quantities has not introduced new information.

**Escape requirement:** name a new channel: scale evolution, aperture variation, localization, probe-family response, zero/prime coupling, or another independently defined structure.

## OBS-002 — Density-one is not RH

Any method that is insensitive to `o(N)` exceptional zeros cannot close RH. Proportion improvements are benchmark/frontier work, not terminal-route closure.

## OBS-003 — Conditional support > 1

Routes that require conjectural prime-pair / pair-correlation input remain conditional. Removing one named conjecture is insufficient if an equivalent conditional dependency remains elsewhere.

## OBS-004 — Pointwise cancellation hazard

A single exponentially growing summand does not by itself imply growth of the magnitude of the whole residual. Cancellation must be controlled, preferably through localization, a norm, or a probe family.

## OBS-005 — FFBBP target leakage

RUN_36 used target-dependent cost in association. This is a permanent regression fixture. Certificate association must be source-only.

## OBS-006 — FFBBP source-side false-field bias

RUN_37 removed target leakage but still generated a field in a known-null world. Unknown-field search requires known-null suppression and multi-seed calibration.

## OBS-007 — Window artifact

RUN_41 rejected `curvature_gap` because it lost to a matched W96 adversarial null and failed the predeclared evolving-transfer condition. Window-local lift is not enough.

## OBS-008 — Scalar prime-upper equivalence wall

**Status:** FORMAL / UNCONDITIONAL (Lean).

The R001 scalar prime-side target — `ArithmeticSideSubexponential`, i.e. subexponentiality of
the translated pole-killed literature-RHS residual for every admissible C² test — is logically
**equivalent** to RH:

    Zeta23.ExceptionalZero.arithmeticSideSubexponential_iff_criticalLine
    (Zeta23/ExceptionalZero/ArithmeticReduction.lean, sorry-free, standard axioms only).

Forward: exposed-pole detector + target-adaptive pole-killed visibility + reflection.
Converse: on the critical line every filtered mode has unit modulus, so the family is bounded.

Consequences. (1) `R001_PRIME_UPPER` is not "one more prime estimate"; closing it in this
observable class IS proving RH. (2) For any replacement observable `O`, once the zero-side leg
"off-line zero ⇒ ¬Subexponential O" is proved, the corresponding upper-bound leg is again
RH-strength; observable-engineering can only reorganize where the RH-strength difficulty sits
(cf. Weil positivity ⇔ RH).

**Escape requirement:** a named new information channel must come with a *new, weaker-looking
but sufficient* zero-side leg whose matching upper bound is provable by an identified
unconditional mechanism — and the pair must be exhibited before terminal coding, per the
feasibility-gate discipline.

## OBS-009 — Band-limited Weil positivity wall (R002 arithmetic leg)

**Status:** CLASSICAL (Weil's criterion), not formalized. Recorded as a design
constraint, not as a Lean theorem.

The R002-A observable is the negative index of the windowed Gram `G̃(T)`. By the
unconditional zero-side/prime-side identity (`ZeroConfig.Gz_eq_Gp` +
`paperInputs_zeta`), the Hermitian form at any real `w` is *exactly*

    wᵀ G w = ∫ |W(τ)|² ν_X(τ) dτ,   W(τ) = Σ_k w_k φ̂(τ − τ_k).

So the property "`G̃(T)` has no negative direction" **is** Weil positivity
restricted to band-limited tests of bandwidth `L = λ·l` localized at height `T`.
RH implies it (on-line contributions are PSD; `ZeroSide.blockA_decomp`), and
positivity for the whole family `∀(T, λ>1)` restores Weil's criterion, hence RH.

Consequence. R002-A **relocates** the R001/OBS-008 difficulty rather than
removing it — but into a better-posed statement: a positivity assertion about an
explicitly given quadratic form, with no δ-threshold and no exponent race
(in the oversampled regime `λ > 1` every depth `δ > 0` is detectable; see the
feasibility certificate §3). The exchange rate is explicit: detecting shallower
zeros requires larger `λ`, i.e. `X = e^L = (T/2π)^λ > T`, a longer Dirichlet
polynomial on the prime side.

**Escape requirement:** an unconditional band-limited positivity theorem at some
bandwidth/height regime in which the zero-side leg is also non-vacuous — i.e. a
regime pair `(λ > 1, T)` where `∫|W|²ν_X ≥ −θ` is provable by a named mechanism
(MV quadratic form, Chebyshev, μ-part positivity, `Tail.prop_tail`). No such
regime is currently identified; §5 of the feasibility certificate grades what is
and is not available.

**What is NOT blocked by this entry:** the block-level separation
(`R002_MULTI_PROBE_SEPARATION`, proved), which is pure linear algebra and makes
no arithmetic claim.
