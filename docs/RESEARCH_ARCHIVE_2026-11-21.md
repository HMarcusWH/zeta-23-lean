# Mathematical approach and scientific status — frozen research snapshot

**Archive date:** 21 November 2026. **Project:** `HMarcusWH/zeta-23-lean`. **Author of the listed manuscripts:** Marcus Hermansson. **Sources:** the original Git history, pinned Lean theorem modules and 43 unmodified PDF manuscripts in [the paper index](../papers/README.md).

## Why preserve this work

The programme was a sustained, source-specific attempt to translate the Riemann hypothesis (RH) into finite, computable, and formally auditable consequences of a hypothetical nontrivial zeta zero away from the critical line. The mathematics does not become uninteresting merely because another group has announced a proposed proof. An announced RH proof, however, must not be represented as an independently accepted theorem before the relevant checks and mathematical scrutiny are complete.

The fork begins from the Anthropic `zeta-23-lean` work on a different zeta-zero theorem. The fork's contributions and the upstream proof are distinct; see `UPSTREAM_README.md`, `UPSTREAM_AUDIT.md`, `FORK_NOTES.md`, `LICENSE`, and `NOTICE`.

## Four-step research architecture

1. **Fingerprint an off-line zero.** Use Weil's zero-side quadratic form, explicit finite Gram witnesses and the complete two-translate correlation to turn a hypothetical off-critical zero into sign-sensitive data. The explicit pair witness is constructive, but pair-local negativity alone is not full-form negativity: other zero contributions can mask an isolated block.
2. **Prove the obstruction cannot hide from every finite canonical detector.** Reconcile the exact Weil–Connes–Consani–Moscovici (CCM) source normalization and the finite Guinand–Weil dictionary. Use boundary-flat centered coefficient spaces (vanishing zeroth, first and second moments), finite Fourier approximation and centered zero extension. This produces conditional finite negative directions that persist under truncation enlargement.
3. **Synchronize and transport the same source.** Study first-bad cutoff shells, reversal parity, cubic secular equations, kernel-safe Schur complements, nonunitary cross-parity maps, real-aperture prime seams, source moments and Riesz endpoint jets. Separately, establish co-Poisson/Fourier rigidity and work with a fixed native causal source, its prime-power field, multiplicity-sensitive Laplace data and Hilbert/Gram observations. Carefully retain the real arithmetic source, sign, norm, aperture, carrier and cutoff at every interface.
4. **Find an independent contradiction.** What the preceding steps do *not* give is a new arithmetic upper/sign/positivity theorem incompatible with the conditional obstruction. The required Step 4 source restriction remains OPEN in this repository. An RH-equivalent finite criterion does not prove its own nonnegativity; negative-ground classification does not exclude negative grounds.

## Selected concrete results, with their limits

- **Closed-form local negativity:** For `B = c(xx^T - yy^T)` with `c > 0`, the witness `w = ||x||^2 y - <x,y>x` satisfies `w^T B w = -c (||x||^2 ||y||^2 - <x,y>^2)^2`. This is a precise finite theorem for a transverse pair block, not an RH proof.
- **Finite dictionary scalar-defect reduction:** On the specified smooth core, the remaining zero/deterministic matrix discrepancy reduces to one rank-one channel `delta_L * 11^T`, subsequently removed by tent mollification. The `11^T` channel is distinct from an identity-matrix normalization shift.
- **Normalization reconciliation:** Comparing literal published CCM formulas with the direct source identifies a scalar identity difference `Q_can = M_print + 2 c_print(L) I` in the conventions of that manuscript. This is presented as a narrow source-specific correction, not independent proof of priority.
- **Persistent finite detection:** A hypothetical off-line zero forces an admissible boundary-flat finite vector with negative canonical Weil value; that value survives centered extension. This is a conditional existence theorem, not universal finite positivity.
- **Parity and spectral rigidity:** The first-bad successor has a one-dimensional new cubic shell. Exact Schur/secular, cross-parity and kernel/range identities constrain negative modes; prime-entry seams are controlled through the legal compression. Later work includes conditional simultaneous two-parity negativity, source-visibility and quartic-cutoff constraints. The missing source exclusion remains independent.
- **Fourier/co-Poisson results:** Signed lattice-gap hypotheses lead to negative-mass budgets and non-repair statements for the precisely specified measure/profile classes. Actual-zero profiles carry a forced arithmetic term; deleting that term to claim self-adjoint eigenvalue exclusion would be invalid.
- **Native causal source:** Source-specific transforms, residual/memory bounds, exact logarithmic-window growth rates and finite Gram certificates distinguish obstruction detection from an opposing upper bound. An exact four-column filtered certificate excludes only a small region already covered by classical zero verification; the same raw trial has a much larger error.
- **Late research:** The signed Möbius/Mellin, regular quartic Schur-inertia and prime-phase noncollision manuscripts (Papers XXV–XXVII) sharpen exact source geometry and feasible conditional packets without establishing the independent sign estimate.

## How to interpret novelty and verification

These manuscripts contain candidate new *source-specific* theorems, decompositions, constants, normalization identities and formal proof integrations. Many ingredients (Weil positivity, Bombieri's finite negative index, Fourier convolution, Mellin methods, Nyman–Beurling approximation, Schur complements, Jordan measures and Laguerre polynomials) have extensive prior art. Mathematical originality and priority beyond the explicitly compared literature require independent expert assessment.

`PROVED` means the exact theorem and hypotheses have a claimed pinned Lean/CI verification trail, not that every claim in an accompanying PDF was independently compiled or refereed. `DERIVED` is a manuscript-level consequence; `EXPERIMENTAL` is a bounded computation; `OPEN` is an unproved obligation. No new whole-repository Lean run or specialist referee report was performed for this archival commit.

## External proposed RH proof (20–21 November 2026)

Levent Alpöge reported an RH/Dirichlet-GRH proof produced with Claude and released a large Lean formalization. Early independent kernel/build checks were publicly reported, but independent mathematical review and wider acceptance were still developing as of this archive date. Reference: https://www.nature.com/articles/d41586-026-03812-7 and https://apnews.com/article/4fe8b69a891f160f9e7f0c85af8c55c8 . This separate claim is not a theorem established by this fork, and no logical equivalence between the two approaches is asserted.

## Why the archive is frozen

This snapshot preserves the actual methods, negative controls, conditional reductions, independent mathematical results, original PDF versions and open obligations. The project is archived as a research record rather than rewritten retroactively to present its unresolved Step 4 as solved. Future work, if any, should start from a new branch or release and be labeled distinctly.

**Open boundary as of this snapshot:** neither RH nor the source-specific independent Step 4 contradiction has been proved by these manuscripts. A future independent proof of RH would not erase the validity of their separately stated finite, Fourier, causal, arithmetic and formal mathematical conclusions.
