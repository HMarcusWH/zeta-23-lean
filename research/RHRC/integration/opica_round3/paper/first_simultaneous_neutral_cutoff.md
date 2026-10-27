# UCDP-13 — First simultaneous pole-neutral parity-negative cutoff

**Status:** DERIVED finite-dimensional/same-source consequence of UCDP-11/12 and inherited nesting; NOT a separately Lean-compiled theorem. Does not prove RH.

## Setup

Fix an aperture L at which **both** actual pole-neutral parity sectors have a negative vector at some finite cutoff. UCDP-12 guarantees a cofinal set of such apertures conditional on one actual off-line zero. At this same L define

`K_e(L) = min {K≥3 | ∃ negative vector in U_even(L,K)}`, 
`K_o(L) = min {K≥3 | ∃ negative vector in U_odd(L,K)}`,
`K_both(L) = max(K_e(L),K_o(L))`.

The sets are nonempty by hypothesis. Fixed-L centered extension is the exact native neutral isometric inclusion and preserves the **complete Weil form**. Thus both parity spaces have negative vectors at `K_both` and no smaller cutoff has simultaneous negative parity witnesses. The canonical neutral full form on the direct sum has negative index at least 2.

## Exact newborn-sector alternative

- If `K_e<K_o`, the **odd** neutral predecessor at `K_o-1` is PSD while the even sector is already negative at `K_o`; the odd sector gains a first negative mode through its one-complex-dimensional new shell. The earliest odd negative mode has index exactly one.
- If `K_o<K_e`, reverse the roles.
- If `K_e=K_o`, **both** neutral predecessors are PSD and each parity gains a first negative mode in its one-dimensional shell at the same cutoff. The complete neutral form has exactly two negative modes at that cutoff, one per parity.

In any newly negative parity, the exact first-bad one-shell dichotomy UCDP-09 applies: a nonzero predecessor-kernel coupling, or vanishing kernel coupling with a strictly negative **full** Schur scalar. That dichotomy does not require a positive predecessor inverse on the kernel; the pseudoinverse is taken only on `(ker A)⊥`.

## Consequences and limitations

1. This is an **actual-source same-aperture mixed-parity transition**, not an identification with the historical **unrestricted** `N_any(L)` or global first-bad branch.
2. The parity newly negative at `K_both` has PSD neutral predecessor, but the **other** parity might already have negative predecessors. Existing theorems demanding **both** predecessors PSD cannot be imported at `K_both` without further proof.
3. Even when `K_e=K_o`, equality of cutoffs does **not** imply equality of the two negative eigenvalues. Do not treat this as a spectral tie covered by `Step123SameStateN23`.
4. For cofinally large L with simultaneous-negative intervals, K_both can depend on L and no bound `K_both≤ceil L⁴` is currently established.
5. Source-only exact inertia (`SourceParityExactInertia.lean`) refers to a different matrix component than the complete pole-neutral Weil form. No sign comparison follows.

## Synthetic controls

Nested diagonal Hermitian models with negative eigenvalues arriving in the two parities at different cutoffs satisfy the first two cases. Simultaneous arrival with unequal negative diagonal values satisfies the third case without a spectral tie. None is a native zeta counterexample. The controls disprove the inference that `K_both` must have both PSD predecessors or a tied negative ground.

## Smallest missing source-theorem target

A *direct*, source-faithful restriction on the **actual corrected cubic-plus-projected-output defect** at such a mixed-parity newborn state could connect the independently proved S15 and Step123 evidence. A theorem excluding every regular/resonant newborn transition when the opposite parity is already negative would contradict the cofinal overlap. But that restriction is not established; naive sign-only versions are false in generic nested Hermitian models.

**RH and Step 4 remain OPEN.**
