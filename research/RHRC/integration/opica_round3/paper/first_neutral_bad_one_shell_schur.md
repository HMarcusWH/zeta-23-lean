# UCDP-09 — First pole-neutral bad cutoff is one-complex-shell; exact Schur/resonance dichotomy

**Status: DERIVED** from S15, current exact neutral nesting/form preservation and elementary finite-dimensional Hermitian linear algebra; this composite is **NOT separately Lean-compiled**.

## 1. Same-aperture first neutral cutoff

Fix L beyond the S15 threshold and let `K0≥3` be the **least** index where some eligible pole-neutral parity restriction of the entire prime+Archimedean canonical Weil form has a negative direction. Existence follows from `finite_pole_neutral_approximation`; use `CanonicalPoleExponentialMoments` to transfer the two physical moments into the actual parity kernels. It is not assumed equal to the older unrestricted `N_any` or to the deep threshold `K_deep`.

`CanonicalPoleNeutralNesting.lean` provides exact isometric embeddings `U_p(K-1)→U_p(K)` preserving the energy, and `CanonicalPoleNeutralBottomNFlow.lean` proves the predecessor compression equals the former operator. Crucially, each parity neutral dimension is `K-2` for K≥3; the successor orthogonal shell has **exactly one complex dimension**, including the zero-space K=2→K=3 case.

Thus at `K0`, the neutral predecessors of **both** parities are PSD. Each new parity operator has negative index at most 1, and at least one has negative index exactly 1. Simultaneous one-negative-mode branches are possible; no chosen parity is imposed.

## 2. Exact 1D Hermitian block

Fix either parity p. Identify the actual predecessor subspace inside the successor by the proved isometry. Choose any unit vector e in its one-dimensional orthogonal complement. Relative to this decomposition the complete neutral Hermitian form is

     Q_p(L,K0) = [[A, b], [b*, d]],

where A is the **actual** preceding pole-neutral compressed canonical operator, A≥0; `b = P_prev Q_p(L,K0)e` is the actual cross term and `d=Re⟨Q_p(L,K0)e,e⟩∈R`. At K0=3, A is the zero-dimensional operator and b=0 by definition.

Decompose `b=b0+b1`, with `b0=P_(ker A)b`, `b1⊥ker A`. Use `A†` for the inverse of A on `(ker A)⊥`, extended by zero on the kernel. The *exact dichotomy* is:

- **Resonant:** `b0≠0`. Then a vector in `ker A ⊕ C e` has negative energy for any real d; indeed the 2×2 restriction has determinant `-‖b0‖²<0`. The operator also has one positive mode there.
- **Regular:** `b0=0`. Completing the square gives

      Q_p(z,t)=⟨A(z+tA†b),z+tA†b⟩ + (d−⟨b,A†b⟩)|t|².

  Therefore this parity becomes negative at the successor **iff** `s:=d−⟨b,A†b⟩<0`. If s≥0 it remains PSD.

Because the original predecessor is PSD and only one complex dimension is added, at the *first neutral-bad index* there can be at most one negative direction in each parity even in the resonant branch.

## 3. Joint consequence under the hypothetical off-line zero

Combining S15 with the same-aperture shell theorem gives:

`¬RH ⇒ ∃ L0>0 ∀L>L0 ∃K0≥3` such that `K0` is the least pole-neutral negative cutoff; one or both parities have the actual complete predecessor A≥0 and **either** `P_kerA b ≠0` **or** `P_kerA b=0 ∧ s<0`.

For every L selected by the previously compiled *cofinal quartic deep original detector* (§ UCDP-08), `K0≤ceil(L⁴)`. This binds the qualitative S15 witness and the quantitative original-detector data to the **same canonical source form**, but it does not imply that the cutoff K0 itself has the full deep `exp(βL)` margin or that the other parity is nonnegative.

## 4. Falsification controls

- `A=diag(0,2), b=(1,0), d=1000` : resonant negative with arbitrarily large **positive** new-shell diagonal. No scalar diagonal-sign shortcut survives.
- `A=diag(0,2), b=(0,1), d=2/5` : regular negative because s=2/5−1/2=−1/10.
- Same A,b, `d=1/2` : regular PSD at s=0, including a kernel.
- `K0=3`: A is empty and only d<0 gives a negative parity ground.
- A parity whose neutral form becomes negative at K0 may coexist with another parity remaining PSD or independently becoming negative at the same cutoff. Nothing forces equality of their ground modes.

These are abstract Hermitian controls, not zeta counterexamples.

## 5. Smallest unproved closing interface

A new, independently source-derived theorem saying **for every actual same-aperture legal neutral predecessor PSD, the shell coupling is perpendicular to the preceding kernel and the complete scalar Schur is nonnegative** would inductively exclude all neutral negative cutoffs and, combined with S15, yield RH. It is in effect a highly concentrated RH-strength positivity law; defining or assuming it is not progress. It must be proved from the complete prime/Archimedean arithmetic and checked against historical sign and resonant controls.

This new 1D-shell form is a better **experimental target** than unrelated fixed K3 boxes or generic positivity of the one-copy native L² dictionary. It is not yet the missing independent arithmetic inequality.
