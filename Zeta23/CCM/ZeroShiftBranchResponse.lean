import Zeta23.CCM.ZeroShiftShellResponse

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A3b: signed regular response and canonical resonant pole

E4-A3a identifies the decoupled zero-shift response with one canonical cubic
shell scalar.  E4-A2 already provides the exact algebraic decomposition

  W = ker A ⊕ range A

for the projected predecessor block `A = P_W T|_W`.

This module makes that decomposition operational.  The kernel coordinate
vanishes exactly on `range A`; projecting the shifted block equation gives the
exact denominator-free identity

  (-lam) • K(R_lam b) = K(b).

For the canonical cubic coupling `b = B c`, its kernel coordinate `k = K(b)`
is therefore the canonical resonance certificate.  In the decoupled branch
`k = 0`; in the resonant branch `k ≠ 0` and the safe shifted resolvent carries
an exact `1/(-lam)` kernel pole.

The regular branch is also sharpened by combining E4-A3a with the already
proved negative zero-shift endpoint: the canonical shell-response scalar has
strictly negative real part at the forced negative explicit root.

Firewalls:
* `ker A` is the kernel of the projected successor predecessor block, not the
  predecessor-size compressed-operator kernel;
* the denominator-free pole identity is primary; no inverse of `A` at zero is
  introduced;
* no spectral decomposition or resolvent limit is used;
* `T u₀ = sigma₀ c` does not make `u₀` an eigenvector and no shell invariance
  is claimed;
* neither branch is excluded here;
* no negative-root exclusion, positivity closure, finite-to-infinite closure,
  or RH theorem is claimed.
-/

/-- The canonical kernel coordinate vanishes exactly on `range A`. -/
theorem intrinsicPredecessorKernelPart_eq_zero_iff_mem_range
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    {w : intrinsicParityPredecessorSubspace p N} :
    intrinsicPredecessorKernelPart p L N w = 0 ↔
      w ∈ LinearMap.range (intrinsicPredecessorBlock p L N) := by
  exact Submodule.projectionOnto_apply_eq_zero_iff
    (intrinsicPredecessorBlock_kernel_isCompl_range p L N)

/-- Applying the predecessor block always lands in the range, so its canonical
kernel coordinate is zero. -/
theorem intrinsicPredecessorKernelPart_intrinsicPredecessorBlock_eq_zero
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x : intrinsicParityPredecessorSubspace p N) :
    intrinsicPredecessorKernelPart p L N
        (intrinsicPredecessorBlock p L N x) = 0 := by
  apply (intrinsicPredecessorKernelPart_eq_zero_iff_mem_range p L N).2
  exact ⟨x, rfl⟩

/-- Exact kernel-coordinate action of the shifted predecessor block. -/
theorem intrinsicPredecessorKernelPart_shiftedIntrinsicPredecessorBlock
    (p : ReversalParity) (L : ℝ) (N : ℕ) (lam : ℝ)
    (y : intrinsicParityPredecessorSubspace p N) :
    intrinsicPredecessorKernelPart p L N
        (shiftedIntrinsicPredecessorBlock p L N lam y) =
      (-lam : ℂ) • intrinsicPredecessorKernelPart p L N y := by
  change
    intrinsicPredecessorKernelPart p L N
        (intrinsicPredecessorBlock p L N y - (lam : ℂ) • y) = _
  rw [map_sub, map_smul,
    intrinsicPredecessorKernelPart_intrinsicPredecessorBlock_eq_zero,
    zero_sub]
  exact
    (neg_smul (lam : ℂ)
      (intrinsicPredecessorKernelPart p L N y)).symm

/-- E4-A3b core identity: after projection to `ker A`, the safe shifted
resolvent has an exact denominator-free pole coefficient. -/
theorem neg_lam_smul_intrinsicPredecessorKernelPart_resolvent_eq
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    (b : intrinsicParityPredecessorSubspace p N) :
    (-lam : ℂ) •
        intrinsicPredecessorKernelPart p L N
          (shiftedIntrinsicPredecessorResolvent
            p hL N hprev lam hlam b) =
      intrinsicPredecessorKernelPart p L N b := by
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  have hres :
      shiftedIntrinsicPredecessorBlock p L N lam (R b) = b := by
    simpa [R] using
      shiftedIntrinsicPredecessorBlock_resolvent_apply
        p hL N hprev lam hlam b
  have hproj := congrArg
    (intrinsicPredecessorKernelPart p L N) hres
  rw [intrinsicPredecessorKernelPart_shiftedIntrinsicPredecessorBlock] at hproj
  simpa [R] using hproj

/-- Divided form of the exact kernel pole, derived only after using `lam < 0`
to certify the scalar denominator is nonzero. -/
theorem intrinsicPredecessorKernelPart_resolvent_eq_inv_neg_smul
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    (b : intrinsicParityPredecessorSubspace p N) :
    intrinsicPredecessorKernelPart p L N
        (shiftedIntrinsicPredecessorResolvent
          p hL N hprev lam hlam b) =
      ((-lam : ℂ)⁻¹) • intrinsicPredecessorKernelPart p L N b := by
  let y := intrinsicPredecessorKernelPart p L N
    (shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam b)
  let k := intrinsicPredecessorKernelPart p L N b
  have hpole : (-lam : ℂ) • y = k := by
    simpa [y, k] using
      neg_lam_smul_intrinsicPredecessorKernelPart_resolvent_eq
        p hL N hprev hlam b
  have hnegneR : -lam ≠ 0 := ne_of_gt (neg_pos.mpr hlam)
  have hnegne : (-lam : ℂ) ≠ 0 := by
    exact_mod_cast hnegneR
  calc
    y = (1 : ℂ) • y := by simp
    _ = (((-lam : ℂ)⁻¹) * (-lam : ℂ)) • y := by
      rw [inv_mul_cancel₀ hnegne]
    _ = ((-lam : ℂ)⁻¹) • ((-lam : ℂ) • y) := by
      rw [mul_smul]
    _ = ((-lam : ℂ)⁻¹) • k := by rw [hpole]

/-- The canonical kernel component pairs with the original vector exactly as
it pairs with itself; the range component contributes no cross term. -/
theorem inner_intrinsicPredecessorKernelPart_coupling_eq_self
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (b : intrinsicParityPredecessorSubspace p N) :
    inner ℂ
        (((intrinsicPredecessorKernelPart p L N b :
            LinearMap.ker (intrinsicPredecessorBlock p L N)) :
          intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        (b : euclideanParityBoundaryFlatSubspace p (N + 1)) =
      inner ℂ
        (((intrinsicPredecessorKernelPart p L N b :
            LinearMap.ker (intrinsicPredecessorBlock p L N)) :
          intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        (((intrinsicPredecessorKernelPart p L N b :
            LinearMap.ker (intrinsicPredecessorBlock p L N)) :
          intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) := by
  let k := intrinsicPredecessorKernelPart p L N b
  let r := intrinsicPredecessorRangePart p L N b
  have hrk :
      inner ℂ
          ((r : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          ((k : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 :=
    inner_intrinsicPredecessorBlock_range_kernel_eq_zero
      p L N
      (r : intrinsicParityPredecessorSubspace p N)
      (k : intrinsicParityPredecessorSubspace p N)
      r.property k.property
  have hkr :
      inner ℂ
          ((k : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          ((r : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
    rw [inner_eq_zero_symm]
    exact hrk
  have hrec := intrinsicPredecessorKernelPart_add_rangePart p L N b
  have hrecAmbient :
      ((k : intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) +
        ((r : intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) =
        (b : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    simpa [k, r] using congrArg
      (fun w : intrinsicParityPredecessorSubspace p N =>
        (w : euclideanParityBoundaryFlatSubspace p (N + 1))) hrec
  rw [← hrecAmbient, inner_add_right, hkr, add_zero]

/-- Nonzero canonical kernel coordinate is equivalent to the existence of a
nontrivial coupling witness in `ker A`. -/
theorem intrinsicPredecessorKernelPart_ne_zero_iff_exists_kernel_coupling
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (b : intrinsicParityPredecessorSubspace p N) :
    intrinsicPredecessorKernelPart p L N b ≠ 0 ↔
      ∃ z : intrinsicParityPredecessorSubspace p N,
        intrinsicPredecessorBlock p L N z = 0 ∧
        inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1)) ≠ 0 := by
  constructor
  · intro hk
    let k := intrinsicPredecessorKernelPart p L N b
    have hkker : intrinsicPredecessorBlock p L N
        (k : intrinsicParityPredecessorSubspace p N) = 0 := k.property
    have hpair := inner_intrinsicPredecessorKernelPart_coupling_eq_self p L N b
    have hkAmbientNe :
        ((k : intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) ≠ 0 := by
      intro hzero
      apply hk
      apply Subtype.ext
      apply Subtype.ext
      exact hzero
    have hselfNe :
        inner ℂ
          ((k : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          ((k : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) ≠ 0 := by
      intro hzero
      exact hkAmbientNe ((inner_self_eq_zero).mp hzero)
    refine ⟨(k : intrinsicParityPredecessorSubspace p N), hkker, ?_⟩
    exact hpair.trans_ne hselfNe
  · rintro ⟨z, hz, hzb⟩ hkzero
    have hbRange : b ∈ LinearMap.range (intrinsicPredecessorBlock p L N) :=
      (intrinsicPredecessorKernelPart_eq_zero_iff_mem_range p L N).1 hkzero
    have hbz :
        inner ℂ
          (b : euclideanParityBoundaryFlatSubspace p (N + 1))
          (z : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 :=
      inner_intrinsicPredecessorBlock_range_kernel_eq_zero
        p L N b z hbRange hz
    have hzbzero :
        inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
      rw [inner_eq_zero_symm]
      exact hbz
    exact hzb hzbzero

/-- Canonical kernel component of the actual cubic shell coupling. -/
def cubicCouplingKernelPart
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    LinearMap.ker (intrinsicPredecessorBlock p L N) :=
  intrinsicPredecessorKernelPart p L N
    (intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N))

/-- A zero-shift preimage forces the canonical cubic kernel component to
vanish. -/
theorem cubicCouplingKernelPart_eq_zero_of_preimage
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x₀ : intrinsicParityPredecessorSubspace p N)
    (hx₀ : intrinsicPredecessorBlock p L N x₀ =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)) :
    cubicCouplingKernelPart p L N = 0 := by
  apply (intrinsicPredecessorKernelPart_eq_zero_iff_mem_range p L N).2
  exact ⟨x₀, hx₀⟩

/-- The cubic coupling is resonant exactly when its canonical kernel component
is nonzero. -/
theorem cubicCouplingKernelPart_ne_zero_iff_resonant
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    cubicCouplingKernelPart p L N ≠ 0 ↔
      ∃ z : intrinsicParityPredecessorSubspace p N,
        intrinsicPredecessorBlock p L N z = 0 ∧
        inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          ((intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N) :
              intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) ≠ 0 := by
  exact intrinsicPredecessorKernelPart_ne_zero_iff_exists_kernel_coupling
    p L N
      (intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N))

/-- Exact denominator-free pole for the canonical cubic coupling. -/
theorem neg_lam_smul_cubicCouplingKernelPart_resolvent_eq
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0) :
    (-lam : ℂ) •
        intrinsicPredecessorKernelPart p L N
          (shiftedIntrinsicPredecessorResolvent
            p hL N hprev lam hlam
              (intrinsicShellToPredecessor p L N
                (intrinsicCubicShellPart p N))) =
      cubicCouplingKernelPart p L N := by
  exact neg_lam_smul_intrinsicPredecessorKernelPart_resolvent_eq
    p hL N hprev hlam
      (intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N))

/-- Divided exact pole for the canonical cubic coupling. -/
theorem cubicCouplingKernelPart_resolvent_eq_inv_neg_smul
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0) :
    intrinsicPredecessorKernelPart p L N
        (shiftedIntrinsicPredecessorResolvent
          p hL N hprev lam hlam
            (intrinsicShellToPredecessor p L N
              (intrinsicCubicShellPart p N))) =
      ((-lam : ℂ)⁻¹) • cubicCouplingKernelPart p L N := by
  exact intrinsicPredecessorKernelPart_resolvent_eq_inv_neg_smul
    p hL N hprev hlam
      (intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N))

/-- At the forced negative explicit root, the canonical regular shell response
has strictly negative real part. -/
theorem cubicZeroShiftShellResponseScalar_re_neg_of_explicit_root
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (x₀ : intrinsicParityPredecessorSubspace p N)
    (hx₀ : intrinsicPredecessorBlock p L N x₀ =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N))
    (lam : ℝ) (hlam : lam < 0)
    (hroot : cubicExplicitSchurScalar p hL N hprev lam hlam = 0) :
    Complex.re (cubicZeroShiftShellResponseScalar p L N x₀) < 0 := by
  let c := intrinsicCubicShellPart p N
  let sigma := cubicZeroShiftShellResponseScalar p L N x₀
  have hSneg :=
    cubicZeroShiftSchurEndpoint_re_neg_of_explicit_root
      p hL N hN hprev x₀ hx₀ lam hlam hroot
  have hendpoint :=
    cubicZeroShiftSchurEndpoint_eq_star_shellResponse_mul_inner
      p L N hN x₀ hx₀
  have hcne : c ≠ 0 := by
    exact intrinsicCubicShellPart_ne_zero p N hN
  have hcAmbientNe :
      (c : euclideanParityBoundaryFlatSubspace p (N + 1)) ≠ 0 := by
    intro hzero
    apply hcne
    apply Subtype.ext
    exact hzero
  have hnormpos :
      0 < ‖(c : euclideanParityBoundaryFlatSubspace p (N + 1))‖ ^ 2 := by
    positivity
  have hre := congrArg Complex.re hendpoint
  change
    Complex.re (cubicZeroShiftSchurEndpoint p L N x₀) =
      Complex.re
        (star sigma *
          inner ℂ
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))) at hre
  have hre' :
      Complex.re (cubicZeroShiftSchurEndpoint p L N x₀) =
        Complex.re sigma *
          ‖(c : euclideanParityBoundaryFlatSubspace p (N + 1))‖ ^ 2 := by
    rw [hre, inner_self_eq_norm_sq_to_K]
    simp [Complex.mul_re]
  rw [hre'] at hSneg
  nlinarith

end Zeta23.CCM

#print axioms Zeta23.CCM.intrinsicPredecessorKernelPart_eq_zero_iff_mem_range
#print axioms Zeta23.CCM.intrinsicPredecessorKernelPart_shiftedIntrinsicPredecessorBlock
#print axioms Zeta23.CCM.neg_lam_smul_intrinsicPredecessorKernelPart_resolvent_eq
#print axioms Zeta23.CCM.intrinsicPredecessorKernelPart_resolvent_eq_inv_neg_smul
#print axioms Zeta23.CCM.intrinsicPredecessorKernelPart_ne_zero_iff_exists_kernel_coupling
#print axioms Zeta23.CCM.cubicCouplingKernelPart_ne_zero_iff_resonant
#print axioms Zeta23.CCM.neg_lam_smul_cubicCouplingKernelPart_resolvent_eq
#print axioms Zeta23.CCM.cubicZeroShiftShellResponseScalar_re_neg_of_explicit_root
