import Zeta23.CCM.CubicSecularMetric

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A1: zero-resonance cubic coupling

This module classifies what the canonical cubic shell coupling does on the
kernel of the projected successor predecessor block

  A = P_W T|_W.

Important semantic firewall: `ker A` is the kernel of this projected block in
the successor problem. It is not identified here with the kernel of the
predecessor-size compressed operator.

If `A z = 0`, the full successor image `T z` has no predecessor coordinate and
therefore lies in the one-dimensional intrinsic shell. The canonical cubic
coordinate from E2 then gives the exact shell coefficient. Full-operator
symmetry identifies that coefficient with the cubic coupling `<z, Bc>`.

No statement that the coupling vanishes is made. No predecessor/shell
invariance, parity-nullity theorem, zero-shift inverse, positivity closure, or
RH theorem is claimed.
-/

/-- If a predecessor-block vector lies in `ker A`, its full successor image is
exactly its intrinsic shell component. Equivalently, `T z` lies in the
one-dimensional successor shell. -/
theorem parityCompressedCanonical_eq_shellPart_of_intrinsicPredecessorBlock_eq_zero
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (z : intrinsicParityPredecessorSubspace p N)
    (hz : intrinsicPredecessorBlock p L N z = 0) :
    parityCompressedCanonical p L (N + 1)
        (z : euclideanParityBoundaryFlatSubspace p (N + 1)) =
      ((intrinsicShellPart p N
          (parityCompressedCanonical p L (N + 1)
            (z : euclideanParityBoundaryFlatSubspace p (N + 1))) :
          intrinsicParitySuccShell p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1)) := by
  let y := parityCompressedCanonical p L (N + 1)
    (z : euclideanParityBoundaryFlatSubspace p (N + 1))
  have hpred : intrinsicPredecessorPart p N y = 0 := by
    change intrinsicPredecessorBlock p L N z = 0
    exact hz
  have hrec := intrinsicPredecessorPart_add_shellPart p N y
  rw [hpred] at hrec
  simpa [y] using hrec.symm

/-- Exact E4-A1 coefficient identity. On `ker A`, the cubic coupling is the
conjugate of the canonical cubic shell coordinate of `T z`, multiplied by the
nonzero shell self-inner normalization. -/
theorem inner_intrinsicPredecessorBlock_kernel_cubicCoupling_eq
    (p : ReversalParity) (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (z : intrinsicParityPredecessorSubspace p N)
    (hz : intrinsicPredecessorBlock p L N z = 0) :
    let c := intrinsicCubicShellPart p N
    let b := intrinsicShellToPredecessor p L N c
    let y := parityCompressedCanonical p L (N + 1)
      (z : euclideanParityBoundaryFlatSubspace p (N + 1))
    inner ℂ
        (z : euclideanParityBoundaryFlatSubspace p (N + 1))
        (b : euclideanParityBoundaryFlatSubspace p (N + 1)) =
      star (intrinsicCubicQuotientCoordinate p N y) *
        inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
  dsimp
  let c := intrinsicCubicShellPart p N
  let b := intrinsicShellToPredecessor p L N c
  let y := parityCompressedCanonical p L (N + 1)
    (z : euclideanParityBoundaryFlatSubspace p (N + 1))
  let s := intrinsicShellPart p N y
  have hyShell :
      y =
        ((s : intrinsicParitySuccShell p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    simpa [y, s] using
      parityCompressedCanonical_eq_shellPart_of_intrinsicPredecessorBlock_eq_zero
        p L N z hz
  have hBT :
      inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          (parityCompressedCanonical p L (N + 1)
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))) =
        inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    let yc := parityCompressedCanonical p L (N + 1)
      (c : euclideanParityBoundaryFlatSubspace p (N + 1))
    have hyrec := intrinsicPredecessorPart_add_shellPart p N yc
    have hort := inner_intrinsicPredecessor_shell_eq_zero
      p N z (intrinsicShellPart p N yc)
    have hbdef : intrinsicPredecessorPart p N yc = b := by
      rfl
    change
      inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1)) yc =
        inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1))
    rw [← hyrec, inner_add_right, hort, add_zero, hbdef]
  have hsym :
      inner ℂ y
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) =
        inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          (parityCompressedCanonical p L (N + 1)
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))) := by
    exact parityCompressedCanonical_isSymmetric p L (N + 1)
      (z : euclideanParityBoundaryFlatSubspace p (N + 1))
      (c : euclideanParityBoundaryFlatSubspace p (N + 1))
  have hcouple :
      inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1)) =
        inner ℂ y
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    exact (hsym.trans hBT).symm
  have hrep := intrinsicCubicShellCoordinate_smul_cubic_eq p N hN s
  have hrepCarrier :
      ((intrinsicCubicShellCoordinate p N s • c :
          intrinsicParitySuccShell p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1)) =
      ((s : intrinsicParitySuccShell p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    exact congrArg
      (fun t : intrinsicParitySuccShell p N =>
        (t : euclideanParityBoundaryFlatSubspace p (N + 1))) hrep
  have hyCubic :
      y =
        intrinsicCubicShellCoordinate p N s •
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    rw [hyShell]
    rw [← hrepCarrier]
    rfl
  change
    inner ℂ
        (z : euclideanParityBoundaryFlatSubspace p (N + 1))
        (b : euclideanParityBoundaryFlatSubspace p (N + 1)) =
      star (intrinsicCubicShellCoordinate p N s) *
        inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))
  rw [hcouple, hyCubic]
  exact inner_smul_left
    (c : euclideanParityBoundaryFlatSubspace p (N + 1))
    (c : euclideanParityBoundaryFlatSubspace p (N + 1))
    (intrinsicCubicShellCoordinate p N s)

/-- On the kernel of the projected predecessor block, zero cubic coupling is
exactly equivalent to being a genuine zero mode of the full successor
compressed operator. This does not assert that either condition holds for any
nonzero vector. -/
theorem inner_cubicCoupling_eq_zero_iff_successor_zero_of_intrinsicPredecessorBlock_eq_zero
    (p : ReversalParity) (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (z : intrinsicParityPredecessorSubspace p N)
    (hz : intrinsicPredecessorBlock p L N z = 0) :
    inner ℂ
        (z : euclideanParityBoundaryFlatSubspace p (N + 1))
        ((intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N) :
            intrinsicParityPredecessorSubspace p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 ↔
      parityCompressedCanonical p L (N + 1)
        (z : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
  let c := intrinsicCubicShellPart p N
  let b := intrinsicShellToPredecessor p L N c
  let y := parityCompressedCanonical p L (N + 1)
    (z : euclideanParityBoundaryFlatSubspace p (N + 1))
  have hidentity :=
    inner_intrinsicPredecessorBlock_kernel_cubicCoupling_eq
      p L N hN z hz
  dsimp at hidentity
  change
    inner ℂ
        (z : euclideanParityBoundaryFlatSubspace p (N + 1))
        (b : euclideanParityBoundaryFlatSubspace p (N + 1)) =
      star (intrinsicCubicQuotientCoordinate p N y) *
        inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) at hidentity
  have hccne :
      inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) ≠ 0 := by
    simpa [c] using inner_intrinsicCubicShellPart_self_ne_zero p N hN
  constructor
  · intro hzero
    change
      inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 at hzero
    have hprod :
        star (intrinsicCubicQuotientCoordinate p N y) *
          inner ℂ
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))
            (c : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 :=
      hidentity.symm.trans hzero
    have hstarq : star (intrinsicCubicQuotientCoordinate p N y) = 0 :=
      (mul_eq_zero.mp hprod).resolve_right hccne
    have hq : intrinsicCubicQuotientCoordinate p N y = 0 := by
      simpa using hstarq
    have hscoord :
        intrinsicCubicShellCoordinate p N (intrinsicShellPart p N y) = 0 := by
      simpa [intrinsicCubicQuotientCoordinate] using hq
    have hs0 : intrinsicShellPart p N y = 0 :=
      (intrinsicCubicShellCoordinate_eq_zero_iff p N hN).mp hscoord
    have hyShell :
        y =
          ((intrinsicShellPart p N y : intrinsicParitySuccShell p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) := by
      simpa only [y] using
        parityCompressedCanonical_eq_shellPart_of_intrinsicPredecessorBlock_eq_zero
          p L N z hz
    change y = 0
    calc
      y =
          ((intrinsicShellPart p N y : intrinsicParitySuccShell p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) := hyShell
      _ = 0 := by simp [hs0]
  · intro hy0
    have hy0' : y = 0 := by
      simpa only [y] using hy0
    change
      inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0
    calc
      inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1)) =
        star (intrinsicCubicQuotientCoordinate p N y) *
          inner ℂ
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))
            (c : euclideanParityBoundaryFlatSubspace p (N + 1)) := hidentity
      _ = 0 := by
        rw [hy0']
        simp

/-- Quantified E4-A1 classification. The canonical cubic coupling vanishes on
the entire kernel of the projected predecessor block if and only if every such
kernel vector is already a genuine zero mode of the full successor operator.
This is intentionally not phrased as a predecessor-size spectral lift. -/
theorem cubicCoupling_zero_on_intrinsicPredecessorBlock_kernel_iff
    (p : ReversalParity) (L : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    (∀ z : intrinsicParityPredecessorSubspace p N,
      intrinsicPredecessorBlock p L N z = 0 →
        inner ℂ
          (z : euclideanParityBoundaryFlatSubspace p (N + 1))
          ((intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N) :
              intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) = 0) ↔
      (∀ z : intrinsicParityPredecessorSubspace p N,
        intrinsicPredecessorBlock p L N z = 0 →
          parityCompressedCanonical p L (N + 1)
            (z : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0) := by
  constructor
  · intro h z hz
    exact
      (inner_cubicCoupling_eq_zero_iff_successor_zero_of_intrinsicPredecessorBlock_eq_zero
        p L N hN z hz).mp (h z hz)
  · intro h z hz
    exact
      (inner_cubicCoupling_eq_zero_iff_successor_zero_of_intrinsicPredecessorBlock_eq_zero
        p L N hN z hz).mpr (h z hz)

end Zeta23.CCM

#print axioms Zeta23.CCM.parityCompressedCanonical_eq_shellPart_of_intrinsicPredecessorBlock_eq_zero
#print axioms Zeta23.CCM.inner_intrinsicPredecessorBlock_kernel_cubicCoupling_eq
#print axioms Zeta23.CCM.inner_cubicCoupling_eq_zero_iff_successor_zero_of_intrinsicPredecessorBlock_eq_zero
#print axioms Zeta23.CCM.cubicCoupling_zero_on_intrinsicPredecessorBlock_kernel_iff
