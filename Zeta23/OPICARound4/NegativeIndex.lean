import Zeta23.OPICARound3.KernelSafeSchur

noncomputable section

namespace Zeta23.OPICARound4
open CCM OPICARound3

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- A PSD predecessor bounds every strictly negative subspace by the physical
shell dimension. This includes a zero-dimensional predecessor and singular PSD
predecessors. It does not assert that the successor is negative. -/
theorem negative_subspace_finrank_le_shell (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (hP : ∀ x : E, 0 ≤ (inner ℂ (predecessorBlock J T x) x).re)
    (N : Submodule ℂ F)
    (hN : ∀ u : N, u ≠ 0 → (inner ℂ (T u) (u : F)).re < 0) :
    Module.finrank ℂ N ≤ Module.finrank ℂ (isometricDetectorComplement J) := by
  let q : N →ₗ[ℂ] isometricDetectorComplement J :=
    (isometricDetectorComplementCoordinate J).comp N.subtype
  have hi : Function.Injective q := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    by_contra hne
    have hneg := hN u hne
    have hrec := isometricDetector_coordinate_decomposition J (u : F)
    have hcoord : (isometricDetectorComplementCoordinate J (u : F) : F) = 0 :=
      congrArg (fun z : isometricDetectorComplement J => (z : F)) hu
    rw [hcoord, add_zero] at hrec
    have hpos := hP (J.toLinearMap.adjoint (u : F))
    have heq : inner ℂ (predecessorBlock J T (J.toLinearMap.adjoint (u : F)))
        (J.toLinearMap.adjoint (u : F)) = inner ℂ (T (u : F)) (u : F) := by
      change inner ℂ (J.toLinearMap.adjoint (T (J (J.toLinearMap.adjoint (u : F)))))
        (J.toLinearMap.adjoint (u : F)) = _
      rw [inner_adjoint_isometry_left, hrec]
    rw [heq] at hpos
    linarith
  exact q.finrank_le_finrank_of_injective hi

/-- S02's upper-index conclusion requires PSD on the predecessor, rather than
being inferred from its successor. Negative existence is a separate premise. -/
theorem one_shell_negative_index_at_most_one (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (hP : ∀ x : E, 0 ≤ (inner ℂ (predecessorBlock J T x) x).re)
    (hshell : Module.finrank ℂ (isometricDetectorComplement J) = 1)
    (N : Submodule ℂ F)
    (hN : ∀ u : N, u ≠ 0 → (inner ℂ (T u) (u : F)).re < 0) :
    Module.finrank ℂ N ≤ 1 := by
  simpa only [hshell] using negative_subspace_finrank_le_shell J T hP N hN

/-- Any negative vector spans a one-dimensional strictly negative subspace.
The scaling is |c|^2 for complex c, with no unit-modulus restriction. -/
theorem negative_vector_spans_negative_line (T : F →ₗ[ℂ] F) (w : F)
    (hneg : (inner ℂ (T w) w).re < 0) :
    ∃ N : Submodule ℂ F, Module.finrank ℂ N = 1 ∧
      ∀ u : N, u ≠ 0 → (inner ℂ (T u) (u : F)).re < 0 := by
  have hw : w ≠ 0 := by
    intro hz
    simpa [hz] using hneg
  refine ⟨ℂ ∙ w, finrank_span_singleton hw, ?_⟩
  intro u hu
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp u.property
  have hc0 : c ≠ 0 := by
    intro hz
    apply hu
    apply Subtype.ext
    simpa [hz] using hc.symm
  have hscale : (inner ℂ (T (c • w)) (c • w)).re =
      Complex.normSq c * (inner ℂ (T w) w).re := by
    rw [map_smul, inner_smul_left, inner_smul_right]
    change (star c * (c * inner ℂ (T w) w)).re =
      Complex.normSq c * (inner ℂ (T w) w).re
    rw [Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im]
    ring
  change (inner ℂ (T (u : F)) (u : F)).re < 0
  rw [← hc, hscale]
  exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hc0) hneg

/-- Exact negative index one in its invariant subspace formulation. A negative
successor is explicitly required in addition to the PSD predecessor. -/
theorem one_shell_negative_index_exact (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (hP : ∀ x : E, 0 ≤ (inner ℂ (predecessorBlock J T x) x).re)
    (hshell : Module.finrank ℂ (isometricDetectorComplement J) = 1)
    (w : F) (hneg : (inner ℂ (T w) w).re < 0) :
    (∀ N : Submodule ℂ F,
      (∀ u : N, u ≠ 0 → (inner ℂ (T u) (u : F)).re < 0) → Module.finrank ℂ N ≤ 1) ∧
    ∃ N : Submodule ℂ F, Module.finrank ℂ N = 1 ∧
      ∀ u : N, u ≠ 0 → (inner ℂ (T u) (u : F)).re < 0 :=
  ⟨fun N hN => one_shell_negative_index_at_most_one J T hP hshell N hN,
    negative_vector_spans_negative_line T w hneg⟩

end Zeta23.OPICARound4
