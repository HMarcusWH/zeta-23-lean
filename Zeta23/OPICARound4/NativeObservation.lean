import Zeta23.OPICARound4.NativeWitnessCosts
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
namespace Zeta23.OPICARound4
open CCM LinearMap Set
open scoped BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- A finite Gram of the declared output map and the actual powers of T.
No extra coordinate observations, positive storage or injectivity is assumed. -/
def finiteObservationGram (T : E →ₗ[ℂ] E) (O : E →ₗ[ℂ] F) (d : ℕ) : E →ₗ[ℂ] E :=
  ∑ j ∈ Finset.range d, (O.comp (T ^ j)).adjoint.comp (O.comp (T ^ j))

theorem finiteObservationGram_energy (T : E →ₗ[ℂ] E) (O : E →ₗ[ℂ] F)
    (d : ℕ) (x : E) :
    (inner ℂ x (finiteObservationGram T O d x)).re =
      ∑ j ∈ Finset.range d, ‖O ((T ^ j) x)‖ ^ 2 := by
  simp only [finiteObservationGram, LinearMap.sum_apply, inner_sum,
    LinearMap.comp_apply, Complex.re_sum, LinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K, Complex.ofReal_re]
  apply Finset.sum_congr rfl
  intro j hj
  norm_cast

theorem finiteObservationGram_nonnegative (T : E →ₗ[ℂ] E) (O : E →ₗ[ℂ] F)
    (d : ℕ) (x : E) : 0 ≤ (inner ℂ x (finiteObservationGram T O d x)).re := by
  rw [finiteObservationGram_energy]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem finiteObservationGram_kernel_iff (T : E →ₗ[ℂ] E) (O : E →ₗ[ℂ] F)
    (d : ℕ) (x : E) :
    finiteObservationGram T O d x = 0 ↔ ∀ j < d, O ((T ^ j) x) = 0 := by
  constructor
  · intro h j hj
    have hz : ∑ k ∈ Finset.range d, ‖O ((T ^ k) x)‖ ^ 2 = 0 := by
      rw [← finiteObservationGram_energy, h, inner_zero_right, Complex.zero_re]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k (_ : k ∈ Finset.range d) => sq_nonneg ‖O ((T ^ k) x)‖)).mp hz
    have hh := hall j (Finset.mem_range.mpr hj)
    exact norm_eq_zero.mp ((sq_eq_zero_iff).mp hh)
  · intro h
    simp only [finiteObservationGram, LinearMap.sum_apply, LinearMap.comp_apply]
    apply Finset.sum_eq_zero
    intro j hj
    rw [h j (Finset.mem_range.mp hj), map_zero]

/-- The full unseen subspace is invariant. A short finite Gram represents only
its declared prefix unless stabilization has separately been established. -/
def observationBlindSubspace (T : E →ₗ[ℂ] E) (O : E →ₗ[ℂ] F) : Submodule ℂ E :=
  ⨅ j : ℕ, LinearMap.ker (O.comp (T ^ j))

theorem observationBlindSubspace_mem (T : E →ₗ[ℂ] E) (O : E →ₗ[ℂ] F) (x : E) :
    x ∈ observationBlindSubspace T O ↔ ∀ j : ℕ, O ((T ^ j) x) = 0 := by
  simp [observationBlindSubspace, Submodule.mem_iInf, LinearMap.mem_ker]

theorem observationBlindSubspace_invariant (T : E →ₗ[ℂ] E) (O : E →ₗ[ℂ] F)
    (x : E) (hx : x ∈ observationBlindSubspace T O) :
    T x ∈ observationBlindSubspace T O := by
  rw [observationBlindSubspace_mem] at hx ⊢
  intro j
  simpa only [pow_succ, Module.End.mul_apply] using hx (j + 1)

theorem blind_vector_in_every_finite_gram_kernel (T : E →ₗ[ℂ] E)
    (O : E →ₗ[ℂ] F) (x : E) (hx : x ∈ observationBlindSubspace T O) (d : ℕ) :
    finiteObservationGram T O d x = 0 :=
  (finiteObservationGram_kernel_iff T O d x).mpr
    (fun j _ => (observationBlindSubspace_mem T O x).mp hx j)

/-- Iterating one scalar channel cannot recover an eigenmode it annihilates. -/
theorem eigenmode_invisible_at_all_powers (T : E →ₗ[ℂ] E) (O : E →ₗ[ℂ] F)
    (x : E) (lam : ℂ) (hx : T x = lam • x) (ho : O x = 0) :
    x ∈ observationBlindSubspace T O := by
  rw [observationBlindSubspace_mem]
  have hpow (j : ℕ) : (T ^ j) x = lam ^ j • x := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, ← mul_smul, pow_succ']
      rw [mul_comm (lam ^ j) lam]
  intro j
  rw [hpow, map_smul, ho, smul_zero]

/-- Input reachability is a separate object from output observability. -/
def finiteInputReachableSubspace {ι : Type*} (T : E →ₗ[ℂ] E)
    (g : ι → E) (d : ℕ) : Submodule ℂ E :=
  Submodule.span ℂ {x | ∃ j < d, ∃ i : ι, (T ^ j) (g i) = x}

theorem reachable_subspace_in_output_kernel {ι : Type*} (T : E →ₗ[ℂ] E)
    (O : E →ₗ[ℂ] F) (g : ι → E) (d : ℕ)
    (h : ∀ j < d, ∀ i, O ((T ^ j) (g i)) = 0) :
    finiteInputReachableSubspace T g d ≤ LinearMap.ker O := by
  apply Submodule.span_le.mpr
  rintro x ⟨j, hj, i, rfl⟩
  exact h j hj i

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-- Reviewed native channels: the actual corrected source in the even carrier
and actual cubic pairing in the odd carrier. More channels need their own
source identity and a mathematical consumer before registration. -/
def nativeEvenObservation (L : ℝ) (K : ℕ) : poleNeutralEvenSubspace L K →ₗ[ℂ] ℂ :=
  poleNeutralCorrectedCubicFunctional L K

def nativeOddObservation (L : ℝ) (K : ℕ) : poleNeutralOddSubspace L K →ₗ[ℂ] ℂ :=
  poleNeutralCubicPairingFunctional L K

theorem native_even_invisible_gram {L : ℝ} (K : ℕ) (u : poleNeutralEvenSubspace L K)
    (lam : ℂ) (hu : poleNeutralEvenCompressedCanonical L K u = lam • u)
    (hf : poleNeutralCorrectedCubicSource L K u = 0) (d : ℕ) :
    finiteObservationGram (poleNeutralEvenCompressedCanonical L K)
      (nativeEvenObservation L K) d u = 0 := by
  apply blind_vector_in_every_finite_gram_kernel
  apply eigenmode_invisible_at_all_powers _ _ u lam hu
  exact hf

theorem native_odd_invisible_gram {L : ℝ} (K : ℕ) (u : poleNeutralOddSubspace L K)
    (lam : ℂ) (hu : poleNeutralOddCompressedCanonical L K u = lam • u)
    (hf : poleNeutralCubicPairingFunctional L K u = 0) (d : ℕ) :
    finiteObservationGram (poleNeutralOddCompressedCanonical L K)
      (nativeOddObservation L K) d u = 0 := by
  apply blind_vector_in_every_finite_gram_kernel
  exact eigenmode_invisible_at_all_powers _ _ u lam hu hf

/-- OPEN source-specific quantitative target. Positivity of its constant and
the same actual negative state are required before any visibility deduction. -/
def NativeNegativeObservationBound (L : ℝ) (K : ℕ) (c : ℝ) : Prop :=
  0 < c ∧
  (∀ (u : poleNeutralEvenSubspace L K) (lam : ℝ), lam < 0 →
    poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u →
      c * ‖u‖ ≤ ‖nativeEvenObservation L K u‖) ∧
  (∀ (u : poleNeutralOddSubspace L K) (lam : ℝ), lam < 0 →
    poleNeutralOddCompressedCanonical L K u = (lam : ℂ) • u →
      c * ‖u‖ ≤ ‖nativeOddObservation L K u‖)

theorem native_observation_bound_excludes_invisible_even {L : ℝ} {K : ℕ} {c : ℝ}
    (h : NativeNegativeObservationBound L K c) (u : poleNeutralEvenSubspace L K)
    (hu : u ≠ 0) (lam : ℝ) (hlam : lam < 0)
    (he : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :
    nativeEvenObservation L K u ≠ 0 := by
  intro hz
  have hb := h.2.1 u lam hlam he
  rw [hz, norm_zero] at hb
  exact (not_le_of_gt (mul_pos h.1 (norm_pos_iff.mpr hu))) hb

end Zeta23.OPICARound4
