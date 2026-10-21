import Zeta23.OPICA.LocalObstruction
import Mathlib.Algebra.BigOperators.Intervals

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Zeta23.OPICA

def localAffineIterate (f : ℂ → ℂ) (M B : ℕ → ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => f
  | n + 1 => fun z => M n z * localAffineIterate f M B n z + B n z

def localAffineCorrection (M B : ℕ → ℂ → ℂ) : ℕ → ℂ → ℂ :=
  localAffineIterate 0 M B

theorem affine_transport_corrected_eq (f : ℂ → ℂ) (M B : ℕ → ℂ → ℂ)
    (n : ℕ) (z : ℂ) :
    localAffineIterate f M B n z - localAffineCorrection M B n z =
      (∏ i ∈ Finset.range n, M i z) * f z := by
  induction n with
  | zero => simp [localAffineIterate, localAffineCorrection]
  | succ n ih =>
    simp only [localAffineIterate, localAffineCorrection, Finset.prod_range_succ] at *
    linear_combination M n z * ih

theorem affine_correction_expansion (M B : ℕ → ℂ → ℂ) (n : ℕ) (z : ℂ) :
    localAffineCorrection M B n z =
      ∑ j ∈ Finset.range n, (∏ i ∈ Finset.Ico (j + 1) n, M i z) * B j z := by
  induction n with
  | zero => simp [localAffineCorrection, localAffineIterate]
  | succ n ih =>
    simp only [localAffineCorrection, localAffineIterate] at ih ⊢
    rw [ih, Finset.sum_range_succ]
    simp only [Finset.Ico_self, Finset.prod_empty, one_mul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.prod_Ico_succ_top (by simpa using Finset.mem_range.mp hj)]
    ring

theorem affine_correction_analytic (center : ℂ) (M B : ℕ → ℂ → ℂ)
    (hM : ∀ i, AnalyticAt ℂ (M i) center)
    (hB : ∀ i, AnalyticAt ℂ (B i) center) (n : ℕ) :
    AnalyticAt ℂ (localAffineCorrection M B n) center := by
  induction n with
  | zero => exact analyticAt_const
  | succ n ih => exact ((hM n).mul ih).add (hB n)

theorem affine_transport_leading_jet {Source : Type*} (s : SimplePoleData Source)
    (m : ℕ → MultiplierOrderData s.center) (B : ℕ → ℂ → ℂ) (n : ℕ)
    (horder : 0 < (MultiplierOrderData.prod m n).order) :
    (fun z => localAffineIterate s.field (fun i => (m i).multiplier) B n z -
        localAffineCorrection (fun i => (m i).multiplier) B n z)
        =ᶠ[𝓝[≠] s.center] s.regularRepresentative (MultiplierOrderData.prod m n) ∧
      analyticOrderAt (s.regularRepresentative (MultiplierOrderData.prod m n)) s.center =
        ((∑ i ∈ Finset.range n, (m i).order) - 1 : ℕ) ∧
      iteratedDeriv ((MultiplierOrderData.prod m n).order - 1)
        (s.regularRepresentative (MultiplierOrderData.prod m n)) s.center =
        ((MultiplierOrderData.prod m n).order - 1).factorial *
          (MultiplierOrderData.prod m n).unit s.center * s.residue := by
  refine ⟨?_, ?_, completion_leading_jet s (MultiplierOrderData.prod m n)⟩
  · filter_upwards [completion_agrees_punctured s (MultiplierOrderData.prod m n) horder]
      with z hz
    rw [affine_transport_corrected_eq, ← multiplier_prod_value]
    exact hz
  · rw [← multiplier_prod_order]
    exact completion_order s (MultiplierOrderData.prod m n)

theorem affine_transport_unit_residue {Source : Type*} (s : SimplePoleData Source)
    (m : ℕ → MultiplierOrderData s.center) (B : ℕ → ℂ → ℂ) (n : ℕ)
    (horder : (MultiplierOrderData.prod m n).order = 0) :
    Tendsto (fun z => (z - s.center) *
      (localAffineIterate s.field (fun i => (m i).multiplier) B n z -
        localAffineCorrection (fun i => (m i).multiplier) B n z))
      (𝓝[≠] s.center) (𝓝 ((MultiplierOrderData.prod m n).unit s.center * s.residue)) := by
  simpa only [affine_transport_corrected_eq, ← multiplier_prod_value] using
    unit_mul_simplePole_residue s (MultiplierOrderData.prod m n) horder

/-- An analytic background can exactly cancel the completed image of a pole. -/
theorem affine_completion_cancellation (z : ℂ) (hz : z ≠ 0) :
    z * ((1 : ℂ) / z) + (-1) = 0 := by
  field_simp
  norm_num

end Zeta23.OPICA
