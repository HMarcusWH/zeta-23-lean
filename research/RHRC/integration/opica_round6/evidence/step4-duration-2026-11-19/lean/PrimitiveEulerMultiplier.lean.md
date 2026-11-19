# Historical source for PrimitiveEulerMultiplier

Recorded source SHA-256 is `f5e5e27b7e12b4e24f37020cf9a044bcec0bc550d2635b0bee14bfdd662f489c`.

```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The finite multiplier for the primitive-direction graph at any real frequency. -/

namespace Step4.PrimitiveEuler

noncomputable section

def cosineFactor (q ξ : ℝ) : ℝ :=
  1 - 2 * Real.sqrt q / (q + 1) * Real.cos (ξ * Real.log q)

theorem cosineFactor_pos {q : ℝ} (hq : 1 < q) (ξ : ℝ) : 0 < cosineFactor q ξ := by
  have hq0 : 0 < q := by linarith
  have hs : 1 < Real.sqrt q := by
    simpa using Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num) hq
  have hstrict : 2 * Real.sqrt q < q + 1 := by
    nlinarith [Real.sq_sqrt hq0.le, sq_pos_of_pos (sub_pos.mpr hs)]
  have hden : 0 < q+1 := by linarith
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one (ξ * Real.log q))
    (show 0 ≤ 2 * Real.sqrt q / (q+1) by positivity)
  unfold cosineFactor
  linarith [(div_lt_one hden).mpr hstrict]

theorem cosineFactor_eq_euler {q : ℝ} (hq : 1 < q) (ξ : ℝ) :
    cosineFactor q ξ = ‖1 - (q : ℂ) ^ (-(1/2 : ℂ) - (ξ : ℂ)*Complex.I)‖ ^ 2 / (1 + 1/q) := by
  have hq0 : 0 < q := by linarith
  have hqn : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq0.ne'
  let e : ℂ := ⟨-(1/2 : ℝ), -ξ⟩
  have he : -(1/2 : ℂ) - (ξ : ℂ)*Complex.I = e := by
    apply Complex.ext <;> norm_num [e, Complex.mul_re, Complex.mul_im]
  rw [he]
  let z : ℂ := (q : ℂ)^e
  have hnorm : ‖z‖ = (Real.sqrt q)⁻¹ := by
    rw [show ‖z‖ = q ^ e.re from Complex.norm_cpow_eq_rpow_re_of_pos hq0 e]
    change q ^ (-(1/2 : ℝ)) = _
    rw [Real.rpow_neg hq0.le, ← Real.sqrt_eq_rpow]
  have hre : z.re = (Real.sqrt q)⁻¹ * Real.cos (ξ * Real.log q) := by
    dsimp only [z]
    rw [Complex.cpow_def_of_ne_zero hqn, ← Complex.ofReal_log hq0.le, Complex.exp_re]
    simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    change Real.exp (Real.log q * (-(1/2 : ℝ))) * Real.cos (Real.log q * -ξ) = _
    rw [← Real.rpow_def_of_pos hq0, Real.rpow_neg hq0.le, ← Real.sqrt_eq_rpow,
      mul_neg, Real.cos_neg, mul_comm (Real.log q) ξ]
  have hsq : ‖1-z‖^2 = 1+((Real.sqrt q)⁻¹)^2-2*((Real.sqrt q)⁻¹ * Real.cos (ξ*Real.log q)) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp [Complex.normSq_eq_norm_sq, hnorm, hre]
  change cosineFactor q ξ = ‖1-z‖^2 / (1 + 1/q)
  rw [hsq]
  unfold cosineFactor
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have normalize (s c : ℝ) (hs : 0 < s) :
      1 - 2*s/(s^2+1)*c = (1 + s⁻¹^2 - 2*(s⁻¹*c))/(1+1/s^2) := by
    field_simp
  simpa only [Real.sq_sqrt hq0.le] using normalize (Real.sqrt q) (Real.cos (ξ*Real.log q)) hs0

theorem finite_primitive_euler_identity_and_pos {ι : Type*} (A : Finset ι) (q : ι → ℝ)
    (hq : ∀ i ∈ A, 1 < q i) (ξ : ℝ) :
    (∏ i ∈ A, cosineFactor (q i) ξ) =
      (∏ i ∈ A, ‖1 - (q i : ℂ) ^ (-(1/2 : ℂ) - (ξ : ℂ)*Complex.I)‖ ^ 2 / (1 + 1/q i)) ∧
    0 < ∏ i ∈ A, cosineFactor (q i) ξ := by
  exact ⟨Finset.prod_congr rfl fun i hi => cosineFactor_eq_euler (hq i hi) ξ,
    Finset.prod_pos fun i hi => cosineFactor_pos (hq i hi) ξ⟩

#check finite_primitive_euler_identity_and_pos
#print axioms cosineFactor_pos
#print axioms cosineFactor_eq_euler
#print axioms finite_primitive_euler_identity_and_pos

end
end Step4.PrimitiveEuler
```
