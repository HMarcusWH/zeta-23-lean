import Zeta23.OPICARound2.NativeJumpControls

noncomputable section
open Set MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace Zeta23.OPICARound2.Validation

theorem gain_actual_arch_source (t : ℝ) :
    CCM.archDensity t = Real.exp (t/2)/(Real.exp t-Real.exp (-t)) := rfl

theorem gain_actual_line_atom (a : ℝ) (I J : Set ℝ) :
    nativeJumpOverlap a I J = volume.real {y : ℝ | y∈J ∧ y+a∈I} := rfl

theorem gain_actual_source_rectangle (R : ℝ) (I J : Set ℝ) :
    nativeJumpGainRectangle R I J =
      (∫ p : ℝ×ℝ in I ×ˢ J, CCM.archDensity |p.1-p.2|) +
      ∑ n∈Finset.Icc 2 ⌊Real.exp R⌋₊, (Λ n/Real.sqrt n : ℝ)*
        (volume.real {y : ℝ | y∈J ∧ y+Real.log n∈I} +
          volume.real {y : ℝ | y∈J ∧ y-Real.log n∈I}) := by
  simp only [nativeJumpGainRectangle,nativeJumpArchRectangle,nativeJumpOverlap,sub_eq_add_neg]

theorem gain_expected_ordering :
    (∀ x∈nativeJumpRow 0, ∀ y∈nativeJumpRow 1, x<y) ∧
    (∀ x∈nativeJumpColumn 0, ∀ y∈nativeJumpColumn 1, x<y) :=
  native_jump_rows_and_columns_ordered

theorem gain_expected_singular_diagonal_avoided (i j : Fin 2)
    (x y : ℝ) (hx : x∈nativeJumpRow i) (hy : y∈nativeJumpColumn j) :
    0≤y ∧ y<x ∧ (1/2:ℝ)<x-y ∧ x-y<1 ∧ x<1 :=
  native_jump_rectangle_geometry i j hx hy

theorem gain_expected_only_prime_two (R : ℝ) (hR : 1≤R) (i j : Fin 2) :
    nativeJumpGainRectangle R (nativeJumpRow i) (nativeJumpColumn j)=
      nativeJumpArchRectangle (nativeJumpRow i) (nativeJumpColumn j) +
        if i=0 ∧ j=1 then Real.log 2 / Real.sqrt 2 * (1/1000:ℝ) else 0 :=
  native_jump_gain_rectangle_identity R hR i j

theorem gain_expected_area_bounds (i j : Fin 2) :
    (1/1000:ℝ)^2/2<nativeJumpArchRectangle (nativeJumpRow i) (nativeJumpColumn j) ∧
      nativeJumpArchRectangle (nativeJumpRow i) (nativeJumpColumn j)<2*(1/1000:ℝ)^2 :=
  native_jump_arch_rectangle_bounds i j

theorem gain_expected_negative_minor (R : ℝ) (hR : 1≤R) :
    nativeJumpGainRectangle R (nativeJumpRow 0) (nativeJumpColumn 0)*
      nativeJumpGainRectangle R (nativeJumpRow 1) (nativeJumpColumn 1) -
    nativeJumpGainRectangle R (nativeJumpRow 0) (nativeJumpColumn 1)*
      nativeJumpGainRectangle R (nativeJumpRow 1) (nativeJumpColumn 0)
        < -(61/375000000000:ℝ) :=
  native_jump_gain_negative_ordered_minor R hR

#print axioms Zeta23.OPICARound2.native_jump_gain_negative_ordered_minor
#print axioms Zeta23.OPICARound2.Validation.gain_expected_negative_minor

theorem gain_expected_smooth_test_properties :
    (∀ i : Fin 2, ContDiff ℝ (⊤:ℕ∞) (nativeJumpRowTest i) ∧
      HasCompactSupport (nativeJumpRowTest i) ∧
      tsupport (nativeJumpRowTest i) ⊆ nativeJumpRow i ∧
      ∀ x : ℝ, 0≤nativeJumpRowTest i x ∧ nativeJumpRowTest i x≤1) ∧
    (∀ j : Fin 2, ContDiff ℝ (⊤:ℕ∞) (nativeJumpColumnTest j) ∧
      HasCompactSupport (nativeJumpColumnTest j) ∧
      tsupport (nativeJumpColumnTest j) ⊆ nativeJumpColumn j ∧
      ∀ y : ℝ, 0≤nativeJumpColumnTest j y ∧ nativeJumpColumnTest j y≤1) :=
  native_jump_smooth_tests

theorem gain_actual_smooth_source (R : ℝ) (i j : Fin 2) :
    nativeJumpSmoothGain R i j =
      (∫ p : ℝ×ℝ, CCM.archDensity |p.1-p.2| *
        (nativeJumpRowTest i p.1*nativeJumpColumnTest j p.2)) +
      ∑ n∈Finset.Icc 2 ⌊Real.exp R⌋₊, (Λ n/Real.sqrt n : ℝ)*
        ((∫ y : ℝ, nativeJumpRowTest i (y+Real.log n)*nativeJumpColumnTest j y) +
          (∫ y : ℝ, nativeJumpRowTest i (y-Real.log n)*nativeJumpColumnTest j y)) := by
  simp only [nativeJumpSmoothGain,native_jump_smooth_arch_full,
    native_jump_smooth_line_full,sub_eq_add_neg]

theorem gain_expected_smooth_negative_minor (R : ℝ) (hR : 1≤R) :
    nativeJumpSmoothGain R 0 0*nativeJumpSmoothGain R 1 1-
      nativeJumpSmoothGain R 0 1*nativeJumpSmoothGain R 1 0<0 :=
  native_jump_smooth_negative_ordered_minor R hR

#print axioms Zeta23.OPICARound2.native_jump_smooth_negative_ordered_minor
#print axioms Zeta23.OPICARound2.Validation.gain_expected_smooth_negative_minor

end Zeta23.OPICARound2.Validation
