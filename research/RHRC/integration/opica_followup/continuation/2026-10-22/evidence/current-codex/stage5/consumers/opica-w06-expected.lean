import Zeta23.OPICAFollowup.WeightedMixing
open MeasureTheory
namespace Zeta23.OPICAFollowup.W06Independent
theorem expected_log_weight (t : ℝ) :
    Zeta23.OPICAFollowup.positiveLogWeight (Real.exp t) =
      Real.exp (-t / 2) :=
  Zeta23.OPICAFollowup.positiveLogWeight_exp t
theorem expected_complex_pullback (f : ℝ → ℂ) (t : ℝ) :
    Zeta23.OPICAFollowup.weightedPositiveLogTest f (Real.exp t) =
      (Real.exp (-t / 2) : ℂ) * f t :=
  Zeta23.OPICAFollowup.weightedPositiveLogTest_exp f t
theorem expected_origin_excluded (f : ℝ → ℂ) {x : ℝ} (hx : x ≤ 0) :
    Zeta23.OPICAFollowup.weightedPositiveLogTest f x = 0 :=
  Zeta23.OPICAFollowup.weightedPositiveLogTest_nonpos f hx
theorem expected_physical_integer_dilation
    (f : ℝ → ℂ) (t : ℝ) (n : ℕ) (hn : 0 < n) :
    Zeta23.OPICAFollowup.weightedPositiveLogTest f (Real.exp t * (n : ℝ)) =
      ((Real.exp (-t / 2) / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
        f (t + Real.log (n : ℝ)) :=
  Zeta23.OPICAFollowup.weightedPositiveLogTest_at_dilatedNat f t n hn
theorem expected_log_measure_add (mu nu : Measure ℝ) :
    Zeta23.OPICAFollowup.positiveLogMeasure (mu + nu) =
      Zeta23.OPICAFollowup.positiveLogMeasure mu +
      Zeta23.OPICAFollowup.positiveLogMeasure nu :=
  Zeta23.OPICAFollowup.positiveLogMeasure_add mu nu
theorem expected_log_measure_zero :
    Zeta23.OPICAFollowup.positiveLogMeasure (0 : Measure ℝ) = 0 :=
  Zeta23.OPICAFollowup.positiveLogMeasure_zero
#print axioms Zeta23.OPICAFollowup.W06Independent.expected_log_measure_add
#print axioms Zeta23.OPICAFollowup.W06Independent.expected_log_measure_zero
theorem expected_finite_logarithmic_additivity {ι : Type*}
    (s : Finset ι) (mu : ι → Measure ℝ) :
    Zeta23.OPICAFollowup.positiveLogMeasure (∑ i ∈ s, mu i) =
      ∑ i ∈ s, Zeta23.OPICAFollowup.positiveLogMeasure (mu i) :=
  Zeta23.OPICAFollowup.positiveLogMeasure_finset_sum s mu
theorem expected_finite_integer_atoms
    (t : ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 0 < n) :
    Zeta23.OPICAFollowup.positiveLogMeasure
      (∑ n ∈ s, Measure.dirac (Real.exp t * (n : ℝ))) =
      ∑ n ∈ s,
        ENNReal.ofReal (Real.exp (-t / 2) / Real.sqrt (n : ℝ)) •
          Measure.dirac (t + Real.log (n : ℝ)) :=
  Zeta23.OPICAFollowup.positiveLogMeasure_finite_integer_lattice t s hs
theorem expected_countable_log_measure_sum {ι : Type*}
    (mu : ι → Measure ℝ) :
    Zeta23.OPICAFollowup.positiveLogMeasure (Measure.sum mu) =
      Measure.sum (fun i =>
        Zeta23.OPICAFollowup.positiveLogMeasure (mu i)) :=
  Zeta23.OPICAFollowup.positiveLogMeasure_sum mu
theorem expected_all_positive_integer_atoms (t : ℝ) :
    Zeta23.OPICAFollowup.positiveLogMeasure
      (Zeta23.OPICAFollowup.positiveIntegerLatticeInput t) =
      Measure.sum (fun n : ℕ =>
        ENNReal.ofReal (Real.exp (-t / 2) /
          Real.sqrt (((n + 1 : ℕ) : ℝ))) •
        Measure.dirac (t + Real.log (((n + 1 : ℕ) : ℝ)))) :=
  Zeta23.OPICAFollowup.positiveLogMeasure_integerLattice t
#print axioms Zeta23.OPICAFollowup.W06Independent.expected_countable_log_measure_sum
#print axioms Zeta23.OPICAFollowup.W06Independent.expected_all_positive_integer_atoms
#print axioms Zeta23.OPICAFollowup.W06Independent.expected_finite_logarithmic_additivity
#print axioms Zeta23.OPICAFollowup.W06Independent.expected_finite_integer_atoms
#print axioms Zeta23.OPICAFollowup.W06Independent.expected_log_weight
#print axioms Zeta23.OPICAFollowup.W06Independent.expected_complex_pullback
#print axioms Zeta23.OPICAFollowup.W06Independent.expected_origin_excluded
theorem expected_weighted_log_dirac (t : ℝ) :
    Zeta23.OPICAFollowup.positiveLogMeasure (Measure.dirac (Real.exp t)) =
      ENNReal.ofReal (Real.exp (-t / 2)) • Measure.dirac t :=
  Zeta23.OPICAFollowup.positiveLogMeasure_dirac t
#print axioms Zeta23.OPICAFollowup.W06Independent.expected_weighted_log_dirac
theorem expected_log_nonpositive_atom {x : ℝ} (hx : x ≤ 0) :
    Zeta23.OPICAFollowup.positiveLogMeasure (Measure.dirac x) = 0 :=
  Zeta23.OPICAFollowup.positiveLogMeasure_dirac_nonpos hx
theorem expected_log_positive_atom {x : ℝ} (hx : 0 < x) :
    Zeta23.OPICAFollowup.positiveLogMeasure (Measure.dirac x) =
      ENNReal.ofReal (Zeta23.OPICAFollowup.positiveLogWeight x) •
        (Measure.dirac (Real.log x)) :=
  Zeta23.OPICAFollowup.positiveLogMeasure_dirac_pos hx
#print axioms Zeta23.OPICAFollowup.W06Independent.expected_log_nonpositive_atom
#print axioms Zeta23.OPICAFollowup.W06Independent.expected_log_positive_atom
theorem expected_weighted_integer_atom (t : ℝ) (n : ℕ) (hn : 0 < n) :
    Zeta23.OPICAFollowup.positiveLogMeasure
      (Measure.dirac (Real.exp t * (n : ℝ))) =
    ENNReal.ofReal (Real.exp (-t / 2) / Real.sqrt (n : ℝ)) •
      Measure.dirac (t + Real.log (n : ℝ)) :=
  Zeta23.OPICAFollowup.positiveLogMeasure_dilatedNat_dirac t n hn
#print axioms Zeta23.OPICAFollowup.W06Independent.expected_weighted_integer_atom
#print axioms Zeta23.OPICAFollowup.W06Independent.expected_physical_integer_dilation
end Zeta23.OPICAFollowup.W06Independent
