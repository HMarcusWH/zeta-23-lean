import Zeta23.CCM.SourceFourierConvolution
import Zeta23.CCM.SourceSignCountermodels
import Zeta23.CCM.ConstrainedParityGeometry

noncomputable section

namespace Zeta23.CCM

open Matrix Finset
open scoped BigOperators ComplexConjugate

/-!
# POST284 follow-up M47: exact `K = 2` legal odd source negativity (Steps 85, 87)

For `K = 2` the legal odd carrier is the line spanned by
`u₀ = (-1, 2, 0, -2, 1)` (`oddSourceWitnessK2`, indices `-2..2`).  Its sine
profile is `T(t) = 4 sin t (cos t - 1)`, its cosine profile vanishes, and

* `e_{u₀}(ω) = -(1/π) ∫₀^{2πω} T(t) T(2πω - t) dt`, so `e_{u₀}(ω) < 0` for
  `0 < ω ≤ 1/2` (both factors negative on `(0, π)`);
* `e_{u₀}(ω) = (1/(3π)) [6a (4 cos a + cos 2a) + 8 sin a - 19 sin 2a]`,
  `a = 2πω`, and every summand is nonpositive (the first strictly negative)
  for `1/2 ≤ ω ≤ 3/4`.

Hence `Re e_u(ω) < 0` for every nonzero legal odd `u` and `0 < ω ≤ 3/4`, and
`Re e_{Dz}(ω) < 0` for every nonzero legal even `z` (with `(Dz)_n = n z_n`).

Regression edges: `e = 0` at `ω = 0`; `e_{u₀}(1) = 20 > 0`, so the interval
cannot be extended to `ω = 1`.  This is an elementary *source* theorem for the
single dimension `K = 2`; it is not a sign of the canonical arithmetic test and
does not generalize to `K ≥ 3` (see the exact parity inertia theorems).
-/

/-- The `K = 2` odd sine profile `T(t) = 4 sin t (cos t - 1)`. -/
def k2OddProfile (t : ℝ) : ℝ := 4 * Real.sin t * (Real.cos t - 1)

theorem k2OddProfile_neg {t : ℝ} (ht0 : 0 < t) (htπ : t < Real.pi) : k2OddProfile t < 0 := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 htπ
  have hc : Real.cos t < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl htπ.le ht0
    rwa [Real.cos_zero] at this
  unfold k2OddProfile
  nlinarith

theorem continuous_k2OddProfile : Continuous k2OddProfile := by
  unfold k2OddProfile
  fun_prop

theorem oddSourceWitnessK2_cosProfile (t : ℝ) :
    sourceCosProfile 2 oddSourceWitnessK2 t = 0 := by
  simp [sourceCosProfile, Fin.sum_univ_succ, oddSourceWitnessK2, centeredIndex]
  norm_num [Complex.cos_neg]

theorem oddSourceWitnessK2_sinProfile (t : ℝ) :
    sourceSinProfile 2 oddSourceWitnessK2 t = (k2OddProfile t : ℂ) := by
  simp [sourceSinProfile, Fin.sum_univ_succ, oddSourceWitnessK2, centeredIndex, k2OddProfile]
  norm_num [Complex.sin_neg, Complex.sin_two_mul]
  ring

/-- Convolution form of the `K = 2` odd source energy. -/
theorem quadraticForm_oddSourceWitnessK2_eq_integral (ω : ℝ) :
    quadraticForm (sourceMatrix ω 2) oddSourceWitnessK2 =
      ((-(1 / Real.pi) *
          ∫ t in (0 : ℝ)..(2 * Real.pi * ω),
            k2OddProfile t * k2OddProfile (2 * Real.pi * ω - t) : ℝ) : ℂ) := by
  rw [quadraticForm_sourceMatrix_eq_convolution]
  have hint : ∀ t : ℝ,
      (conj (sourceCosProfile 2 oddSourceWitnessK2 t) *
          sourceCosProfile 2 oddSourceWitnessK2 (2 * Real.pi * ω - t) -
        conj (sourceSinProfile 2 oddSourceWitnessK2 t) *
          sourceSinProfile 2 oddSourceWitnessK2 (2 * Real.pi * ω - t)) =
        ((-(k2OddProfile t * k2OddProfile (2 * Real.pi * ω - t)) : ℝ) : ℂ) := by
    intro t
    rw [oddSourceWitnessK2_cosProfile, oddSourceWitnessK2_cosProfile,
      oddSourceWitnessK2_sinProfile, oddSourceWitnessK2_sinProfile, Complex.conj_ofReal]
    push_cast
    ring
  simp_rw [hint]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_neg]
  push_cast
  ring

/-- Explicit trigonometric form, `a = 2πω`. -/
theorem quadraticForm_oddSourceWitnessK2 (ω : ℝ) :
    quadraticForm (sourceMatrix ω 2) oddSourceWitnessK2 =
      (((1 / (3 * Real.pi)) * (6 * (2 * Real.pi * ω) * (4 * Real.cos (2 * Real.pi * ω) +
        Real.cos (2 * (2 * Real.pi * ω))) + 8 * Real.sin (2 * Real.pi * ω) -
          19 * Real.sin (2 * (2 * Real.pi * ω))) : ℝ) : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [quadraticForm, Fin.sum_univ_succ, oddSourceWitnessK2, centeredIndex, sourceEntry_of_ne,
    sourcePotential, sourceDiagonal, Complex.conj_ofNat]
  rw [show (2 : ℂ) * ↑Real.pi * 2 * ↑ω = 2 * (2 * ↑Real.pi * ↑ω) by ring]
  field_simp
  ring

/-- Negativity on `0 < ω ≤ 1/2` from the convolution form. -/
theorem re_quadraticForm_oddSourceWitnessK2_neg_of_le_half {ω : ℝ} (h0 : 0 < ω)
    (h1 : ω ≤ 1 / 2) :
    (quadraticForm (sourceMatrix ω 2) oddSourceWitnessK2).re < 0 := by
  rw [quadraticForm_oddSourceWitnessK2_eq_integral, Complex.ofReal_re]
  set a := 2 * Real.pi * ω with ha
  have hpi := Real.pi_pos
  have ha0 : 0 < a := by positivity
  have haπ : a ≤ Real.pi := by rw [ha]; nlinarith
  have hpos : 0 < ∫ t in (0 : ℝ)..a, k2OddProfile t * k2OddProfile (a - t) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact (continuous_k2OddProfile.mul
        (continuous_k2OddProfile.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _
    · intro t ht
      exact mul_pos_of_neg_of_neg (k2OddProfile_neg ht.1 (by linarith [ht.2]))
        (k2OddProfile_neg (by linarith [ht.2]) (by linarith [ht.1]))
    · exact ha0
  have : 0 < 1 / Real.pi := by positivity
  nlinarith

/-- Negativity on `1/2 ≤ ω ≤ 3/4` from the explicit trigonometric form. -/
theorem re_quadraticForm_oddSourceWitnessK2_neg_of_half_le {ω : ℝ} (h1 : 1 / 2 ≤ ω)
    (h3 : ω ≤ 3 / 4) :
    (quadraticForm (sourceMatrix ω 2) oddSourceWitnessK2).re < 0 := by
  rw [quadraticForm_oddSourceWitnessK2, Complex.ofReal_re]
  set a := 2 * Real.pi * ω with ha
  have hpi := Real.pi_pos
  have haπ : Real.pi ≤ a := by rw [ha]; nlinarith
  have ha3 : a ≤ Real.pi + Real.pi / 2 := by rw [ha]; nlinarith
  have hcos : Real.cos a ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) ha3
  have hcos1 : -1 ≤ Real.cos a := Real.neg_one_le_cos a
  have hsin : Real.sin a ≤ 0 := by
    have h := Real.sin_nonneg_of_nonneg_of_le_pi (x := a - Real.pi) (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at h
    linarith
  have hX : 4 * Real.cos a + Real.cos (2 * a) ≤ -1 := by
    rw [Real.cos_two_mul]
    nlinarith
  have hs2 : 0 ≤ Real.sin (2 * a) := by
    rw [Real.sin_two_mul]
    nlinarith
  have hinner : 6 * a * (4 * Real.cos a + Real.cos (2 * a)) + 8 * Real.sin a -
      19 * Real.sin (2 * a) < 0 := by
    have : 6 * a * (4 * Real.cos a + Real.cos (2 * a)) ≤ 6 * a * (-1) :=
      mul_le_mul_of_nonneg_left hX (by positivity)
    nlinarith
  have hc : 0 < 1 / (3 * Real.pi) := by positivity
  exact mul_neg_of_pos_of_neg hc hinner

/-- **`K = 2` odd generator negativity** on `0 < ω ≤ 3/4`. -/
theorem re_quadraticForm_oddSourceWitnessK2_neg {ω : ℝ} (h0 : 0 < ω) (h3 : ω ≤ 3 / 4) :
    (quadraticForm (sourceMatrix ω 2) oddSourceWitnessK2).re < 0 := by
  rcases le_or_gt ω (1 / 2) with h | h
  · exact re_quadraticForm_oddSourceWitnessK2_neg_of_le_half h0 h
  · exact re_quadraticForm_oddSourceWitnessK2_neg_of_half_le h.le h3

/-- Regression edge `ω = 1`: `e_{u₀}(1) = 2 ‖u₀‖² = 20 > 0`. -/
theorem quadraticForm_oddSourceWitnessK2_one :
    quadraticForm (sourceMatrix 1 2) oddSourceWitnessK2 = 20 := by
  rw [sourceMatrix_one, quadraticForm]
  simp [Fin.sum_univ_succ, oddSourceWitnessK2, Matrix.one_apply, Complex.conj_ofNat]
  norm_num

/-- Regression edge `ω = 0`: the source energy vanishes. -/
theorem quadraticForm_oddSourceWitnessK2_zero :
    quadraticForm (sourceMatrix 0 2) oddSourceWitnessK2 = 0 := by
  rw [sourceMatrix_zero]
  simp [quadraticForm]

/-- The `K = 2` legal odd carrier is the line through `u₀`. -/
theorem eq_smul_oddSourceWitnessK2 {u : Fin (2 * 2 + 1) → ℂ}
    (hu : u ∈ oddBoundaryFlatSubspace 2) : u = u 4 • oddSourceWitnessK2 := by
  obtain ⟨hflat, hodd⟩ := Submodule.mem_inf.mp hu
  have hrev := (mem_oddCoefficientSubspace_iff 2 u).mp hodd
  have hbf := (mem_boundaryFlatSubspace_iff 2 u).mp hflat
  have h1 := hbf.2.1
  have r0 := congrFun hrev 0
  have r1 := congrFun hrev 1
  have r2 := congrFun hrev 2
  simp only [reverseCoefficients, Pi.neg_apply] at r0 r1 r2
  have e0 : u 0 = -u 4 := by
    have h : u 4 = -u 0 := by simpa using r0
    linear_combination h
  have e1 : u 1 = -u 3 := by
    have h : u 3 = -u 1 := by simpa using r1
    linear_combination h
  have e2 : u 2 = 0 := by
    have : u 2 = -u 2 := by simpa using r2
    linear_combination this / 2
  have hm : centeredMoment 2 1 u = -2 * u 0 - u 1 + u 3 + 2 * u 4 := by
    simp [centeredMoment, Fin.sum_univ_succ, centeredIndex]
    ring
  rw [hm, e0, e1] at h1
  have e3 : u 3 = -2 * u 4 := by linear_combination h1 / 2
  funext i
  fin_cases i <;> simp [oddSourceWitnessK2, e0, e1, e2, e3] <;> ring

/-- **M47 (odd form).**  Every nonzero legal odd `K = 2` vector has strictly
negative real source energy on `0 < ω ≤ 3/4`. -/
theorem re_quadraticForm_neg_of_mem_oddBoundaryFlat_two {u : Fin (2 * 2 + 1) → ℂ}
    (hu : u ∈ oddBoundaryFlatSubspace 2) (hne : u ≠ 0) {ω : ℝ} (h0 : 0 < ω)
    (h3 : ω ≤ 3 / 4) :
    (quadraticForm (sourceMatrix ω 2) u).re < 0 := by
  have heq := eq_smul_oddSourceWitnessK2 hu
  have hc : u 4 ≠ 0 := by
    intro hc
    apply hne
    rw [heq, hc, zero_smul]
  rw [heq, quadraticForm_smul]
  have hstar : star (u 4) * u 4 = ((Complex.normSq (u 4) : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    rfl
  rw [hstar, Complex.re_ofReal_mul]
  exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hc)
    (re_quadraticForm_oddSourceWitnessK2_neg h0 h3)

/-- **M47 (even form).**  For every nonzero legal even `K = 2` vector `z`,
`Re e_{Dz}(ω) < 0` on `0 < ω ≤ 3/4`, where `(Dz)_n = n z_n`. -/
theorem re_quadraticForm_index_neg_of_mem_evenBoundaryFlat_two {z : Fin (2 * 2 + 1) → ℂ}
    (hz : z ∈ evenBoundaryFlatSubspace 2) (hne : z ≠ 0) {ω : ℝ} (h0 : 0 < ω)
    (h3 : ω ≤ 3 / 4) :
    (quadraticForm (sourceMatrix ω 2) (indexMatrix 2 *ᵥ z)).re < 0 := by
  have hodd : indexMatrix 2 *ᵥ z ∈ oddBoundaryFlatSubspace 2 :=
    (evenToOddIndexLinearMap 2 ⟨z, hz⟩).property
  have hDne : indexMatrix 2 *ᵥ z ≠ 0 := by
    intro hD
    apply hne
    have hflat := (mem_boundaryFlatSubspace_iff 2 z).mp (Submodule.mem_inf.mp hz).1
    have h0' := hflat.1
    have hcoord : ∀ i, (indexMatrix 2 *ᵥ z) i = ((centeredIndex 2 i : ℤ) : ℂ) * z i := by
      intro i
      simp [indexMatrix, Matrix.mulVec_diagonal]
    have hz0 : z 0 = 0 := by
      have := congrFun hD 0
      rw [hcoord] at this
      simpa [centeredIndex] using this
    have hz1 : z 1 = 0 := by
      have := congrFun hD 1
      rw [hcoord] at this
      simpa [centeredIndex] using this
    have hz3 : z 3 = 0 := by
      have := congrFun hD 3
      rw [hcoord] at this
      simpa [centeredIndex] using this
    have hz4 : z 4 = 0 := by
      have := congrFun hD 4
      rw [hcoord] at this
      simpa [centeredIndex] using this
    have hz2 : z 2 = 0 := by
      have hm : centeredMoment 2 0 z = z 0 + z 1 + z 2 + z 3 + z 4 := by
        simp [centeredMoment, Fin.sum_univ_succ]
        ring
      rw [hm, hz0, hz1, hz3, hz4] at h0'
      simpa using h0'
    funext i
    fin_cases i <;> simp [hz0, hz1, hz2, hz3, hz4]
  exact re_quadraticForm_neg_of_mem_oddBoundaryFlat_two hodd hDne h0 h3

/-! ## M48: every `K = 2` prime sample is sign-controlled through `L = log 16` -/

/-- For `0 < L ≤ log 16` and an integer sample `2 ≤ q ≤ e^L`, the source
coordinate `ω_q = 1 - log q / L` lies in `[0, 3/4]`. -/
theorem primeSampleCoordinate_mem_of_le_log_sixteen {L : ℝ} (hL : 0 < L)
    (hL16 : L ≤ Real.log 16) {q : ℕ} (hq2 : 2 ≤ q) (hqL : (q : ℝ) ≤ Real.exp L) :
    0 ≤ 1 - Real.log q / L ∧ 1 - Real.log q / L ≤ 3 / 4 := by
  have hq0 : (0 : ℝ) < q := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq2
    linarith
  have hlogq : Real.log q ≤ L := by
    rw [Real.log_le_iff_le_exp hq0]
    exact hqL
  have hlog2 : Real.log 2 ≤ Real.log q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq2)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  constructor
  · rw [sub_nonneg, div_le_one hL]
    exact hlogq
  · have : 1 / 4 ≤ Real.log q / L := by
      rw [le_div_iff₀ hL]
      nlinarith
    linarith

/-- **M48 (source side).**  For a legal even `K = 2` vector, every sampled
prime-power coordinate with `0 < L ≤ log 16` has nonpositive real source
energy, strictly negative when `z ≠ 0` and the sample is not the entering one
(`q < e^L`).  Consequently each prime term `-β_q e_{Dz}(ω_q)` with `β_q ≥ 0` is
nonnegative.  (No F04 or contact statement is made here.) -/
theorem re_quadraticForm_index_nonpos_of_primeSample_two {z : Fin (2 * 2 + 1) → ℂ}
    (hz : z ∈ evenBoundaryFlatSubspace 2) {L : ℝ} (hL : 0 < L) (hL16 : L ≤ Real.log 16)
    {q : ℕ} (hq2 : 2 ≤ q) (hqL : (q : ℝ) ≤ Real.exp L) :
    (quadraticForm (sourceMatrix (1 - Real.log q / L) 2) (indexMatrix 2 *ᵥ z)).re ≤ 0 := by
  obtain ⟨h0, h3⟩ := primeSampleCoordinate_mem_of_le_log_sixteen hL hL16 hq2 hqL
  by_cases hz0 : z = 0
  · subst hz0
    simp [quadraticForm]
  rcases eq_or_lt_of_le h0 with hω | hω
  · rw [← hω, sourceMatrix_zero]
    simp [quadraticForm]
  · exact (re_quadraticForm_index_neg_of_mem_evenBoundaryFlat_two hz hz0 hω h3).le

theorem re_quadraticForm_index_neg_of_primeSample_two {z : Fin (2 * 2 + 1) → ℂ}
    (hz : z ∈ evenBoundaryFlatSubspace 2) (hne : z ≠ 0) {L : ℝ} (hL : 0 < L)
    (hL16 : L ≤ Real.log 16) {q : ℕ} (hq2 : 2 ≤ q) (hqL : (q : ℝ) < Real.exp L) :
    (quadraticForm (sourceMatrix (1 - Real.log q / L) 2) (indexMatrix 2 *ᵥ z)).re < 0 := by
  obtain ⟨_, h3⟩ := primeSampleCoordinate_mem_of_le_log_sixteen hL hL16 hq2 hqL.le
  have hq0 : (0 : ℝ) < q := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq2
    linarith
  have hlt : Real.log q < L := by
    rw [Real.log_lt_iff_lt_exp hq0]
    exact hqL
  have hω : 0 < 1 - Real.log q / L := by
    rw [sub_pos, div_lt_one hL]
    exact hlt
  exact re_quadraticForm_index_neg_of_mem_evenBoundaryFlat_two hz hne hω h3

theorem primeTerm_nonneg_of_primeSample_two {z : Fin (2 * 2 + 1) → ℂ}
    (hz : z ∈ evenBoundaryFlatSubspace 2) {L : ℝ} (hL : 0 < L) (hL16 : L ≤ Real.log 16)
    {q : ℕ} (hq2 : 2 ≤ q) (hqL : (q : ℝ) ≤ Real.exp L) {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ -(β * (quadraticForm (sourceMatrix (1 - Real.log q / L) 2) (indexMatrix 2 *ᵥ z)).re) := by
  have := re_quadraticForm_index_nonpos_of_primeSample_two hz hL hL16 hq2 hqL
  nlinarith

end Zeta23.CCM

#print axioms Zeta23.CCM.quadraticForm_oddSourceWitnessK2_eq_integral
#print axioms Zeta23.CCM.quadraticForm_oddSourceWitnessK2
#print axioms Zeta23.CCM.re_quadraticForm_oddSourceWitnessK2_neg
#print axioms Zeta23.CCM.quadraticForm_oddSourceWitnessK2_one
#print axioms Zeta23.CCM.eq_smul_oddSourceWitnessK2
#print axioms Zeta23.CCM.re_quadraticForm_neg_of_mem_oddBoundaryFlat_two
#print axioms Zeta23.CCM.re_quadraticForm_index_neg_of_mem_evenBoundaryFlat_two
#print axioms Zeta23.CCM.primeSampleCoordinate_mem_of_le_log_sixteen
#print axioms Zeta23.CCM.re_quadraticForm_index_nonpos_of_primeSample_two
#print axioms Zeta23.CCM.re_quadraticForm_index_neg_of_primeSample_two
#print axioms Zeta23.CCM.primeTerm_nonneg_of_primeSample_two
