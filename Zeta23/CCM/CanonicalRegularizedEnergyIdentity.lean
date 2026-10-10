import Zeta23.CCM.DictionaryCompletePhysicalRHS
import Zeta23.CCM.SourceNormalizationRepair

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate Interval

/-!
# POST284-M05: canonical nonzero-endpoint finite-part energy identity

For every positive aperture `L`, every size `N` and all complex coefficient
vectors, the production canonical source pairing is an exact regularized
physical-space value of the (generally NOT zero-centered) mixed dictionary test.
With `f_L(t) = e_u(1 - t/L)`, `c_u = e_u(1) = 2‖u‖²`,
`W = e^{-t/2} + e^{t/2}`, `ρ = archDensity`:

`quadraticForm (canonicalSourceMatrix L N) u
   = ∫_0^L f_L W - ∫_0^L (f_L - c_u e^{-t/2}) ρ - c_u wCorrection(L)
       - ∑_{2 ≤ q ≤ ⌊e^L⌋} Λ(q)/√q f_L(log q)`.

Normalization audit (handoff v0.4 §2.1):

* the scalar correction is exactly `c_u · wCorrection L` with the repository's
  `wCorrection` definition;
* `canonicalArchScalarCorrection = 2 (sourceEq411DerivedCorrection + wCorrection)`
  is NOT added again: it belongs to the reduced normalization only;
* the derivation uses the theorem-authoritative dictionary bridge
  `literatureRHS_dictionaryMixedTest_eq_matrixCoefficientPairing`, the
  archimedean `μ₀` density theorem and the `μ₀`/`wCorrection` tail identity
  `mu_zero_reference_tail_eq_neg_two_wCorrection`; no zero-at-origin hypothesis
  and no F04 premise is used.

This is a fixed-aperture value identity.  It does not differentiate in `L` and
gives no derivative transport (F04 stays OPEN), no sign, and no RH conclusion.
-/

/-- Regularized complete physical value of an even test that need not vanish at
the origin. -/
def regularizedCompletePhysicalRHS (k : ℝ → ℂ) (L : ℝ) : ℂ :=
  (∫ x in (0 : ℝ)..L, k x * (completeSourcePoleWeight x : ℂ))
    -
  ((∫ x in (0 : ℝ)..L,
      (k x - k 0 * (Real.exp (-x / 2) : ℂ)) * (archDensity x : ℂ)) +
    k 0 * (wCorrection L : ℂ))
    -
  ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, primeSourceWeight q * k (Real.log q)

/-- Nonzero-endpoint archimedean channel of a mixed dictionary test. -/
theorem half_dictionaryArchRHS_dictionaryMixedTest_eq_regularized
    (N : ℕ) (x y : Fin (2 * N + 1) → ℂ) {L : ℝ} (hL : 0 < L) :
    (1 / 2 : ℂ) * dictionaryArchRHS (dictionaryMixedTest N x y L) =
      -((∫ z in (0 : ℝ)..L,
          (dictionaryMixedTest N x y L z -
            dictionaryMixedTest N x y L 0 * (Real.exp (-z / 2) : ℂ)) *
              (archDensity z : ℂ)) +
        dictionaryMixedTest N x y L 0 * (wCorrection L : ℂ)) := by
  set k : ℝ → ℂ := dictionaryMixedTest N x y L with hk_def
  have hk : Continuous k := continuous_dictionaryMixedTest N x y hL
  have hki : Integrable k :=
    hk.integrable_of_hasCompactSupport (dictionaryMixedTest_hasCompactSupport N x y L)
  have hFk := integrable_fourier_dictionaryMixedTest N x y hL
  have heven : ∀ z : ℝ, k (-z) = k z := fun z => dictionaryMixedTest_neg N x y L z
  have hmu := integrable_paperFT_dictionaryMixedTest_mul_mu_sub_mu_zero N x y hL
  have harch := dictionaryArchRHS_eq_mu_zero_add_archDensity_integral hk hki hFk heven hmu
  have htail := mu_zero_reference_tail_eq_neg_two_wCorrection hL
  -- integrability
  have hD : IntegrableOn (fun z : ℝ => (k 0 - k z) * (archDensity z : ℂ)) (Ioi 0) :=
    integrableOn_sub_mul_archDensity_Ioi hk hki hFk heven hmu
  have hR : IntegrableOn (fun z : ℝ => (1 - Real.exp (-z / 2)) * archDensity z) (Ioi 0) :=
    integrableOn_one_sub_exp_mul_archDensity_Ioi
  have hE : IntegrableOn (fun z : ℝ => Real.exp (-z / 2) * archDensity z) (Ioi L) :=
    integrableOn_exp_neg_half_mul_archDensity_Ioi hL
  have hset : Ioc 0 L ∪ Ioi L = Ioi (0 : ℝ) := Set.Ioc_union_Ioi_eq_Ioi hL.le
  have hdisj : Disjoint (Ioc (0 : ℝ) L) (Ioi L) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact absurd hz1.2 (not_le.mpr hz2)
  have hIoc : Ioc (0 : ℝ) L ⊆ Ioi 0 := fun z hz => hz.1
  have hIoiL : Ioi L ⊆ Ioi (0 : ℝ) := fun z hz => hL.trans hz
  -- real splittings
  have hA : (∫ z in Ioi (0 : ℝ), (1 - Real.exp (-z / 2)) * archDensity z) =
      (∫ z in Ioc (0 : ℝ) L, (1 - Real.exp (-z / 2)) * archDensity z) +
        ∫ z in Ioi L, (1 - Real.exp (-z / 2)) * archDensity z := by
    rw [← hset, setIntegral_union hdisj measurableSet_Ioi (hR.mono_set hIoc)
      (hR.mono_set hIoiL)]
  have hRL : (∫ z in Ioi L, archDensity z) =
      (∫ z in Ioi L, (1 - Real.exp (-z / 2)) * archDensity z) +
        ∫ z in Ioi L, Real.exp (-z / 2) * archDensity z := by
    rw [← integral_add (hR.mono_set hIoiL) hE]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z _
    ring
  -- complex splittings
  have hDsplit : (∫ z in Ioi (0 : ℝ), (k 0 - k z) * (archDensity z : ℂ)) =
      (∫ z in Ioc (0 : ℝ) L, (k 0 - k z) * (archDensity z : ℂ)) +
        ∫ z in Ioi L, (k 0 - k z) * (archDensity z : ℂ) := by
    rw [← hset, setIntegral_union hdisj measurableSet_Ioi (hD.mono_set hIoc)
      (hD.mono_set hIoiL)]
  have hDtail : (∫ z in Ioi L, (k 0 - k z) * (archDensity z : ℂ)) =
      k 0 * ((∫ z in Ioi L, archDensity z : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    have hzL : L < |z| := by
      rw [abs_of_pos (hL.trans hz)]
      exact hz
    have hkz : k z = 0 := dictionaryMixedTest_eq_zero_of_lt_abs N x y L z hzL
    simp [hkz]
  have hTint : (∫ z in (0 : ℝ)..L,
        (k z - k 0 * (Real.exp (-z / 2) : ℂ)) * (archDensity z : ℂ)) =
      -(∫ z in Ioc (0 : ℝ) L, (k 0 - k z) * (archDensity z : ℂ)) +
        k 0 * ((∫ z in Ioc (0 : ℝ) L, (1 - Real.exp (-z / 2)) * archDensity z : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_of_le hL.le, ← integral_complex_ofReal, ← integral_const_mul,
      ← integral_neg, ← integral_add]
    · apply setIntegral_congr_fun measurableSet_Ioc
      intro z _
      push_cast
      ring
    · exact (hD.mono_set hIoc).neg
    · exact ((hR.mono_set hIoc).ofReal).const_mul _
  -- cast the real identities
  have htailC : ((2 * Real.pi * Zeta23.mu 0 : ℝ) : ℂ) +
      2 * ((∫ z in Ioi (0 : ℝ), (1 - Real.exp (-z / 2)) * archDensity z : ℝ) : ℂ) +
      2 * ((∫ z in Ioi L, Real.exp (-z / 2) * archDensity z : ℝ) : ℂ) =
        -2 * (wCorrection L : ℂ) := by
    exact_mod_cast htail
  have hAC : ((∫ z in Ioi (0 : ℝ), (1 - Real.exp (-z / 2)) * archDensity z : ℝ) : ℂ) =
      ((∫ z in Ioc (0 : ℝ) L, (1 - Real.exp (-z / 2)) * archDensity z : ℝ) : ℂ) +
        ((∫ z in Ioi L, (1 - Real.exp (-z / 2)) * archDensity z : ℝ) : ℂ) := by
    exact_mod_cast hA
  have hRLC : ((∫ z in Ioi L, archDensity z : ℝ) : ℂ) =
      ((∫ z in Ioi L, (1 - Real.exp (-z / 2)) * archDensity z : ℝ) : ℂ) +
        ((∫ z in Ioi L, Real.exp (-z / 2) * archDensity z : ℝ) : ℂ) := by
    exact_mod_cast hRL
  rw [harch, hTint]
  rw [hDsplit, hDtail]
  linear_combination (k 0 / 2) * htailC - k 0 * hAC + k 0 * hRLC

/-- **M05 sesquilinear form.**  The production canonical source pairing is
twice the regularized physical value of the mixed dictionary test, for every
positive aperture; no zero-at-origin or F04 premise. -/
theorem matrixCoefficientPairing_canonicalSourceMatrix_eq_regularized
    (N : ℕ) (x y : Fin (2 * N + 1) → ℂ) {L : ℝ} (hL : 0 < L) :
    matrixCoefficientPairing (canonicalSourceMatrix L N) x y =
      2 * regularizedCompletePhysicalRHS (dictionaryMixedTest N x y L) L := by
  rw [canonicalSourceMatrix_eq_dictionaryMatrix,
    ← literatureRHS_dictionaryMixedTest_eq_matrixCoefficientPairing N x y hL,
    literatureRHS_eq_dictionaryChannels]
  have hpole := half_dictionaryPoleRHS_dictionaryMixedTest_eq_interval N x y hL
  have hprime := half_dictionaryPrimeRHS_dictionaryMixedTest_eq_samples N x y hL
  have harch := half_dictionaryArchRHS_dictionaryMixedTest_eq_regularized N x y hL
  unfold regularizedCompletePhysicalRHS
  linear_combination 2 * hpole + 2 * hprime + 2 * harch

/-- On the physical aperture the doubled mixed test is the elementary source
sesquilinear contraction at `ω = 1 - t/L`. -/
theorem two_mul_dictionaryMixedTest_eq_sourcePairing
    (N : ℕ) (x y : Fin (2 * N + 1) → ℂ) {L t : ℝ} (ht0 : 0 ≤ t) (htL : t ≤ L) :
    2 * dictionaryMixedTest N x y L t =
      matrixCoefficientPairing (sourceMatrix (1 - t / L) N) x y := by
  unfold dictionaryMixedTest matrixCoefficientPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [dictionaryBasisTest, kernel, abs_of_nonneg ht0, htL,
    sourceEntry_one_sub_eq_qBasis]
  ring

/-- At the origin the doubled mixed test is the `ω = 1` source pairing
`2 ⟨x, y⟩`. -/
theorem two_mul_dictionaryMixedTest_zero
    (N : ℕ) (x y : Fin (2 * N + 1) → ℂ) {L : ℝ} (hL : 0 ≤ L) :
    2 * dictionaryMixedTest N x y L 0 =
      matrixCoefficientPairing (sourceMatrix 1 N) x y := by
  have h := two_mul_dictionaryMixedTest_eq_sourcePairing N x y le_rfl hL
  simpa using h

/-- **M05 energy form (handoff notation).**  With `f_L(t) = e_u(1 - t/L)` and
`c_u = e_u(1)`:
`e_L(u) = ∫ f_L W - ∫ (f_L - c_u e^{-t/2}) ρ - c_u wCorrection L
  - ∑ Λ(q)/√q f_L(log q)`. -/
theorem quadraticForm_canonicalSourceMatrix_eq_regularizedEnergy
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) {L : ℝ} (hL : 0 < L) :
    quadraticForm (canonicalSourceMatrix L N) u =
      (∫ t in (0 : ℝ)..L,
          quadraticForm (sourceMatrix (1 - t / L) N) u *
            (completeSourcePoleWeight t : ℂ))
        -
      ((∫ t in (0 : ℝ)..L,
          (quadraticForm (sourceMatrix (1 - t / L) N) u -
            quadraticForm (sourceMatrix 1 N) u * (Real.exp (-t / 2) : ℂ)) *
              (archDensity t : ℂ)) +
        quadraticForm (sourceMatrix 1 N) u * (wCorrection L : ℂ))
        -
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight q *
          quadraticForm (sourceMatrix (1 - Real.log q / L) N) u := by
  have hq : ∀ (M : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ),
      quadraticForm M u = matrixCoefficientPairing M u u := by
    intro M
    rfl
  set k := dictionaryMixedTest N u u L with hk_def
  have hk0 : quadraticForm (sourceMatrix 1 N) u = 2 * k 0 := by
    rw [hq, two_mul_dictionaryMixedTest_zero N u u hL.le]
  have hkt : ∀ t ∈ Set.uIcc (0 : ℝ) L,
      quadraticForm (sourceMatrix (1 - t / L) N) u = 2 * k t := by
    intro t ht
    rw [Set.uIcc_of_le hL.le] at ht
    rw [hq, two_mul_dictionaryMixedTest_eq_sourcePairing N u u ht.1 ht.2]
  have hpole : (∫ t in (0 : ℝ)..L,
        quadraticForm (sourceMatrix (1 - t / L) N) u * (completeSourcePoleWeight t : ℂ)) =
      2 * ∫ t in (0 : ℝ)..L, k t * (completeSourcePoleWeight t : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only
    rw [hkt t ht]
    ring
  have harch : (∫ t in (0 : ℝ)..L,
        (quadraticForm (sourceMatrix (1 - t / L) N) u -
          quadraticForm (sourceMatrix 1 N) u * (Real.exp (-t / 2) : ℂ)) *
            (archDensity t : ℂ)) =
      2 * ∫ t in (0 : ℝ)..L,
        (k t - k 0 * (Real.exp (-t / 2) : ℂ)) * (archDensity t : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only
    rw [hkt t ht, hk0]
    ring
  have hprime : (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight q * quadraticForm (sourceMatrix (1 - Real.log q / L) N) u) =
      2 * ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, primeSourceWeight q * k (Real.log q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq'
    rw [Finset.mem_Icc] at hq'
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq'.1
    have hqpos : (0 : ℝ) < q := by linarith
    have hlog0 : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
    have hlogL : Real.log q ≤ L := by
      have hle : (q : ℝ) ≤ Real.exp L := by
        have := Nat.floor_le (Real.exp_pos L).le
        exact le_trans (by exact_mod_cast hq'.2) this
      have := Real.log_le_log hqpos hle
      rwa [Real.log_exp] at this
    rw [hkt (Real.log q) (by rw [Set.uIcc_of_le hL.le]; exact ⟨hlog0, hlogL⟩)]
    ring
  rw [hq (canonicalSourceMatrix L N),
    matrixCoefficientPairing_canonicalSourceMatrix_eq_regularized N u u hL,
    hpole, harch, hprime, hk0]
  unfold regularizedCompletePhysicalRHS
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.half_dictionaryArchRHS_dictionaryMixedTest_eq_regularized
#print axioms Zeta23.CCM.matrixCoefficientPairing_canonicalSourceMatrix_eq_regularized
#print axioms Zeta23.CCM.two_mul_dictionaryMixedTest_eq_sourcePairing
#print axioms Zeta23.CCM.quadraticForm_canonicalSourceMatrix_eq_regularizedEnergy
