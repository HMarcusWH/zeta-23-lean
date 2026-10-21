import Zeta23.OPICA.EnergyRate
import Zeta23.OPICA.ObservationCompatibility
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace Zeta23.OPICAFollowup

noncomputable section

variable {𝕜 E Y H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [FiniteDimensional 𝕜 Y]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]

local instance : CompleteSpace E := FiniteDimensional.complete 𝕜 E
local instance : CompleteSpace Y := FiniteDimensional.complete 𝕜 Y
local instance : CompleteSpace H := FiniteDimensional.complete 𝕜 H
local instance : ProperSpace Y := FiniteDimensional.proper 𝕜 Y

/-- Observation and retained history use the Hilbert product norm. -/
def jointObservation (P : E →L[𝕜] Y) (C : E →L[𝕜] H) :
    E →L[𝕜] WithLp 2 (Y × H) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 Y H).symm.toContinuousLinearMap.comp (P.prod C)

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 Y] [FiniteDimensional 𝕜 H] in
@[simp] theorem jointObservation_apply (P : E →L[𝕜] Y) (C : E →L[𝕜] H) (x : E) :
    jointObservation P C x = WithLp.toLp 2 (P x, C x) := rfl

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 Y] [FiniteDimensional 𝕜 H] in
theorem jointObservation_ker (P : E →L[𝕜] Y) (C : E →L[𝕜] H) :
    (jointObservation P C).ker = P.ker ⊓ C.ker := by
  ext x
  simp [LinearMap.mem_ker, jointObservation]

omit [FiniteDimensional 𝕜 Y] [FiniteDimensional 𝕜 H] in
/-- Recoverability is a kernel condition for the complete finite-rank observation. -/
theorem joint_recovery_iff (P : E →L[𝕜] Y) (C : E →L[𝕜] H) (ell : E →L[𝕜] 𝕜) :
    (∃ R : WithLp 2 (Y × H) →L[𝕜] 𝕜,
      ∀ x, R (jointObservation P C x) = ell x) ↔ P.ker ⊓ C.ker ≤ ell.ker := by
  let A := jointObservation P C
  constructor
  · rintro ⟨R, hR⟩ x hx
    have hxA : A x = 0 := by
      have : x ∈ A.ker := by simpa [A, jointObservation_ker] using hx
      exact this
    change ell x = 0
    rw [← hR x, hxA, map_zero]
  · intro hker
    have hkerA : A.ker ≤ ell.ker := by simpa [A, jointObservation_ker] using hker
    obtain ⟨r, hr⟩ := (Zeta23.OPICA.observation_factors_iff_ker_le
      A.toLinearMap ell.toLinearMap).mpr hkerA
    let R : WithLp 2 (Y × H) →L[𝕜] 𝕜 :=
      r.toContinuousLinearMap.comp A.range.orthogonalProjectionOnto
    refine ⟨R, fun x => ?_⟩
    have hp := A.range.orthogonalProjectionOnto_mem_subspace_eq_self
      (⟨A x, ⟨x, rfl⟩⟩ : A.range)
    change r (A.range.orthogonalProjectionOnto (A x)) = ell x
    rw [hp]
    exact (congrArg (fun f : E →ₗ[𝕜] 𝕜 => f x) hr).symm

/-- Approximate compatibility is attained in finite dimensions, and a unit left-null
observation supplies a strict infeasibility certificate. -/
theorem approx_compatibility_left_null (B : E →L[𝕜] Y) (b : Y) (epsilon : ℝ)
    (_hepsilon : 0 ≤ epsilon) :
    (Metric.infDist b (B.range : Set Y) ≤ epsilon ↔
      ∃ x : E, ‖b - B x‖ ≤ epsilon) ∧
    (∀ v : Y, B.adjoint v = 0 → ‖v‖ = 1 → epsilon < ‖inner 𝕜 v b‖ →
      ¬ ∃ x : E, ‖b - B x‖ ≤ epsilon) := by
  constructor
  · constructor
    · intro hd
      obtain ⟨y, hy, hdist⟩ := B.range.closed_of_finiteDimensional.exists_infDist_eq_dist
        ⟨0, B.range.zero_mem⟩ b
      obtain ⟨x, rfl⟩ := hy
      exact ⟨x, by simpa [hdist, dist_eq_norm] using hd⟩
    · rintro ⟨x, hx⟩
      have hd := Metric.infDist_le_dist_of_mem (x := b)
        (show B x ∈ B.range from ⟨x, rfl⟩)
      have hd' : Metric.infDist b (B.range : Set Y) ≤ ‖b - B x‖ := by
        simpa only [dist_eq_norm] using hd
      exact hd'.trans hx
  · intro v hv hnorm hstrict
    rintro ⟨x, hx⟩
    have hz : inner 𝕜 v (B x) = 0 := by
      rw [← B.adjoint_inner_left x v, hv, inner_zero_left]
    have hp : inner 𝕜 v b = inner 𝕜 v (b - B x) := by
      rw [inner_sub_right, hz, sub_zero]
    have hh := norm_inner_le_norm (𝕜 := 𝕜) v (b - B x)
    rw [hnorm, one_mul, ← hp] at hh
    exact (not_lt_of_ge (hh.trans hx)) hstrict

omit [FiniteDimensional 𝕜 Y] [FiniteDimensional 𝕜 H] in
/-- The optimal recovery is attained, has the exact ratio-supremum norm, and has
zero cost exactly when the target is zero, including nonzero observations. -/
theorem joint_recovery_optimal_norm (P : E →L[𝕜] Y) (C : E →L[𝕜] H)
    (ell : E →L[𝕜] 𝕜) (hker : P.ker ⊓ C.ker ≤ ell.ker) :
    ∃ R : WithLp 2 (Y × H) →L[𝕜] 𝕜,
      (∀ x, R (jointObservation P C x) = ell x) ∧
      ‖R‖ = sSup {q : ℝ | ∃ x : E, jointObservation P C x ≠ 0 ∧
        q = ‖ell x‖ / ‖jointObservation P C x‖} ∧
      (‖R‖ = 0 ↔ ell = 0) ∧
      (∀ R' : WithLp 2 (Y × H) →L[𝕜] 𝕜,
        (∀ x, R' (jointObservation P C x) = ell x) → ‖R‖ ≤ ‖R'‖) := by
  let A := jointObservation P C
  have hkerA : A.ker ≤ ell.ker := by simpa [A, jointObservation_ker] using hker
  obtain ⟨r₀, hr₀⟩ := (Zeta23.OPICA.observation_factors_iff_ker_le
    A.toLinearMap ell.toLinearMap).mpr hkerA
  let r : A.range →L[𝕜] 𝕜 := r₀.toContinuousLinearMap
  have hfactor (x : E) : r ⟨A x, ⟨x, rfl⟩⟩ = ell x :=
    (congrArg (fun f : E →ₗ[𝕜] 𝕜 => f x) hr₀).symm
  let R : WithLp 2 (Y × H) →L[𝕜] 𝕜 := r.comp A.range.orthogonalProjectionOnto
  have hrec (x : E) : R (A x) = ell x := by
    change r (A.range.orthogonalProjectionOnto (A x)) = ell x
    rw [A.range.orthogonalProjectionOnto_mem_subspace_eq_self
      (⟨A x, ⟨x, rfl⟩⟩ : A.range)]
    exact hfactor x
  have hlower (R' : WithLp 2 (Y × H) →L[𝕜] 𝕜)
      (hR' : ∀ x, R' (A x) = ell x) : ‖r‖ ≤ ‖R'‖ := by
    apply r.opNorm_le_bound (norm_nonneg R')
    rintro ⟨y, ⟨x, rfl⟩⟩
    change ‖r ⟨A x, _⟩‖ ≤ ‖R'‖ * ‖A x‖
    rw [hfactor x, ← hR' x]
    exact R'.le_opNorm (A x)
  have hnorm : ‖R‖ = ‖r‖ := by
    apply le_antisymm
    · calc
        ‖R‖ ≤ ‖r‖ * ‖A.range.orthogonalProjectionOnto‖ := r.opNorm_comp_le _
        _ ≤ ‖r‖ * 1 := mul_le_mul_of_nonneg_left
          A.range.orthogonalProjectionOnto_norm_le (norm_nonneg r)
        _ = ‖r‖ := mul_one _
    · exact hlower R hrec
  have hsup : ‖r‖ = sSup {q : ℝ | ∃ x : E, A x ≠ 0 ∧ q = ‖ell x‖ / ‖A x‖} := by
    by_cases hA : ∃ x : E, A x ≠ 0
    · obtain ⟨x₀, hx₀⟩ := hA
      have hn : Set.Nonempty {q : ℝ | ∃ x : E, A x ≠ 0 ∧ q = ‖ell x‖ / ‖A x‖} :=
        ⟨‖ell x₀‖ / ‖A x₀‖, x₀, hx₀, rfl⟩
      apply Eq.symm
      apply IsLUB.csSup_eq _ hn
      constructor
      · rintro q ⟨x, hx, rfl⟩
        have hb := r.ratio_le_opNorm (⟨A x, ⟨x, rfl⟩⟩ : A.range)
        change ‖r ⟨A x, _⟩‖ / ‖A x‖ ≤ ‖r‖ at hb
        rwa [hfactor x] at hb
      · intro q hq
        have hq₀ : 0 ≤ q := (div_nonneg (norm_nonneg _) (norm_nonneg _)).trans
          (hq ⟨x₀, hx₀, rfl⟩)
        apply r.opNorm_le_bound hq₀
        rintro ⟨y, ⟨x, rfl⟩⟩
        change ‖r ⟨A x, _⟩‖ ≤ q * ‖A x‖
        rw [hfactor]
        by_cases hx : A x = 0
        · have he : ell x = 0 := hkerA hx
          simp [hx, he]
        · exact (div_le_iff₀ (norm_pos_iff.mpr hx)).mp (hq ⟨x, hx, rfl⟩)
    · have hAz : ∀ x : E, A x = 0 := by simpa using hA
      have hr : r = 0 := by
        ext y
        obtain ⟨y, ⟨x, rfl⟩⟩ := y
        have he : ell x = 0 := hkerA (hAz x)
        change r ⟨A x, _⟩ = 0
        rw [hfactor x, he]
      have hs : {q : ℝ | ∃ x : E, A x ≠ 0 ∧ q = ‖ell x‖ / ‖A x‖} = ∅ := by
        ext q
        simp [hAz]
      rw [hr, hs, Real.sSup_empty]
      exact ContinuousLinearMap.opNorm_zero
  refine ⟨R, hrec, hnorm.trans hsup, ?_, ?_⟩
  · constructor
    · intro hz
      have hRz : R = 0 := norm_eq_zero.mp hz
      ext x
      simpa [hRz] using (hrec x).symm
    · intro hell
      have hm := hlower 0 (by simp [hell])
      have hm' : ‖r‖ ≤ 0 := by simpa only [norm_zero] using hm
      exact hnorm.trans (le_antisymm hm' (norm_nonneg r))
  · intro R' hR'
    rw [hnorm]
    exact hlower R' hR'

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 Y] [FiniteDimensional 𝕜 H] in
/-- An exact joint recovery propagates every observation/history error with its
operator norm; at the optimum this is the exact minimal recovery cost. -/
theorem joint_recovery_noise_bound (P : E →L[𝕜] Y) (C : E →L[𝕜] H)
    (ell : E →L[𝕜] 𝕜) (R : WithLp 2 (Y × H) →L[𝕜] 𝕜)
    (hR : ∀ x, R (jointObservation P C x) = ell x)
    (epsilon : ℝ) (_hepsilon : 0 ≤ epsilon) (x : E) (y : WithLp 2 (Y × H))
    (herror : ‖y - jointObservation P C x‖ ≤ epsilon) :
    ‖ell x - R y‖ ≤ ‖R‖ * epsilon := by
  calc
    ‖ell x - R y‖ = ‖R (jointObservation P C x - y)‖ := by rw [map_sub, hR]
    _ ≤ ‖R‖ * ‖jointObservation P C x - y‖ := R.le_opNorm _
    _ ≤ ‖R‖ * epsilon := by
      exact mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using herror)
        (norm_nonneg R)

/-- The observation spaces may change with the horizon. The error vector is the
complete observation/history error, and its recovery cost is explicitly retained. -/
theorem recovery_subexp_budget {F : ℕ → Type*}
    [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace 𝕜 (F n)]
    (T : Zeta23.OPICA.HorizonSchedule) (R : ∀ n, F n →L[𝕜] 𝕜) (error : ∀ n, F n)
    (recovery_budget : Zeta23.OPICA.SubexpAlong T (fun n => ‖R n‖))
    (error_budget : Zeta23.OPICA.SubexpAlong T (fun n => ‖error n‖)) :
    Zeta23.OPICA.SubexpAlong T (fun n => R n (error n)) := by
  have hprod := Zeta23.OPICA.subexpAlong_mul T recovery_budget error_budget
  apply squeeze_zero
    (fun n => Zeta23.OPICA.magnitudeRate_nonneg T (fun n => R n (error n))
      (fun n => norm_nonneg _) n) (fun n => ?_) hprod
  unfold Zeta23.OPICA.magnitudeRate
  apply div_le_div_of_nonneg_right _ (by nlinarith [T.positive n])
  apply Real.log_le_log (by positivity)
  simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg (R n)),
    abs_of_nonneg (norm_nonneg (error n)), add_comm] using
    add_le_add_left ((R n).le_opNorm (error n)) 1

end
end Zeta23.OPICAFollowup
