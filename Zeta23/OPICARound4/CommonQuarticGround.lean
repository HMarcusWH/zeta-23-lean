import Zeta23.CCM.OriginalDetectorFinitePhaseNativeProducer
import Zeta23.OPICARound3.NeutralParityCover
import Zeta23.OPICARound4.JointGroundConstraints
import Zeta23.OPICARound3.FirstSimultaneousNegative

/-!
Actual two-parity negativity at the prescribed quartic detector cutoff.
The common threshold is chosen before the generated packet. Its selected
Schur cutoff and the two first-birth cutoffs remain distinct. The fixed
translated phases give constant negative depths, not two exponential depths.
These necessary constraints do not supply the independent arithmetic bound.
-/
noncomputable section
open Set Complex MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace Zeta23.OPICARound4
open CCM ExceptionalZero OPICARound3

def recenteredSmoothPhase (σ L c : ℝ) : ℝ → ℂ := fun x =>
  (fixedOriginalSincTrialNormalization : ℂ) *
    (fixedOriginalSincKernel (x-c) + (σ : ℂ)*fixedOriginalSincKernel (L-x-c))

def recenteredFiniteApprox (σ L c : ℝ) (hL : 0 < L) : ℝ → ℂ := fun x =>
  (fixedOriginalSincTrialNormalization : ℂ) *
    localizedFiniteFunction L (originalDetectorQuarticCutoff L)
      ((EuclideanSpace.equiv (Fin (2*originalDetectorQuarticCutoff L+1)) ℂ)
        (originalDetectorFinitePhaseVector σ L c hL)) x

def recenteredFiniteHard (σ L c : ℝ) (hL : 0 < L) : ℝ → ℂ := fun x =>
  (fixedOriginalSincTrialNormalization : ℂ) *
    localizedFiniteVector L (originalDetectorQuarticCutoff L)
      ((EuclideanSpace.equiv (Fin (2*originalDetectorQuarticCutoff L+1)) ℂ)
        (originalDetectorFinitePhaseVector σ L c hL)) x

theorem recenteredSmoothPhase_eq_translate (σ L c : ℝ) :
    recenteredSmoothPhase σ L c =
      translateRight (fixedOriginalSincPhaseTrial σ (L/2-c)) (c-fixedOriginalSincLobeCenter) := by
  funext x
  simp only [translateRight, fixedOriginalSincPhaseTrial_reflected_formula,
    recenteredSmoothPhase, fixedOriginalSincTrialAperture]
  congr 3 <;> ring

theorem recenteredSmoothPhase_contDiff (σ L c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (recenteredSmoothPhase σ L c) := by
  rw [recenteredSmoothPhase_eq_translate]
  exact (fixedOriginalSincPhaseTrial_contDiff_top σ (L/2-c)).comp
    (contDiff_id.sub contDiff_const)

theorem recenteredSmoothPhase_L1_bound {σ : ℝ} (hσ : σ=1 ∨ σ= -1)
    (L c : ℝ) (r : ℕ) :
    (∫ x : ℝ, ‖iteratedDeriv r (recenteredSmoothPhase σ L c) x‖) ≤
      originalDetectorOriginalPhaseL1JetBudget r := by
  rw [recenteredSmoothPhase_eq_translate]
  change (∫ x : ℝ, ‖iteratedDeriv r
    (fun y => fixedOriginalSincPhaseTrial σ (L/2-c) (y-(c-fixedOriginalSincLobeCenter))) x‖) ≤ _
  rw [iteratedDeriv_comp_sub_const]
  change (∫ x : ℝ, (fun y => ‖iteratedDeriv r (fixedOriginalSincPhaseTrial σ (L/2-c)) y‖)
    (x-(c-fixedOriginalSincLobeCenter))) ≤ _
  exact (integral_sub_right_eq_self
    (fun x : ℝ => ‖iteratedDeriv r (fixedOriginalSincPhaseTrial σ (L/2-c)) x‖)
    (c-fixedOriginalSincLobeCenter)).le.trans
      (fixedOriginalSincPhaseTrial_originalPhase_L1_bound hσ (L/2-c) r)

theorem recenteredSmoothPhase_zero_outside {L c : ℝ}
    (hleft : 1+UniversalSinc.fixedScale ≤ c)
    (hright : c+UniversalSinc.fixedScale ≤ L-1) (σ : ℝ)
    {x : ℝ} (hx : x ∉ Icc (0 : ℝ) L) : recenteredSmoothPhase σ L c x = 0 := by
  have h1 : x-c ∉ Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale := by
    intro hm
    apply hx
    constructor <;> linarith [hm.1,hm.2]
  have h2 : L-x-c ∉ Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale := by
    intro hm
    apply hx
    constructor <;> linarith [hm.1,hm.2]
  have hz1 := universalSincKernel_zero_outside UniversalSinc.fixedScale_pos h1
  have hz2 := universalSincKernel_zero_outside UniversalSinc.fixedScale_pos h2
  change originalSincTest UniversalSinc.fixedScale (x-c)=0 at hz1
  change originalSincTest UniversalSinc.fixedScale (L-x-c)=0 at hz2
  simp only [recenteredSmoothPhase, fixedOriginalSincKernel, hz1,hz2,mul_zero,add_zero]

theorem recenteredFiniteHard_contDiff {L : ℝ} (hL : 2 ≤ L) (σ c : ℝ) :
    ContDiff ℝ 2 (recenteredFiniteHard σ L c (by linarith)) := by
  apply contDiff_const.mul
  apply contDiff_localizedFiniteVector_of_boundaryFlat _ _ (by linarith)
  rw [originalDetectorFinitePhaseVector_raw]
  exact originalDetectorFinitePhaseRaw_boundaryFlat σ c hL

private theorem iteratedDeriv_reflectionCombination
    {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (σ L : ℝ) (r : ℕ) (x : ℝ) :
    iteratedDeriv r (fun y => f y + (σ : ℂ) * f (L - y)) x =
      iteratedDeriv r f x + (σ : ℂ) * ((-1 : ℝ) ^ r • iteratedDeriv r f (L - x)) := by
  have hr : (r : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top)
  have hreflect : ContDiff ℝ (⊤ : ℕ∞) (fun y => f (L - y)) :=
    hf.comp (contDiff_const.sub contDiff_id)
  rw [iteratedDeriv_fun_add ((hf.of_le hr).contDiffAt)
    (((contDiff_const.mul hreflect).of_le hr).contDiffAt), iteratedDeriv_const_mul_field]
  rw [congrFun (iteratedDeriv_comp_const_sub r f L) x]

private theorem contDiff_finitePoleFunction (L c : ℝ) (hL : 0 < L) :
    ContDiff ℝ (⊤ : ℕ∞) (localizedFiniteFunction L (originalDetectorQuarticCutoff L)
      (originalDetectorFinitePoleImageCoefficients UniversalSinc.fixedScale L c hL)) := by
  unfold localizedFiniteFunction
  apply ContDiff.sum
  intro i hi
  exact contDiff_const.mul ((contDiff_localizedMode L _).of_le le_top)

theorem recenteredFiniteApprox_jet_error {L c : ℝ} (hL : 2 ≤ L)
    (hleft : 1+UniversalSinc.fixedScale ≤ c)
    (hright : c+UniversalSinc.fixedScale ≤ L-1)
    (σ : ℝ) (r : ℕ) {x : ℝ} (hx : x ∈ Icc 0 L) :
    ‖iteratedDeriv r (recenteredSmoothPhase σ L c) x -
      iteratedDeriv r (recenteredFiniteApprox σ L c (by linarith)) x‖ ≤
      fixedOriginalSincTrialNormalization * (1+|σ|) *
        originalDetectorFinitePoleImageJetBudget UniversalSinc.fixedScale L r := by
  have hLp : 0 < L := by linarith
  have hL2 := hL
  let f : ℝ → ℂ := fun y => originalSincTest UniversalSinc.fixedScale (y - c)
  let g := localizedFiniteFunction L (originalDetectorQuarticCutoff L)
    (originalDetectorFinitePoleImageCoefficients UniversalSinc.fixedScale L c hLp)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (contDiff_originalSincTest UniversalSinc.fixedScale_pos).comp
      (contDiff_id.sub contDiff_const)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_finitePoleFunction L c hLp
  have htrial : recenteredSmoothPhase σ L c =
      fun y => (fixedOriginalSincTrialNormalization : ℂ) *
        (f y + (σ : ℂ) * f (L - y)) := by
    funext y
    rfl
  have hfinite : recenteredFiniteApprox σ L c hLp =
      fun y => (fixedOriginalSincTrialNormalization : ℂ) *
        (g y + (σ : ℂ) * g (L - y)) := by
    funext y
    unfold recenteredFiniteApprox
    rw [originalDetectorFinitePhaseVector_physical_formula]
  have hx' : L - x ∈ Icc (0 : ℝ) L := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h1 := originalDetectorFinitePoleImage_iteratedDeriv_error_le_budget
    UniversalSinc.fixedScale_pos hL2 hleft hright r hx
  have h2 := originalDetectorFinitePoleImage_iteratedDeriv_error_le_budget
    UniversalSinc.fixedScale_pos hL2 hleft hright r hx'
  rw [htrial, hfinite, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_reflectionCombination hf, iteratedDeriv_reflectionCombination hg, ← mul_sub,
    norm_mul]
  have heq : (iteratedDeriv r f x + (σ : ℂ) * ((-1 : ℝ) ^ r • iteratedDeriv r f (L - x))) -
      (iteratedDeriv r g x + (σ : ℂ) * ((-1 : ℝ) ^ r • iteratedDeriv r g (L - x))) =
      (iteratedDeriv r f x - iteratedDeriv r g x) +
      (σ : ℂ) * ((-1 : ℝ) ^ r • (iteratedDeriv r f (L - x) - iteratedDeriv r g (L - x))) := by
    simp only [smul_sub]
    ring
  rw [heq]
  have hnorm : ‖(fixedOriginalSincTrialNormalization : ℂ)‖ =
      fixedOriginalSincTrialNormalization := by
    simp [abs_of_pos fixedOriginalSincTrialNormalization_pos]
  rw [hnorm]
  refine (mul_le_mul_of_nonneg_left (norm_add_le _ _)
    fixedOriginalSincTrialNormalization_pos.le).trans ?_
  rw [norm_mul, norm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hh := add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg σ))
  have hh' := mul_le_mul_of_nonneg_left hh
    fixedOriginalSincTrialNormalization_pos.le
  convert! hh' using 1 <;> ring

private theorem tsupport_iteratedDeriv_subset (r : ℕ) (f : ℝ → ℂ) :
    tsupport (iteratedDeriv r f) ⊆ tsupport f := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem recenteredFiniteHard_L1_error {L c : ℝ} (hL : 2 ≤ L)
    (hleft : 1+UniversalSinc.fixedScale ≤ c)
    (hright : c+UniversalSinc.fixedScale ≤ L-1) (σ : ℝ) {r : ℕ} (hr : r ≤ 2) :
    (∫ x : ℝ, ‖iteratedDeriv r (recenteredFiniteHard σ L c (by linarith) -
      recenteredSmoothPhase σ L c) x‖) ≤ L *
      (fixedOriginalSincTrialNormalization*(1+|σ|)*
        originalDetectorFinitePoleImageJetBudget UniversalSinc.fixedScale L r) := by
  have hLp : 0 < L := by linarith
  let p := recenteredFiniteHard σ L c hLp
  let h := recenteredSmoothPhase σ L c
  have hp : ContDiff ℝ 2 p := recenteredFiniteHard_contDiff hL σ c
  have hh : ContDiff ℝ 2 h := (recenteredSmoothPhase_contDiff σ L c).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hpc : ∀ x ∉ Icc (0 : ℝ) L, p x = 0 := by
    intro x hx
    dsimp [p, recenteredFiniteHard]
    rw [localizedFiniteVector_eq_indicator, Set.indicator_of_notMem hx, mul_zero]
  have hhc : ∀ x ∉ Icc (0 : ℝ) L, h x = 0 := by
    intro x hx
    exact recenteredSmoothPhase_zero_outside hleft hright σ hx
  have hsupp : tsupport (p - h) ⊆ Icc (0 : ℝ) L := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hout
    exact hx (by simp [Pi.sub_apply, hpc x hout, hhc x hout])
  have hjetcont : Continuous (iteratedDeriv r (p - h)) := by
    apply (hp.sub hh).continuous_iteratedDeriv r
    exact_mod_cast hr
  apply integral_norm_le_length_mul_of_support_Icc hLp.le hjetcont
  · exact subset_closure.trans ((tsupport_iteratedDeriv_subset r (p - h)).trans hsupp)
  · intro x hx
    have hpr : ContDiff ℝ r p := hp.of_le (by exact_mod_cast hr)
    have hhr : ContDiff ℝ r h := hh.of_le (by exact_mod_cast hr)
    rw [iteratedDeriv_sub hpr.contDiffAt hhr.contDiffAt]
    have hlocal : iteratedDeriv r p x =
        iteratedDeriv r (recenteredFiniteApprox σ L c hLp) x := by
      let u := (EuclideanSpace.equiv (Fin (2 * originalDetectorQuarticCutoff L + 1)) ℂ)
        (originalDetectorFinitePhaseVector σ L c hLp)
      change iteratedDeriv r (fun y => (fixedOriginalSincTrialNormalization : ℂ) *
        localizedFiniteVector L (originalDetectorQuarticCutoff L) u y) x =
        iteratedDeriv r (fun y => (fixedOriginalSincTrialNormalization : ℂ) *
          localizedFiniteFunction L (originalDetectorQuarticCutoff L) u y) x
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
      congr 1
      apply iteratedDeriv_localizedFiniteVector_eq_formula_on_interval hLp _ _ _ hr hx
      dsimp only [u]
      rw [originalDetectorFinitePhaseVector_raw]
      exact originalDetectorFinitePhaseRaw_boundaryFlat σ _ hL
    rw [hlocal, norm_sub_rev]
    exact recenteredFiniteApprox_jet_error hL hleft hright σ r hx

private theorem recentered_L1_common {L c σ : ℝ} (hL : 2 ≤ L)
    (hleft : 1+UniversalSinc.fixedScale ≤ c)
    (hright : c+UniversalSinc.fixedScale ≤ L-1)
    (hσ : σ=1 ∨ σ= -1) {r : ℕ} (hr : r ≤ 2) :
    (∫ x : ℝ, ‖iteratedDeriv r (recenteredFiniteHard σ L c (by linarith) -
      recenteredSmoothPhase σ L c) x‖) ≤ originalDetectorFinitePhaseL1ErrorBudget L r := by
  have he := recenteredFiniteHard_L1_error hL hleft hright σ hr
  have hs : |σ|=1 := by rcases hσ with rfl | rfl <;> norm_num
  rw [hs] at he
  convert he using 1 <;> unfold originalDetectorFinitePhaseL1ErrorBudget <;> ring

theorem recenteredFinitePhase_Weil_error {L c σ : ℝ} (hL : 2 ≤ L)
    (hleft : 1+UniversalSinc.fixedScale ≤ c)
    (hright : c+UniversalSinc.fixedScale ≤ L-1) (hσ : σ=1 ∨ σ= -1) :
    ‖zetaZeroConfig.W (recenteredFiniteHard σ L c (by linarith))
      (recenteredFiniteHard σ L c (by linarith)) -
      zetaZeroConfig.W (recenteredSmoothPhase σ L c) (recenteredSmoothPhase σ L c)‖ ≤
      originalDetectorFinitePhaseWeilErrorBudget L := by
  have hLp : 0 < L := by linarith
  let p := recenteredFiniteHard σ L c hLp
  let h := recenteredSmoothPhase σ L c
  let E0 := originalDetectorFinitePhaseL1ErrorBudget L 0
  let E2 := originalDetectorFinitePhaseL1ErrorBudget L 2
  let H0 := originalDetectorOriginalPhaseL1JetBudget 0
  let H2 := originalDetectorOriginalPhaseL1JetBudget 2
  have hp : ContDiff ℝ 2 p := recenteredFiniteHard_contDiff hL σ c
  have hh : ContDiff ℝ 2 h := (recenteredSmoothPhase_contDiff σ L c).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hpsupp : ∀ x, p x ≠ 0 → |x| ≤ L := by
    intro x hx
    have hv : localizedFiniteVector L (originalDetectorQuarticCutoff L)
        ((EuclideanSpace.equiv (Fin (2 * originalDetectorQuarticCutoff L + 1)) ℂ)
          (originalDetectorFinitePhaseVector σ L c hLp)) x ≠ 0 := by
      intro hz
      apply hx
      change (fixedOriginalSincTrialNormalization : ℂ) * _ = 0
      rw [hz, mul_zero]
    have hb := localizedFiniteVector_support_subset L _ _ hv
    rw [abs_of_nonneg hb.1]
    exact hb.2
  have hhsupp : ∀ x, h x ≠ 0 → |x| ≤ L := by
    intro x hx
    have hm : x ∈ Icc (0 : ℝ) L := by
      by_contra hout
      exact hx (recenteredSmoothPhase_zero_outside hleft hright σ hout)
    rw [abs_of_nonneg hm.1]
    exact hm.2
  have he0 : (∫ x : ℝ, ‖(p - h) x‖) ≤ E0 := by
    simpa only [iteratedDeriv_zero] using recentered_L1_common hL hleft hright hσ (r := 0) (by norm_num)
  have he2 : (∫ x : ℝ, ‖deriv (deriv (p - h)) x‖) ≤ E2 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      recentered_L1_common hL hleft hright hσ (r := 2) (by norm_num)
  have hH0 : (∫ x : ℝ, ‖h x‖) ≤ H0 := by
    simpa only [iteratedDeriv_zero] using recenteredSmoothPhase_L1_bound hσ L c 0
  have hH2 : (∫ x : ℝ, ‖deriv (deriv h) x‖) ≤ H2 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      recenteredSmoothPhase_L1_bound hσ L c 2
  have hpI : Integrable p volume := hp.continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_of_support_subset_abs hpsupp)
  have hhI : Integrable h volume := hh.continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_of_support_subset_abs hhsupp)
  have heI : Integrable (p - h) volume := hpI.sub hhI
  have hP0 : (∫ x : ℝ, ‖p x‖) ≤ E0 + H0 := by
    have htri (x : ℝ) : ‖p x‖ ≤ ‖(p - h) x‖ + ‖h x‖ := by
      convert norm_add_le ((p - h) x) (h x) using 1 <;> simp only [Pi.sub_apply, sub_add_cancel]
    calc
      _ ≤ ∫ x : ℝ, ‖(p - h) x‖ + ‖h x‖ := integral_mono hpI.norm (heI.norm.add hhI.norm) htri
      _ = (∫ x : ℝ, ‖(p - h) x‖) + ∫ x : ℝ, ‖h x‖ := integral_add heI.norm hhI.norm
      _ ≤ _ := add_le_add he0 hH0
  have hE0n : 0 ≤ E0 := (integral_nonneg (fun x => norm_nonneg ((p - h) x))).trans he0
  have hE2n : 0 ≤ E2 := (integral_nonneg (fun x => norm_nonneg (deriv (deriv (p - h)) x))).trans he2
  have hH0n : 0 ≤ H0 := (integral_nonneg (fun x => norm_nonneg (h x))).trans hH0
  have hH2n : 0 ≤ H2 := (integral_nonneg (fun x => norm_nonneg (deriv (deriv h) x))).trans hH2
  have hfirst := mul_le_mul (add_le_add he0 he2) hP0
    (integral_nonneg (fun x => norm_nonneg (p x))) (add_nonneg hE0n hE2n)
  have hsecond := mul_le_mul (add_le_add hH0 hH2) he0
    (integral_nonneg (fun x => norm_nonneg ((p - h) x))) (add_nonneg hH0n hH2n)
  have hW := zeta_W_self_sub_self_norm_le_commonSupport hLp.le hp hh hpsupp hhsupp
  exact hW.trans (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond)
    (mul_nonneg (Real.exp_pos L).le zetaInvSqZeroMass_nonneg))

private theorem localizedFiniteVector_smul_eq (L : ℝ) (K : ℕ) (u : Fin (2 * K + 1) → ℂ) (z : ℂ) :
    localizedFiniteVector L K (z • u) = fun x => z * localizedFiniteVector L K u x := by
  funext x
  unfold localizedFiniteVector
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem re_inner_apply_smul_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ[ℂ] E) (v : E) (t : ℝ) :
    (inner ℂ (A ((t : ℂ) • v)) ((t : ℂ) • v)).re = t ^ 2 * (inner ℂ (A v) v).re := by
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero]
  ring

theorem recenteredFiniteHard_Weil_eq_native {L : ℝ} (hL : 2 ≤ L) (σ c : ℝ) :
    (zetaZeroConfig.W (recenteredFiniteHard σ L c (by linarith))
      (recenteredFiniteHard σ L c (by linarith))).re =
      fixedOriginalSincTrialNormalization^2 *
        (inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
          (originalDetectorFinitePhaseVector σ L c (by linarith)))
          (originalDetectorFinitePhaseVector σ L c (by linarith))).re := by
  have hLp : 0 < L := by linarith
  let K := originalDetectorQuarticCutoff L
  let v := originalDetectorFinitePhaseVector σ L c hLp
  let u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) v
  let η := fixedOriginalSincTrialNormalization
  have hflat : BoundaryFlatCoefficients K u := by
    dsimp [u, v]
    rw [originalDetectorFinitePhaseVector_raw]
    exact originalDetectorFinitePhaseRaw_boundaryFlat σ _ hL
  have hflatScaled : BoundaryFlatCoefficients K ((η : ℂ) • u) := by
    apply (mem_boundaryFlatSubspace_iff _ _).mp
    apply (boundaryFlatSubspace K).smul_mem
    exact (mem_boundaryFlatSubspace_iff _ _).mpr hflat
  have hp : localizedFiniteVector L K ((η : ℂ) • u) =
      recenteredFiniteHard σ L c hLp := localizedFiniteVector_smul_eq L K u η
  have hW := congrArg Complex.re
    (zeta_W_boundaryFlatFiniteVector_eq_canonicalSourceQuadraticForm K ((η : ℂ) • u) hLp hflatScaled)
  rw [hp] at hW
  have hquad : (quadraticForm (canonicalSourceMatrix L K) ((η : ℂ) • u)).re =
      (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin ((η : ℂ) • v)) ((η : ℂ) • v)).re := by
    simpa only [map_smul] using
      quadraticForm_re_eq_re_inner_apply_self (canonicalSourceMatrix L K) ((η : ℂ) • v)
  exact hW.trans (hquad.trans (re_inner_apply_smul_self _ v η))




/-- Center translation changes only the aperture placement, not the complete
genuine Weil energy or any zero multiplicity. -/
theorem recenteredSmoothPhase_fixed_energy (σ a L : ℝ) :
    zetaZeroConfig.W (recenteredSmoothPhase σ L (L/2-a))
      (recenteredSmoothPhase σ L (L/2-a)) =
      zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a)
        (fixedOriginalSincPhaseTrial σ a) := by
  rw [recenteredSmoothPhase_eq_translate]
  have he : L/2-(L/2-a)=a := by ring
  rw [he, W_translateRight_self]

/-- Each genuine negative smooth phase survives at every sufficiently large
aperture, in the unchanged actual quartic coordinates. The depth is fixed
after selecting the smooth phase; it is not asserted to grow with L. -/
theorem recentered_negative_phase_eventually_quartic {σ a : ℝ}
    (hσ : σ=1 ∨ σ= -1) (ha : UniversalSinc.fixedScale < a)
    (hneg : (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a)
      (fixedOriginalSincPhaseTrial σ a)).re < 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ L : ℝ in atTop, ∃ hL : 2 ≤ L,
      (inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
        (originalDetectorFinitePhaseVector σ L (L/2-a) (by linarith)))
        (originalDetectorFinitePhaseVector σ L (L/2-a) (by linarith))).re < -d := by
  let W := (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a)
    (fixedOriginalSincPhaseTrial σ a)).re
  let n := fixedOriginalSincTrialNormalization
  let d := (-W)/(2*n^2)
  have hW : W < 0 := hneg
  have hn : 0 < n := fixedOriginalSincTrialNormalization_pos
  have hd : 0 < d := div_pos (neg_pos.mpr hW)
    (mul_pos (by norm_num) (sq_pos_of_pos hn))
  refine ⟨d, hd, ?_⟩
  have hlim := originalDetectorFinitePhaseWeilErrorBudget_mul_exp_tendsto_zero 0
  simp only [zero_mul, Real.exp_zero, mul_one] at hlim
  have hsmall := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < -W/2 by linarith))
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop (fixedOriginalSincTrialAperture a), hsmall] with L hL hLa he
  refine ⟨hL, ?_⟩
  have hleft : 1+UniversalSinc.fixedScale ≤ L/2-a := by
    dsimp [fixedOriginalSincTrialAperture, fixedOriginalSincLobeCenter] at hLa
    linarith
  have hright : L/2-a+UniversalSinc.fixedScale ≤ L-1 := by
    have ha0 := UniversalSinc.fixedScale_pos.trans ha
    linarith
  have hb := recenteredFinitePhase_Weil_error hL hleft hright hσ
  rw [recenteredSmoothPhase_fixed_energy] at hb
  have hr := (Complex.re_le_norm
    (zetaZeroConfig.W (recenteredFiniteHard σ L (L/2-a) (by linarith))
      (recenteredFiniteHard σ L (L/2-a) (by linarith)) -
      zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a)
        (fixedOriginalSincPhaseTrial σ a))).trans hb
  rw [Complex.sub_re, recenteredFiniteHard_Weil_eq_native hL] at hr
  have hdn : n^2*d = -W/2 := by
    dsimp [d]
    field_simp
  dsimp only [W,n] at hdn hr he
  nlinarith [sq_pos_of_pos fixedOriginalSincTrialNormalization_pos]

theorem exists_fixed_negative_original_phase (ρ : zetaZeroConfig.carrier)
    (hoff : (ρ : ℂ).re ≠ 1/2) {σ : ℝ} (hσ : σ=1 ∨ σ= -1) :
    ∃ a : ℝ, UniversalSinc.fixedScale < a ∧
      (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a)
        (fixedOriginalSincPhaseTrial σ a)).re < 0 := by
  let β := |(ρ : ℂ).re-1/2|/2
  have hδ : 0 < |(ρ : ℂ).re-1/2| := abs_pos.mpr (sub_ne_zero.mpr hoff)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβρ : β < |(ρ : ℂ).re-1/2| := by dsimp [β]; linarith
  obtain ⟨a, hlate, _, _, hdepth⟩ := exists_fixedOriginalSincPhaseTrial_depth_of_off_line_zero
    ρ hβ hβρ hσ (2*UniversalSinc.fixedScale+2*fixedOriginalSincLobeCenter)
  have ha : UniversalSinc.fixedScale < a := by
    have hh := (le_max_left (2*UniversalSinc.fixedScale+2*fixedOriginalSincLobeCenter) 4).trans_lt hlate
    dsimp [fixedOriginalSincTrialAperture] at hh
    linarith
  refine ⟨a, ha, ?_⟩
  rw [← fixedOriginalSincPhaseTrial_Weil_eq_native] at hdepth
  exact hdepth.trans_lt (neg_neg_of_pos (Real.exp_pos _))

/-- Actual parity-specific sources, each at the very same mandated K(L),
exist at every sufficiently large aperture under an off-line zero. -/
theorem eventually_both_negative_at_original_quartic (ρ : zetaZeroConfig.carrier)
    (hoff : (ρ : ℂ).re ≠ 1/2) :
    ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧
      BothNeutralNegative L (originalDetectorQuarticCutoff L) := by
  obtain ⟨ae, hae, he⟩ := exists_fixed_negative_original_phase ρ hoff (Or.inl rfl)
  obtain ⟨ao, hao, ho⟩ := exists_fixed_negative_original_phase ρ hoff (Or.inr rfl)
  obtain ⟨de, hde, he⟩ := recentered_negative_phase_eventually_quartic (Or.inl rfl) hae he
  obtain ⟨do', hdo, ho⟩ := recentered_negative_phase_eventually_quartic (Or.inr rfl) hao ho
  filter_upwards [he, ho] with L he ho
  obtain ⟨hL, he⟩ := he
  obtain ⟨_, ho⟩ := ho
  refine ⟨hL, ?_, ?_⟩
  · refine ⟨originalDetectorFiniteEvenPhase (L/2-ae) hL, ?_⟩
    rw [inner_poleNeutralEvenCompressedCanonical_self]
    change (inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
      (originalDetectorFinitePhaseVector 1 L (L/2-ae) (by linarith)))
      (originalDetectorFinitePhaseVector 1 L (L/2-ae) (by linarith))).re < 0
    exact he.trans (neg_neg_of_pos hde)
  · refine ⟨originalDetectorFiniteOddPhase (L/2-ao) hL, ?_⟩
    rw [inner_poleNeutralOddCompressedCanonical_self]
    change (inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
      (originalDetectorFinitePhaseVector (-1) L (L/2-ao) (by linarith)))
      (originalDetectorFinitePhaseVector (-1) L (L/2-ao) (by linarith))).re < 0
    exact ho.trans (neg_neg_of_pos hdo)

theorem cofinally_both_negative_at_original_quartic (ρ : zetaZeroConfig.carrier)
    (hoff : (ρ : ℂ).re ≠ 1/2) (R : ℝ) :
    ∃ L : ℝ, R < L ∧ 0 < L ∧ 3 ≤ originalDetectorQuarticCutoff L ∧
      BothNeutralNegative L (originalDetectorQuarticCutoff L) := by
  obtain ⟨L, hLR, hL, hboth⟩ :=
    (eventually_gt_atTop R).and (eventually_both_negative_at_original_quartic ρ hoff) |>.exists
  have hK := originalDetectorQuarticCutoff_ge_sixteen hL
  exact ⟨L,hLR,by linarith,by omega,hboth⟩



open CCM ExceptionalZero OPICARound3

/-- One threshold, chosen before any packet, synchronizes both native
parities and the full joint ground constraints at that packet's detector
cutoff. Its selected Schur cutoff is retained separately. -/
theorem every_late_generated_packet_has_joint_detector_ground
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1/2) :
    ∃ R0 : ℝ, ∀ (β : ℝ) (p : ReversalParity) (R : ℝ), R0 ≤ R →
      ∀ out : GeneratedStep123ComposedEvidencePacket ρ β p R,
      let g := out.integrated.boundary.generated
      let native := g.native
      let L := fixedOriginalSincTrialAperture g.sourceData.separation
      let Kd := originalDetectorQuarticCutoff L
      let hKd : 3 ≤ Kd := native.retained.state.selection.cutoff_nonempty.trans
        native.retained.state.selection.cutoff_le_detector
      BothNeutralNegative L Kd ∧
        NativeJointGroundConstraints native.aperture_pos Kd hKd ∧
        ‖native.retained.state.detector‖ = 1 ∧
        (inner ℂ (nativePoleNeutralParityCanonical p L Kd native.retained.state.detector)
          native.retained.state.detector).re ≤ -Real.exp (β*L) ∧
        native.retained.state.selection.cutoff ≤ Kd := by
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp
    (eventually_both_negative_at_original_quartic ρ hoff)
  refine ⟨R0, ?_⟩
  intro β p R hR out
  dsimp only
  let g := out.integrated.boundary.generated
  let native := g.native
  let L := fixedOriginalSincTrialAperture g.sourceData.separation
  have hlate : R < L := (le_max_left R 4).trans_lt g.native_aperture_bound
  have hb := (hR0 L (hR.trans hlate.le)).2
  refine ⟨hb, joint_ground_constraints_of_both_negative native.aperture_pos _ _ hb,
    native.retained.state.detector_unit, native.retained.state.detector_depth,
    native.retained.state.selection.cutoff_le_detector⟩

/-- The actual first common cutoff is bounded by the synchronized detector
cutoff. Each parity still has its own predecessor and Schur alternative. -/
theorem first_common_cutoff_le_original_quartic {L : ℝ} (hL : 2 ≤ L)
    (hboth : BothNeutralNegative L (originalDetectorQuarticCutoff L)) :
    ∃ Ke Ko : ℕ, 3 ≤ Ke ∧ 3 ≤ Ko ∧
      EvenNeutralNegative L Ke ∧ OddNeutralNegative L Ko ∧
      BothNeutralNegative L (max Ke Ko) ∧ max Ke Ko ≤ originalDetectorQuarticCutoff L ∧
      PoleNeutralParityPSD .even L (Ke-1) ∧ PoleNeutralParityPSD .odd L (Ko-1) ∧
      NeutralNewbornSchur .even L Ke ∧ NeutralNewbornSchur .odd L Ko := by
  have hLp : 0 < L := by linarith
  have hKd : 3 ≤ originalDetectorQuarticCutoff L := by
    have h := originalDetectorQuarticCutoff_ge_sixteen hL
    omega
  obtain ⟨Ke, Ko, hKe, hKo, he, ho, _, _, hc, hmin, hpe, hpo, hse, hso, _, _⟩ :=
    first_simultaneous_neutral_negative_cutoff hLp hKd hboth
  exact ⟨Ke,Ko,hKe,hKo,he,ho,hc,hmin _ hKd hboth,hpe,hpo,hse,hso⟩


end Zeta23.OPICARound4
