import Zeta23.CCM.Components
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Ordered minors of the actual positive off-diagonal gain. This is not a
statement about the signed Weil form, a compression, or a semigroup. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal BigOperators ArithmeticFunction

namespace Zeta23.OPICARound2

def nativeJumpWidth : ℝ := 1/1000
def nativeJumpSpacing : ℝ := 1/10
def nativeJumpRow (i : Fin 2) : Set ℝ :=
  Icc (Real.log 2 + ((i:ℕ)+1)*nativeJumpSpacing)
    (Real.log 2 + ((i:ℕ)+1)*nativeJumpSpacing + nativeJumpWidth)
def nativeJumpColumn (j : Fin 2) : Set ℝ :=
  Icc ((j:ℕ)*nativeJumpSpacing) ((j:ℕ)*nativeJumpSpacing+nativeJumpWidth)

/-- Literal line-atom overlap: the pushforward of dy along y ↦ (y+a,y). -/
def nativeJumpOverlap (a : ℝ) (I J : Set ℝ) : ℝ :=
  volume.real {y : ℝ | y∈J ∧ y+a∈I}

def nativeJumpArchRectangle (I J : Set ℝ) : ℝ :=
  ∫ p : ℝ×ℝ in I ×ˢ J, CCM.archDensity |p.1-p.2|

/-- Restriction of the prime-plus-Archimedean gain to a bounded square.
Each translated line has its actual von-Mangoldt weight, with no extra two. -/
def nativeJumpGainRectangle (R : ℝ) (I J : Set ℝ) : ℝ :=
  nativeJumpArchRectangle I J +
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp R⌋₊,
      (Λ n / Real.sqrt n : ℝ) *
        (nativeJumpOverlap (Real.log n) I J + nativeJumpOverlap (-Real.log n) I J)

theorem native_jump_rectangle_geometry (i j : Fin 2)
    {x y : ℝ} (hx : x∈nativeJumpRow i) (hy : y∈nativeJumpColumn j) :
    0≤y ∧ y<x ∧ 1/2<x-y ∧ x-y<1 ∧ x<1 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [nativeJumpRow,nativeJumpColumn,nativeJumpWidth,nativeJumpSpacing] at *
  all_goals rcases hx with ⟨hxl,hxu⟩; rcases hy with ⟨hyl,hyu⟩
  all_goals refine ⟨?_,?_,?_,?_,?_⟩ <;>
    linarith [Real.log_two_gt_d9,Real.log_two_lt_d9]

theorem native_jump_rows_and_columns_ordered :
    (∀ x∈nativeJumpRow 0, ∀ y∈nativeJumpRow 1, x<y) ∧
    (∀ x∈nativeJumpColumn 0, ∀ y∈nativeJumpColumn 1, x<y) := by
  constructor <;> intro x hx y hy <;>
    norm_num [nativeJumpRow,nativeJumpColumn,nativeJumpWidth,nativeJumpSpacing] at *
  all_goals rcases hx with ⟨hxl,hxu⟩; rcases hy with ⟨hyl,hyu⟩; linarith

theorem native_jump_arch_density_bounds {t : ℝ} (ht : 1/2<t) (ht1 : t<1) :
    1/2<CCM.archDensity t ∧ CCM.archDensity t<2 := by
  have he : CCM.archDensity t = Real.exp (-t/2)/(1-Real.exp (-2*t)) := by
    unfold CCM.archDensity
    have hn : Real.exp t - Real.exp (-t) ≠ 0 :=
      ne_of_gt (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith)))
    have hd : 1-Real.exp (-2*t) ≠ 0 :=
      ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
    apply (div_eq_div_iff hn hd).mpr
    simp_rw [mul_sub,mul_one,←Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  have hhalf : Real.exp (1/2)<2 := by
    have hh : Real.exp (1/2)^2=Real.exp 1 := by
      rw [pow_two,←Real.exp_add]
      norm_num
    nlinarith [Real.exp_one_lt_three,Real.exp_pos (1/2)]
  have hnegHalf : 1/2<Real.exp (-1/2) := by
    rw [show (-1/2:ℝ)= -(1/2:ℝ) by ring,Real.exp_neg]
    have hh : (1/2:ℝ)<1/Real.exp (1/2) :=
      (lt_div_iff₀ (Real.exp_pos _)).mpr (by linarith)
    simpa only [one_div] using hh
  have hnum : 1/2<Real.exp (-t/2) :=
    hnegHalf.trans (Real.exp_lt_exp.mpr (by linarith))
  have hnum1 : Real.exp (-t/2)<1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hinv : Real.exp (-1)<1/2 := by
    rw [Real.exp_neg]
    have hh : 1 / Real.exp (1:ℝ) < 1/2 :=
      (div_lt_iff₀ (Real.exp_pos _)).mpr (by linarith [Real.exp_one_gt_two])
    simpa only [one_div] using hh
  have hden : 1/2<1-Real.exp (-2*t) := by
    have := Real.exp_lt_exp.mpr (show -2*t < -1 by linarith)
    linarith
  rw [he]
  constructor
  · apply (lt_div_iff₀ (by linarith : 0<1-Real.exp (-2*t))).mpr
    nlinarith [Real.exp_pos (-2*t)]
  · apply (div_lt_iff₀ (by linarith : 0<1-Real.exp (-2*t))).mpr
    linarith

theorem native_jump_prime_two_weight : (1/3:ℝ)<Real.log 2 / Real.sqrt 2 := by
  have hs0 : 0<Real.sqrt 2 := by positivity
  have hs : Real.sqrt 2 < 3/2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  apply (lt_div_iff₀ hs0).mpr
  linarith [Real.log_two_gt_d9]

theorem native_jump_only_prime_two_overlap (i j : Fin 2) {n : ℕ} (hn : 3≤n) :
    nativeJumpOverlap (Real.log n) (nativeJumpRow i) (nativeJumpColumn j)=0 ∧
    nativeJumpOverlap (-Real.log n) (nativeJumpRow i) (nativeJumpColumn j)=0 := by
  have hlog3 : 1<Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
  have hlog : 1<Real.log n := hlog3.trans_le
    (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
  have hpos : 0<Real.log n := by linarith
  have hzero (a : ℝ) (ha : a<0 ∨ 1<a) :
      nativeJumpOverlap a (nativeJumpRow i) (nativeJumpColumn j)=0 := by
    unfold nativeJumpOverlap
    have he : {y : ℝ | y∈nativeJumpColumn j ∧
        y + a ∈ nativeJumpRow i} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y ⟨hy,hx⟩
      have hg := native_jump_rectangle_geometry i j hx hy
      rcases ha with ha | ha <;> linarith [hg.2.1,hg.2.2.2.1]
    rw [he,measureReal_empty]
  exact ⟨hzero _ (Or.inr hlog),hzero _ (Or.inl (by linarith))⟩

theorem native_jump_prime_two_overlap (i j : Fin 2) :
    nativeJumpOverlap (Real.log 2) (nativeJumpRow i) (nativeJumpColumn j)=
      if i=0 ∧ j=1 then nativeJumpWidth else 0 := by
  have hzero (i j : Fin 2)
      (hsep : ∀ y∈nativeJumpColumn j, y+Real.log 2 ∉ nativeJumpRow i) :
      nativeJumpOverlap (Real.log 2) (nativeJumpRow i) (nativeJumpColumn j)=0 := by
    unfold nativeJumpOverlap
    have he : {y : ℝ | y∈nativeJumpColumn j ∧ y+Real.log 2∈nativeJumpRow i}=∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun y hy => hsep y hy.1 hy.2)
    rw [he,measureReal_empty]
  fin_cases i <;> fin_cases j
  · change nativeJumpOverlap (Real.log 2) (nativeJumpRow 0) (nativeJumpColumn 0)=0
    apply hzero 0 0
    intro y hy hx
    norm_num [nativeJumpColumn,nativeJumpRow,nativeJumpWidth,nativeJumpSpacing] at hy hx
    linarith [hy.1,hy.2,hx.1,hx.2]
  · change nativeJumpOverlap (Real.log 2) (nativeJumpRow 0) (nativeJumpColumn 1)=nativeJumpWidth
    have he : {y : ℝ | y∈nativeJumpColumn 1 ∧ y+Real.log 2∈nativeJumpRow 0}
        = Icc (1/10) (101/1000) := by
      ext y
      norm_num [nativeJumpColumn,nativeJumpRow,nativeJumpWidth,nativeJumpSpacing]
      intro hyl hyu
      constructor <;> linarith
    unfold nativeJumpOverlap
    rw [he,Real.volume_real_Icc_of_le (by norm_num)]
    norm_num [nativeJumpWidth]
  · change nativeJumpOverlap (Real.log 2) (nativeJumpRow 1) (nativeJumpColumn 0)=0
    apply hzero 1 0
    intro y hy hx
    norm_num [nativeJumpColumn,nativeJumpRow,nativeJumpWidth,nativeJumpSpacing] at hy hx
    linarith [hy.1,hy.2,hx.1,hx.2]
  · change nativeJumpOverlap (Real.log 2) (nativeJumpRow 1) (nativeJumpColumn 1)=0
    apply hzero 1 1
    intro y hy hx
    norm_num [nativeJumpColumn,nativeJumpRow,nativeJumpWidth,nativeJumpSpacing] at hy hx
    linarith [hy.1,hy.2,hx.1,hx.2]

theorem native_jump_negative_two_overlap (i j : Fin 2) :
    nativeJumpOverlap (-Real.log 2) (nativeJumpRow i) (nativeJumpColumn j)=0 := by
  unfold nativeJumpOverlap
  have he : {y : ℝ | y∈nativeJumpColumn j ∧ y+ -Real.log 2∈nativeJumpRow i}=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y ⟨hy,hx⟩
    have hg := native_jump_rectangle_geometry i j hx hy
    linarith [hg.2.1,Real.log_two_gt_d9]
  rw [he,measureReal_empty]

theorem native_jump_rectangle_volume (i j : Fin 2) :
    volume.real (nativeJumpRow i ×ˢ nativeJumpColumn j)=nativeJumpWidth^2 := by
  change ((volume:Measure ℝ).prod volume).real (_ ×ˢ _)=_
  rw [measureReal_prod_prod]
  have hi : volume.real (nativeJumpRow i)=nativeJumpWidth := by
    unfold nativeJumpRow
    rw [Real.volume_real_Icc_of_le (by unfold nativeJumpWidth; linarith)]
    ring
  have hj : volume.real (nativeJumpColumn j)=nativeJumpWidth := by
    unfold nativeJumpColumn
    rw [Real.volume_real_Icc_of_le (by unfold nativeJumpWidth; linarith)]
    ring
  rw [hi,hj,pow_two]

theorem native_jump_arch_rectangle_bounds (i j : Fin 2) :
    nativeJumpWidth^2/2 < nativeJumpArchRectangle (nativeJumpRow i) (nativeJumpColumn j) ∧
    nativeJumpArchRectangle (nativeJumpRow i) (nativeJumpColumn j)<2*nativeJumpWidth^2 := by
  let Q : Set (ℝ×ℝ) := nativeJumpRow i ×ˢ nativeJumpColumn j
  let f : ℝ×ℝ → ℝ := fun p => CCM.archDensity |p.1-p.2|
  have hQ : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hQm : MeasurableSet Q := hQ.measurableSet
  have hg (p : ℝ×ℝ) (hp : p∈Q) :
      1/2<f p ∧ f p<2 := by
    have hb := native_jump_rectangle_geometry i j hp.1 hp.2
    dsimp [f]
    rw [abs_of_pos (sub_pos.mpr hb.2.1)]
    exact native_jump_arch_density_bounds hb.2.2.1 hb.2.2.2.1
  have hc : ContinuousOn f Q := by
    unfold f CCM.archDensity
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro p hp
    have hb := native_jump_rectangle_geometry i j hp.1 hp.2
    apply ne_of_gt
    apply sub_pos.mpr
    apply Real.exp_lt_exp.mpr
    rw [abs_of_pos (sub_pos.mpr hb.2.1)]
    linarith [hb.2.1]
  have hi : IntegrableOn f Q := hc.integrableOn_compact hQ
  have hconstant (c : ℝ) : IntegrableOn (fun _ : ℝ×ℝ => c) Q :=
    continuousOn_const.integrableOn_compact hQ
  have hmeasure : 0<volume Q := by
    have hv : 0<volume.real Q := by
      rw [native_jump_rectangle_volume]
      norm_num [nativeJumpWidth]
    exact ENNReal.toReal_pos_iff.mp hv |>.1
  have hl : 0<∫ p in Q, f p-1/2 := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (show 0≤ᵐ[volume.restrict Q] (fun p => f p-1/2) from by
        filter_upwards [ae_restrict_mem hQm] with p hp
        exact sub_nonneg.mpr (hg p hp).1.le) (hi.sub (hconstant (1/2)))).mpr
    have he : Function.support (fun p => f p-1/2) ∩ Q=Q := by
      ext p
      constructor
      · exact fun hp => hp.2
      · intro hp
        exact ⟨ne_of_gt (sub_pos.mpr (hg p hp).1),hp⟩
    rw [he]
    exact hmeasure
  have hu : 0<∫ p in Q, 2-f p := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (show 0≤ᵐ[volume.restrict Q] (fun p => 2-f p) from by
        filter_upwards [ae_restrict_mem hQm] with p hp
        exact sub_nonneg.mpr (hg p hp).2.le) ((hconstant 2).sub hi)).mpr
    have he : Function.support (fun p => 2-f p) ∩ Q=Q := by
      ext p
      constructor
      · exact fun hp => hp.2
      · intro hp
        exact ⟨ne_of_gt (sub_pos.mpr (hg p hp).2),hp⟩
    rw [he]
    exact hmeasure
  rw [integral_sub hi (hconstant (1/2)),setIntegral_const,smul_eq_mul] at hl
  rw [integral_sub (hconstant 2) hi,setIntegral_const,smul_eq_mul] at hu
  have hv : volume.real Q=nativeJumpWidth^2 := native_jump_rectangle_volume i j
  rw [hv] at hl hu
  change nativeJumpWidth^2/2<(∫ p in Q, f p) ∧ (∫ p in Q, f p)<2*nativeJumpWidth^2
  constructor <;> linarith

theorem native_jump_gain_rectangle_identity (R : ℝ) (hR : 1≤R) (i j : Fin 2) :
    nativeJumpGainRectangle R (nativeJumpRow i) (nativeJumpColumn j)=
      nativeJumpArchRectangle (nativeJumpRow i) (nativeJumpColumn j) +
        if i=0 ∧ j=1 then Real.log 2 / Real.sqrt 2 * nativeJumpWidth else 0 := by
  have hfloor : 2≤⌊Real.exp R⌋₊ := Nat.le_floor
    ((Real.exp_one_gt_two.le).trans (Real.exp_le_exp.mpr hR))
  unfold nativeJumpGainRectangle
  congr 1
  rw [Finset.sum_eq_single 2]
  · norm_num only [Nat.cast_ofNat]
    rw [native_jump_prime_two_overlap,native_jump_negative_two_overlap,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    split_ifs <;> simp
  · intro n hn hne
    have hn3 : 3≤n := by have := (Finset.mem_Icc.mp hn).1; omega
    rw [(native_jump_only_prime_two_overlap i j hn3).1,
      (native_jump_only_prime_two_overlap i j hn3).2]
    simp
  · intro hn
    exact False.elim (hn (Finset.mem_Icc.mpr ⟨le_rfl,hfloor⟩))

theorem native_jump_gain_negative_ordered_minor (R : ℝ) (hR : 1≤R) :
    nativeJumpGainRectangle R (nativeJumpRow 0) (nativeJumpColumn 0) *
      nativeJumpGainRectangle R (nativeJumpRow 1) (nativeJumpColumn 1) -
    nativeJumpGainRectangle R (nativeJumpRow 0) (nativeJumpColumn 1) *
      nativeJumpGainRectangle R (nativeJumpRow 1) (nativeJumpColumn 0)
        < -(61/375000000000:ℝ) := by
  have h00 := native_jump_arch_rectangle_bounds 0 0
  have h01 := native_jump_arch_rectangle_bounds 0 1
  have h10 := native_jump_arch_rectangle_bounds 1 0
  have h11 := native_jump_arch_rectangle_bounds 1 1
  rw [native_jump_gain_rectangle_identity R hR,native_jump_gain_rectangle_identity R hR,
    native_jump_gain_rectangle_identity R hR,native_jump_gain_rectangle_identity R hR]
  norm_num only [Fin.zero_eta,Fin.isValue,zero_ne_one,one_ne_zero,and_false,if_false,if_true,
    and_self,add_zero] at *
  have hc := native_jump_prime_two_weight
  norm_num [nativeJumpWidth] at h00 h01 h10 h11 ⊢
  nlinarith

/-- A concrete smooth replacement of each interval indicator. Its flat middle
half suffices to preserve the negative minor with an explicit smaller margin. -/
def nativeJumpWindowBump (a : ℝ) : ContDiffBump (a+nativeJumpWidth/2) :=
  ⟨nativeJumpWidth/4,nativeJumpWidth/2,by norm_num [nativeJumpWidth],
    by norm_num [nativeJumpWidth]⟩

def nativeJumpWindowTest (a : ℝ) : ℝ→ℝ := nativeJumpWindowBump a

def nativeJumpWindowInner (a : ℝ) : Set ℝ :=
  Icc (a+nativeJumpWidth/4) (a+3*nativeJumpWidth/4)

theorem native_jump_window_test_smooth (a : ℝ) :
    ContDiff ℝ (⊤:ℕ∞) (nativeJumpWindowTest a) := (nativeJumpWindowBump a).contDiff

theorem native_jump_window_test_bounds (a x : ℝ) :
    0≤nativeJumpWindowTest a x ∧ nativeJumpWindowTest a x≤1 :=
  ⟨(nativeJumpWindowBump a).nonneg,(nativeJumpWindowBump a).le_one⟩

theorem native_jump_window_tsupport (a : ℝ) :
    tsupport (nativeJumpWindowTest a) ⊆ Icc a (a+nativeJumpWidth) := by
  intro x hx
  change x ∈ tsupport (nativeJumpWindowBump a) at hx
  rw [ContDiffBump.tsupport_eq] at hx
  have hd : |x-(a+nativeJumpWidth/2)|≤nativeJumpWidth/2 := by
    simpa [nativeJumpWindowBump,Metric.mem_closedBall,Real.dist_eq] using hx
  obtain ⟨hl,hu⟩ := abs_le.mp hd
  exact ⟨by linarith,by linarith⟩

theorem native_jump_window_test_zero (a : ℝ) {x : ℝ} (hx : x∉Icc a (a+nativeJumpWidth)) :
    nativeJumpWindowTest a x=0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (native_jump_window_tsupport a h))

theorem native_jump_window_inner_subset (a : ℝ) :
    nativeJumpWindowInner a ⊆ Icc a (a+nativeJumpWidth) := by
  intro x hx
  unfold nativeJumpWindowInner at hx
  constructor <;> linarith [hx.1,hx.2,show (0:ℝ)<nativeJumpWidth by norm_num [nativeJumpWidth]]

theorem native_jump_window_test_one (a : ℝ) {x : ℝ} (hx : x∈nativeJumpWindowInner a) :
    nativeJumpWindowTest a x=1 := by
  apply (nativeJumpWindowBump a).one_of_mem_closedBall
  change |x-(a+nativeJumpWidth/2)|≤nativeJumpWidth/4
  exact abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩

theorem native_jump_window_inner_volume (a : ℝ) :
    volume.real (nativeJumpWindowInner a)=nativeJumpWidth/2 := by
  unfold nativeJumpWindowInner
  rw [Real.volume_real_Icc_of_le (by norm_num [nativeJumpWidth])]
  ring

theorem native_jump_window_square_mass (a : ℝ) :
    nativeJumpWidth/2≤∫ y in Icc a (a+nativeJumpWidth), (nativeJumpWindowTest a y)^2 := by
  have hi : IntegrableOn (fun y => (nativeJumpWindowTest a y)^2)
      (Icc a (a+nativeJumpWidth)) :=
    ((native_jump_window_test_smooth a).continuous.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hsub := native_jump_window_inner_subset a
  have hinner : (∫ y in nativeJumpWindowInner a, (nativeJumpWindowTest a y)^2)=nativeJumpWidth/2 := by
    calc
      _ = ∫ _ in nativeJumpWindowInner a, (1:ℝ) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro y hy
        change (nativeJumpWindowTest a y)^2=1
        rw [native_jump_window_test_one a hy]
        norm_num
      _ = _ := by rw [setIntegral_const,smul_eq_mul,native_jump_window_inner_volume,mul_one]
  rw [←hinner]
  exact setIntegral_mono_set hi (Eventually.of_forall fun y => sq_nonneg _)
    (Eventually.of_forall hsub)

def nativeJumpRowTest (i : Fin 2) : ℝ→ℝ :=
  nativeJumpWindowTest (Real.log 2+((i:ℕ)+1)*nativeJumpSpacing)

def nativeJumpColumnTest (j : Fin 2) : ℝ→ℝ :=
  nativeJumpWindowTest ((j:ℕ)*nativeJumpSpacing)

def nativeJumpSmoothArch (i j : Fin 2) : ℝ :=
  ∫ p : ℝ×ℝ in nativeJumpRow i ×ˢ nativeJumpColumn j,
    CCM.archDensity |p.1-p.2| * (nativeJumpRowTest i p.1*nativeJumpColumnTest j p.2)

theorem native_jump_arch_continuous (i j : Fin 2) :
    ContinuousOn (fun p : ℝ×ℝ => CCM.archDensity |p.1-p.2|)
      (nativeJumpRow i ×ˢ nativeJumpColumn j) := by
  unfold CCM.archDensity
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro p hp
  have hb := native_jump_rectangle_geometry i j hp.1 hp.2
  apply ne_of_gt
  apply sub_pos.mpr
  apply Real.exp_lt_exp.mpr
  rw [abs_of_pos (sub_pos.mpr hb.2.1)]
  linarith [hb.2.1]

theorem native_jump_smooth_arch_bounds (i j : Fin 2) :
    nativeJumpWidth^2/8≤nativeJumpSmoothArch i j ∧
      nativeJumpSmoothArch i j≤2*nativeJumpWidth^2 := by
  let a : ℝ := Real.log 2+((i:ℕ)+1)*nativeJumpSpacing
  let b : ℝ := (j:ℕ)*nativeJumpSpacing
  let Q : Set (ℝ×ℝ) := nativeJumpRow i ×ˢ nativeJumpColumn j
  let S : Set (ℝ×ℝ) := nativeJumpWindowInner a ×ˢ nativeJumpWindowInner b
  let f : ℝ×ℝ→ℝ := fun p => CCM.archDensity |p.1-p.2| *
    (nativeJumpRowTest i p.1*nativeJumpColumnTest j p.2)
  have hsub : S⊆Q := Set.prod_mono (native_jump_window_inner_subset a)
    (native_jump_window_inner_subset b)
  have hF : ContinuousOn f Q := (native_jump_arch_continuous i j).mul
    (((native_jump_window_test_smooth a).continuous.comp continuous_fst).mul
      ((native_jump_window_test_smooth b).continuous.comp continuous_snd)).continuousOn
  have hi : IntegrableOn f Q := hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hnonneg (p : ℝ×ℝ) (hp : p∈Q) : 0≤f p := by
    have hg := native_jump_rectangle_geometry i j hp.1 hp.2
    have hb := native_jump_arch_density_bounds hg.2.2.1 hg.2.2.2.1
    dsimp [f]
    rw [abs_of_pos (sub_pos.mpr hg.2.1)]
    exact mul_nonneg (by linarith [hb.1])
      (mul_nonneg (native_jump_window_test_bounds a p.1).1
        (native_jump_window_test_bounds b p.2).1)
  have hupper : (∫ p in Q,f p)≤2*nativeJumpWidth^2 := by
    calc
      _ ≤ ∫ _ in Q,(2:ℝ) := by
        apply setIntegral_mono_on hi
          (continuousOn_const.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
          (measurableSet_Icc.prod measurableSet_Icc)
        intro p hp
        have hg := native_jump_rectangle_geometry i j hp.1 hp.2
        have hb := native_jump_arch_density_bounds hg.2.2.1 hg.2.2.2.1
        dsimp [f]
        rw [abs_of_pos (sub_pos.mpr hg.2.1)]
        have hprod : nativeJumpRowTest i p.1*nativeJumpColumnTest j p.2≤1 :=
          (mul_le_mul (native_jump_window_test_bounds a p.1).2
            (native_jump_window_test_bounds b p.2).2
              (native_jump_window_test_bounds b p.2).1 (by norm_num)).trans_eq (by norm_num)
        calc
          _ ≤ 2*(nativeJumpRowTest i p.1*nativeJumpColumnTest j p.2) :=
            mul_le_mul_of_nonneg_right hb.2.le
              (mul_nonneg (native_jump_window_test_bounds a p.1).1
                (native_jump_window_test_bounds b p.2).1)
          _ ≤ 2 := by linarith
      _ = _ := by rw [setIntegral_const,smul_eq_mul,native_jump_rectangle_volume]; ring
  have hmeasure : volume.real S=(nativeJumpWidth/2)^2 := by
    change ((volume:Measure ℝ).prod volume).real (_ ×ˢ _)=_
    rw [measureReal_prod_prod,native_jump_window_inner_volume,native_jump_window_inner_volume,pow_two]
  have hlower : nativeJumpWidth^2/8≤∫ p in Q,f p := by
    calc
      _ = ∫ _ in S,(1/2:ℝ) := by rw [setIntegral_const,smul_eq_mul,hmeasure]; ring
      _ ≤ ∫ p in S,f p := by
        apply setIntegral_mono_on
          (continuousOn_const.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
          (hi.mono_set hsub) (measurableSet_Icc.prod measurableSet_Icc)
        intro p hp
        have hg := native_jump_rectangle_geometry i j (hsub hp).1 (hsub hp).2
        have hb := native_jump_arch_density_bounds hg.2.2.1 hg.2.2.2.1
        dsimp [f,nativeJumpRowTest,nativeJumpColumnTest]
        rw [native_jump_window_test_one a hp.1,native_jump_window_test_one b hp.2,
          one_mul,mul_one,abs_of_pos (sub_pos.mpr hg.2.1)]
        exact hb.1.le
      _ ≤ _ := setIntegral_mono_set hi
        (by filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
            exact hnonneg p hp) (Eventually.of_forall hsub)
  exact ⟨hlower,hupper⟩

def nativeJumpSmoothLine (a : ℝ) (i j : Fin 2) : ℝ :=
  ∫ y in nativeJumpColumn j, nativeJumpRowTest i (y+a)*nativeJumpColumnTest j y

theorem native_jump_smooth_line_zero_of_overlap (a : ℝ) (i j : Fin 2)
    (h : nativeJumpOverlap a (nativeJumpRow i) (nativeJumpColumn j)=0) :
    nativeJumpSmoothLine a i j=0 := by
  let S : Set ℝ := {y : ℝ | y∈nativeJumpColumn j ∧ y+a∈nativeJumpRow i}
  have hfinite : volume S≠∞ := ne_of_lt
    ((measure_mono (show S⊆nativeJumpColumn j from fun _ hy => hy.1)).trans_lt
      isCompact_Icc.measure_lt_top)
  have hzero : volume S=0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right hfinite
  have hae := measure_eq_zero_iff_ae_notMem.mp hzero
  unfold nativeJumpSmoothLine
  calc
    _ = ∫ _ in nativeJumpColumn j, (0:ℝ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hae] with y hy hn
      have hx : y+a∉nativeJumpRow i := fun hx => hn ⟨hy,hx⟩
      change nativeJumpRowTest i (y+a)*nativeJumpColumnTest j y=0
      rw [nativeJumpRowTest,native_jump_window_test_zero _ hx,zero_mul]
    _ = 0 := by simp

theorem native_jump_smooth_line_nonneg (a : ℝ) (i j : Fin 2) :
    0≤nativeJumpSmoothLine a i j :=
  integral_nonneg fun y => mul_nonneg
    (native_jump_window_test_bounds _ (y+a)).1 (native_jump_window_test_bounds _ y).1

theorem native_jump_smooth_two_line_lower :
    nativeJumpWidth/2≤nativeJumpSmoothLine (Real.log 2) 0 1 := by
  let b : ℝ := (1:Fin 2).val*nativeJumpSpacing
  let S : Set ℝ := nativeJumpWindowInner b
  let J : Set ℝ := nativeJumpColumn 1
  let f : ℝ→ℝ := fun y => nativeJumpRowTest 0 (y+Real.log 2)*nativeJumpColumnTest 1 y
  have hsub : S⊆J := native_jump_window_inner_subset b
  have hc : Continuous f := by
    apply Continuous.mul
    · exact (native_jump_window_test_smooth _).continuous.comp (continuous_id.add_const _)
    · exact (native_jump_window_test_smooth _).continuous
  have hi : IntegrableOn f J := hc.continuousOn.integrableOn_compact isCompact_Icc
  have he (y : ℝ) (hy : y∈S) : f y=1 := by
    have hrow : y+Real.log 2∈nativeJumpWindowInner
        (Real.log 2+((0:Fin 2).val+1)*nativeJumpSpacing) := by
      norm_num [S,b,nativeJumpWindowInner,nativeJumpWidth,nativeJumpSpacing] at hy ⊢
      exact ⟨by linarith [hy.1],by linarith [hy.2]⟩
    dsimp [f,nativeJumpRowTest,nativeJumpColumnTest]
    have hr := native_jump_window_test_one _ hrow
    have ht := native_jump_window_test_one b hy
    norm_num [b,nativeJumpSpacing] at hr ht ⊢
    rw [hr,ht]
    norm_num
  calc
    _ = ∫ _ in S,(1:ℝ) := by rw [setIntegral_const,smul_eq_mul,native_jump_window_inner_volume,mul_one]
    _ = ∫ y in S,f y := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      exact (he y hy).symm
    _ ≤ ∫ y in J,f y := setIntegral_mono_set hi
      (Eventually.of_forall fun y => mul_nonneg (native_jump_window_test_bounds _ _).1
        (native_jump_window_test_bounds _ _).1) (Eventually.of_forall hsub)

def nativeJumpSmoothGain (R : ℝ) (i j : Fin 2) : ℝ :=
  nativeJumpSmoothArch i j + ∑ n ∈ Finset.Icc 2 ⌊Real.exp R⌋₊,
    (Λ n/Real.sqrt n : ℝ)*(nativeJumpSmoothLine (Real.log n) i j+
      nativeJumpSmoothLine (-Real.log n) i j)

theorem native_jump_smooth_gain_identity (R : ℝ) (hR : 1≤R) (i j : Fin 2) :
    nativeJumpSmoothGain R i j=nativeJumpSmoothArch i j+
      if i=0 ∧ j=1 then Real.log 2/Real.sqrt 2*nativeJumpSmoothLine (Real.log 2) i j else 0 := by
  have hfloor : 2≤⌊Real.exp R⌋₊ := Nat.le_floor
    ((Real.exp_one_gt_two.le).trans (Real.exp_le_exp.mpr hR))
  unfold nativeJumpSmoothGain
  congr 1
  rw [Finset.sum_eq_single 2]
  · norm_num only [Nat.cast_ofNat]
    rw [native_jump_smooth_line_zero_of_overlap _ i j (native_jump_negative_two_overlap i j),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,add_zero]
    split_ifs with h
    · rfl
    · rw [native_jump_smooth_line_zero_of_overlap _ i j
        (by rw [native_jump_prime_two_overlap,if_neg h]),mul_zero]
  · intro n hn hne
    have hn3 : 3≤n := by have := (Finset.mem_Icc.mp hn).1; omega
    rw [native_jump_smooth_line_zero_of_overlap _ i j
      (native_jump_only_prime_two_overlap i j hn3).1,
      native_jump_smooth_line_zero_of_overlap _ i j
        (native_jump_only_prime_two_overlap i j hn3).2]
    simp
  · intro hn
    exact False.elim (hn (Finset.mem_Icc.mpr ⟨le_rfl,hfloor⟩))

/-- Four explicit smooth nonnegative tests retain a strictly negative minor.
The smaller margin pays for keeping only the flat middle half of each test. -/
theorem native_jump_smooth_negative_ordered_minor (R : ℝ) (hR : 1≤R) :
    nativeJumpSmoothGain R 0 0*nativeJumpSmoothGain R 1 1-
      nativeJumpSmoothGain R 0 1*nativeJumpSmoothGain R 1 0<0 := by
  have h00 := native_jump_smooth_arch_bounds 0 0
  have h01 := native_jump_smooth_arch_bounds 0 1
  have h10 := native_jump_smooth_arch_bounds 1 0
  have h11 := native_jump_smooth_arch_bounds 1 1
  have hc := native_jump_prime_two_weight
  have hline := native_jump_smooth_two_line_lower
  rw [native_jump_smooth_gain_identity R hR,native_jump_smooth_gain_identity R hR,
    native_jump_smooth_gain_identity R hR,native_jump_smooth_gain_identity R hR]
  norm_num only [Fin.zero_eta,Fin.isValue,zero_ne_one,one_ne_zero,and_false,if_false,if_true,
    and_self,add_zero] at *
  let c : ℝ := Real.log 2/Real.sqrt 2
  let l : ℝ := nativeJumpSmoothLine (Real.log 2) 0 1
  have hprod : (1/6000:ℝ)<c*l := by
    have hc0 : 0≤c := by dsimp [c]; linarith
    have hm := mul_le_mul_of_nonneg_left hline hc0
    norm_num [nativeJumpWidth] at hm
    dsimp [c,l]
    nlinarith
  norm_num [nativeJumpWidth] at h00 h01 h10 h11 ⊢
  change nativeJumpSmoothArch 0 0*nativeJumpSmoothArch 1 1 <
    (nativeJumpSmoothArch 0 1+c*l)*nativeJumpSmoothArch 1 0
  have hcross : (1/6000:ℝ)≤nativeJumpSmoothArch 0 1+c*l := by linarith [h01.1]
  have hmin := mul_le_mul_of_nonneg_right hcross (show 0≤nativeJumpSmoothArch 1 0 by linarith [h10.1])
  have hdiag := mul_le_mul h00.2 h11.2 (show 0≤nativeJumpSmoothArch 1 1 by linarith [h11.1])
    (by norm_num : (0:ℝ)≤1/500000)
  nlinarith

theorem native_jump_smooth_arch_full (i j : Fin 2) :
    nativeJumpSmoothArch i j = ∫ p : ℝ×ℝ,
      CCM.archDensity |p.1-p.2| * (nativeJumpRowTest i p.1*nativeJumpColumnTest j p.2) := by
  unfold nativeJumpSmoothArch
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  by_cases hx : p.1∈nativeJumpRow i
  · have hy : p.2∉nativeJumpColumn j := fun hy => hp ⟨hx,hy⟩
    rw [nativeJumpColumnTest,native_jump_window_test_zero _ hy,mul_zero,mul_zero]
  · rw [nativeJumpRowTest,native_jump_window_test_zero _ hx,zero_mul,mul_zero]

theorem native_jump_smooth_line_full (a : ℝ) (i j : Fin 2) :
    nativeJumpSmoothLine a i j =
      ∫ y : ℝ, nativeJumpRowTest i (y+a)*nativeJumpColumnTest j y := by
  unfold nativeJumpSmoothLine
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  rw [nativeJumpColumnTest,native_jump_window_test_zero _ hy,mul_zero]

theorem native_jump_smooth_tests :
    (∀ i : Fin 2, ContDiff ℝ (⊤:ℕ∞) (nativeJumpRowTest i) ∧
      HasCompactSupport (nativeJumpRowTest i) ∧
      tsupport (nativeJumpRowTest i) ⊆ nativeJumpRow i ∧
      ∀ x : ℝ, 0≤nativeJumpRowTest i x ∧ nativeJumpRowTest i x≤1) ∧
    (∀ j : Fin 2, ContDiff ℝ (⊤:ℕ∞) (nativeJumpColumnTest j) ∧
      HasCompactSupport (nativeJumpColumnTest j) ∧
      tsupport (nativeJumpColumnTest j) ⊆ nativeJumpColumn j ∧
      ∀ y : ℝ, 0≤nativeJumpColumnTest j y ∧ nativeJumpColumnTest j y≤1) := by
  constructor <;> intro i
  all_goals exact ⟨native_jump_window_test_smooth _,(nativeJumpWindowBump _).hasCompactSupport,
    native_jump_window_tsupport _,native_jump_window_test_bounds _⟩

end Zeta23.OPICARound2
