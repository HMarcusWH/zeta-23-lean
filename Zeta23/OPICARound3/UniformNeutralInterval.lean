import Zeta23.OPICARound3.CofinalSimultaneousNegative
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section

namespace Zeta23.OPICARound3

open CCM Matrix Set Filter
open scoped BigOperators Topology ComplexConjugate

def unitNormalize {K : ℕ} (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    EuclideanSpace ℂ (Fin (2 * K + 1)) := (‖u‖ : ℂ)⁻¹ • u

@[simp] theorem unitNormalize_zero (K : ℕ) :
    unitNormalize (0 : EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 := by
  simp [unitNormalize]

theorem norm_unitNormalize {K : ℕ} {u : EuclideanSpace ℂ (Fin (2 * K + 1))}
    (hu : u ≠ 0) : ‖unitNormalize u‖ = 1 := by
  simpa [unitNormalize] using (norm_smul_inv_norm (𝕜 := ℂ) hu)

theorem continuousAt_unitNormalize {K : ℕ}
    (u : ℝ → EuclideanSpace ℂ (Fin (2 * K + 1))) {L : ℝ}
    (hu : ContinuousAt u L) (hne : u L ≠ 0) :
    ContinuousAt (fun t => unitNormalize (u t)) L := by
  have hn : ContinuousAt (fun t => (‖u t‖ : ℂ)) L :=
    Complex.continuous_ofReal.continuousAt.comp hu.norm
  exact (hn.inv₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hne))).smul hu

theorem fullCanonicalEnergy_smul (L : ℝ) (K : ℕ) (c : ℂ)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    fullCanonicalEnergy L K (c • u) = ‖c‖ ^ 2 * fullCanonicalEnergy L K u := by
  unfold fullCanonicalEnergy
  rw [map_smul, inner_smul_left, inner_smul_right]
  have hc : star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.star_def, Complex.ofReal_pow] using (Complex.conj_mul' c)
  calc
    (star c * (c * inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin u) u)).re =
        ((star c * c) * inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin u) u).re := by
          congr 1
          ring
    _ = _ := by
      rw [hc]
      simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]

theorem unitNormalize_negative {L : ℝ} {K : ℕ}
    {u : EuclideanSpace ℂ (Fin (2 * K + 1))} (h : fullCanonicalEnergy L K u < 0) :
    fullCanonicalEnergy L K (unitNormalize u) < 0 := by
  have hu := negative_fullCanonicalEnergy_ne_zero h
  have hc : (‖u‖ : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu))
  rw [unitNormalize, fullCanonicalEnergy_smul]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos (norm_pos_iff.mpr hc)) h

theorem unitNormalize_input_ne_zero {L : ℝ} {K : ℕ}
    {u : EuclideanSpace ℂ (Fin (2 * K + 1))}
    (h : fullCanonicalEnergy L K (unitNormalize u) < 0) : u ≠ 0 := by
  intro hu
  rw [hu, unitNormalize_zero, fullCanonicalEnergy_zero] at h
  exact (lt_irrefl 0) h

theorem inner_even_odd_eq_zero (K : ℕ)
    (u v : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hu : u ∈ euclideanEvenBoundaryFlatSubspace K)
    (hv : v ∈ euclideanOddBoundaryFlatSubspace K) : inner ℂ u v = 0 := by
  have he := (mem_evenCoefficientSubspace_iff K _).mp
    ((mem_euclideanEvenBoundaryFlatSubspace_iff K u).mp hu).2
  have ho := (mem_oddCoefficientSubspace_iff K _).mp
    ((mem_euclideanOddBoundaryFlatSubspace_iff K v).mp hv).2
  have hes : reverseCoefficients K (star u.ofLp) = star u.ofLp := by
    funext i
    exact congrArg star (congrFun he i)
  have hz := dotProduct_eq_zero_of_reverse_odd_even K
    v.ofLp (star u.ofLp) ho hes
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hz

theorem fullCanonicalEnergy_even_odd_add (L : ℝ) (K : ℕ)
    (u v : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hu : u ∈ euclideanEvenBoundaryFlatSubspace K)
    (hv : v ∈ euclideanOddBoundaryFlatSubspace K) :
    fullCanonicalEnergy L K (u + v) = fullCanonicalEnergy L K u + fullCanonicalEnergy L K v := by
  let ru := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) u
  let rv := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) v
  have he : reverseCoefficients K ru = ru :=
    (mem_evenCoefficientSubspace_iff K ru).mp ((mem_euclideanEvenBoundaryFlatSubspace_iff K u).mp hu).2
  have ho : reverseCoefficients K rv = -rv :=
    (mem_oddCoefficientSubspace_iff K rv).mp ((mem_euclideanOddBoundaryFlatSubspace_iff K v).mp hv).2
  have hpartE : evenPart K (ru + rv) = ru := by
    funext i
    have hei := congrFun he i
    have hoi := congrFun ho i
    change (1 / 2 : ℂ) * ((ru i + rv i) + (ru i.rev + rv i.rev)) = ru i
    change ru i.rev = ru i at hei
    change rv i.rev = -rv i at hoi
    rw [hei, hoi]
    ring
  have hpartO : oddPart K (ru + rv) = rv := by
    funext i
    have hei := congrFun he i
    have hoi := congrFun ho i
    change (1 / 2 : ℂ) * ((ru i + rv i) - (ru i.rev + rv i.rev)) = rv i
    change ru i.rev = ru i at hei
    change rv i.rev = -rv i at hoi
    rw [hei, hoi]
    ring
  have hsum := congrArg Complex.re (quadraticForm_evenPart_add_oddPart L K (ru + rv))
  rw [hpartE, hpartO, Complex.add_re] at hsum
  unfold fullCanonicalEnergy
  rw [← quadraticForm_re_eq_re_inner_apply_self (canonicalSourceMatrix L K) (u + v),
    ← quadraticForm_re_eq_re_inner_apply_self (canonicalSourceMatrix L K) u,
    ← quadraticForm_re_eq_re_inner_apply_self (canonicalSourceMatrix L K) v]
  exact hsum.symm

theorem fullCanonicalEnergy_parity_combination (L : ℝ) (K : ℕ)
    (u v : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hu : u ∈ euclideanEvenBoundaryFlatSubspace K)
    (hv : v ∈ euclideanOddBoundaryFlatSubspace K) (c d : ℂ) :
    fullCanonicalEnergy L K (c • u + d • v) =
      ‖c‖ ^ 2 * fullCanonicalEnergy L K u + ‖d‖ ^ 2 * fullCanonicalEnergy L K v := by
  rw [fullCanonicalEnergy_even_odd_add L K (c • u) (d • v)
    ((euclideanEvenBoundaryFlatSubspace K).smul_mem c hu)
    ((euclideanOddBoundaryFlatSubspace K).smul_mem d hv),
    fullCanonicalEnergy_smul, fullCanonicalEnergy_smul]

theorem parity_unit_frame_orthonormal (K : ℕ)
    (u v : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hu : u ∈ euclideanEvenBoundaryFlatSubspace K)
    (hv : v ∈ euclideanOddBoundaryFlatSubspace K)
    (hnu : ‖u‖ = 1) (hnv : ‖v‖ = 1) : Orthonormal ℂ ![u, v] := by
  have huv := inner_even_odd_eq_zero K u v hu hv
  have hvu : inner ℂ v u = 0 := inner_eq_zero_symm.mp huv
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [inner_self_eq_norm_sq_to_K, hnu, hnv, huv, hvu]

theorem parity_unit_frame_norm_sq (K : ℕ)
    (u v : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hu : u ∈ euclideanEvenBoundaryFlatSubspace K)
    (hv : v ∈ euclideanOddBoundaryFlatSubspace K)
    (hnu : ‖u‖ = 1) (hnv : ‖v‖ = 1) (c d : ℂ) :
    ‖c • u + d • v‖ ^ 2 = ‖c‖ ^ 2 + ‖d‖ ^ 2 := by
  have hcross : inner ℂ (c • u) (d • v) = 0 := by
    simp [inner_smul_left, inner_smul_right, inner_even_odd_eq_zero K u v hu hv]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _ hcross
  simpa only [pow_two, norm_smul, hnu, hnv, mul_one] using h

/-- An actual continuously varying two-dimensional negative frame on one
closed interval. The cutoff and margin are fixed on this interval only. -/
structure UniformNeutralNegativeFrame (a b : ℝ) (K : ℕ) (η : ℝ) where
  even : ℝ → EuclideanSpace ℂ (Fin (2 * K + 1))
  odd : ℝ → EuclideanSpace ℂ (Fin (2 * K + 1))
  even_continuous : ContinuousOn even (Icc a b)
  odd_continuous : ContinuousOn odd (Icc a b)
  even_legal : ∀ L ∈ Icc a b, even L ∈ euclideanEvenBoundaryFlatSubspace K
  odd_legal : ∀ L ∈ Icc a b, odd L ∈ euclideanOddBoundaryFlatSubspace K
  even_pole : ∀ L ∈ Icc a b, canonicalPoleEvenFunctional L K (even L) = 0
  odd_pole : ∀ L ∈ Icc a b, canonicalPoleOddFunctional L K (odd L) = 0
  even_unit : ∀ L ∈ Icc a b, ‖even L‖ = 1
  odd_unit : ∀ L ∈ Icc a b, ‖odd L‖ = 1
  orthonormal : ∀ L ∈ Icc a b, Orthonormal ℂ ![even L, odd L]
  energy_le : ∀ L ∈ Icc a b, ∀ c d : ℂ,
    fullCanonicalEnergy L K (c • even L + d • odd L) ≤ -η * (‖c‖ ^ 2 + ‖d‖ ^ 2)

theorem exists_uniform_neutral_interval_of_both {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (hboth : BothNeutralNegative L K)
    (R : ℝ) (hRL : R < L) :
    ∃ a b η : ℝ, R < a ∧ 0 < a ∧ a < b ∧ 0 < η ∧
      Nonempty (UniformNeutralNegativeFrame a b K η) := by
  obtain ⟨u, hu, hpu, hEu⟩ := (evenNeutralNegative_iff_ambient L K).mp hboth.1
  obtain ⟨v, hv, hpv, hEv⟩ := (oddNeutralNegative_iff_ambient L K).mp hboth.2
  let hK₂ : 2 ≤ K := by omega
  let ue := neutralRepair .even K hK₂ u
  let vo := neutralRepair .odd K hK₂ v
  let e : ℝ → EuclideanSpace ℂ (Fin (2 * K + 1)) := fun t => unitNormalize (ue t)
  let o : ℝ → EuclideanSpace ℂ (Fin (2 * K + 1)) := fun t => unitNormalize (vo t)
  have hue : ue L = u := neutralRepair_eq_self .even L K hK₂ u hpu
  have hvo : vo L = v := neutralRepair_eq_self .odd L K hK₂ v hpv
  have hueNeg : fullCanonicalEnergy L K (ue L) < 0 := by rw [hue]; exact hEu
  have hvoNeg : fullCanonicalEnergy L K (vo L) < 0 := by rw [hvo]; exact hEv
  have heNeg : fullCanonicalEnergy L K (e L) < 0 := unitNormalize_negative hueNeg
  have hoNeg : fullCanonicalEnergy L K (o L) < 0 := unitNormalize_negative hvoNeg
  have heCont : ContinuousAt e L := continuousAt_unitNormalize ue
    (continuousAt_neutralRepair .even K hK₂ u hL) (negative_fullCanonicalEnergy_ne_zero hueNeg)
  have hoCont : ContinuousAt o L := continuousAt_unitNormalize vo
    (continuousAt_neutralRepair .odd K hK₂ v hL) (negative_fullCanonicalEnergy_ne_zero hvoNeg)
  let η := min (-fullCanonicalEnergy L K (e L) / 2) (-fullCanonicalEnergy L K (o L) / 2)
  have hη : 0 < η := by
    apply lt_min <;> linarith
  have heSmall : fullCanonicalEnergy L K (e L) < -η := by
    have hm := min_le_left (-fullCanonicalEnergy L K (e L) / 2)
      (-fullCanonicalEnergy L K (o L) / 2)
    change η ≤ -fullCanonicalEnergy L K (e L) / 2 at hm
    linarith
  have hoSmall : fullCanonicalEnergy L K (o L) < -η := by
    have hm := min_le_right (-fullCanonicalEnergy L K (e L) / 2)
      (-fullCanonicalEnergy L K (o L) / 2)
    change η ≤ -fullCanonicalEnergy L K (o L) / 2 at hm
    linarith
  have heEvent : ∀ᶠ t in 𝓝 L, fullCanonicalEnergy t K (e t) < -η :=
    (continuousAt_fullCanonicalEnergy K e hL heCont).tendsto.eventually
      (isOpen_Iio.mem_nhds heSmall)
  have hoEvent : ∀ᶠ t in 𝓝 L, fullCanonicalEnergy t K (o t) < -η :=
    (continuousAt_fullCanonicalEnergy K o hL hoCont).tendsto.eventually
      (isOpen_Iio.mem_nhds hoSmall)
  have hEvent : ∀ᶠ t in 𝓝 L,
      fullCanonicalEnergy t K (e t) < -η ∧ fullCanonicalEnergy t K (o t) < -η := by
    filter_upwards [heEvent, hoEvent] with t he ho
    exact ⟨he, ho⟩
  obtain ⟨δ, hδ, hδmem⟩ := Metric.eventually_nhds_iff.mp hEvent
  let r := min (δ / 2) (min ((L - R) / 2) (L / 2))
  have hr : 0 < r := by
    apply lt_min
    · positivity
    · apply lt_min <;> linarith
  have hrδ : r < δ := (min_le_left _ _).trans_lt (by linarith)
  have hrR : r ≤ (L - R) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrL : r ≤ L / 2 := (min_le_right _ _).trans (min_le_right _ _)
  let a := L - r
  let b := L + r
  have hRa : R < a := by dsimp [a]; linarith
  have ha : 0 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a, b]; linarith
  have htpos : ∀ t ∈ Icc a b, 0 < t := fun t ht => ha.trans_le ht.1
  have hGood : ∀ t ∈ Icc a b,
      fullCanonicalEnergy t K (e t) < -η ∧ fullCanonicalEnergy t K (o t) < -η := by
    intro t ht
    apply hδmem
    rw [Real.dist_eq]
    have ht' : |t - L| ≤ r := by
      apply abs_le.mpr
      dsimp [a, b] at ht
      constructor <;> linarith [ht.1, ht.2]
    exact ht'.trans_lt hrδ
  have hueNZ : ∀ t ∈ Icc a b, ue t ≠ 0 := by
    intro t ht
    exact unitNormalize_input_ne_zero ((hGood t ht).1.trans (neg_lt_zero.mpr hη))
  have hvoNZ : ∀ t ∈ Icc a b, vo t ≠ 0 := by
    intro t ht
    exact unitNormalize_input_ne_zero ((hGood t ht).2.trans (neg_lt_zero.mpr hη))
  have heLegal : ∀ t ∈ Icc a b, e t ∈ euclideanEvenBoundaryFlatSubspace K := by
    intro t _
    exact (euclideanEvenBoundaryFlatSubspace K).smul_mem _
      (neutralRepair_mem .even K hK₂ u hu t)
  have hoLegal : ∀ t ∈ Icc a b, o t ∈ euclideanOddBoundaryFlatSubspace K := by
    intro t _
    exact (euclideanOddBoundaryFlatSubspace K).smul_mem _
      (neutralRepair_mem .odd K hK₂ v hv t)
  have heUnit : ∀ t ∈ Icc a b, ‖e t‖ = 1 := fun t ht => norm_unitNormalize (hueNZ t ht)
  have hoUnit : ∀ t ∈ Icc a b, ‖o t‖ = 1 := fun t ht => norm_unitNormalize (hvoNZ t ht)
  refine ⟨a, b, η, hRa, ha, hab, hη, ⟨{
    even := e
    odd := o
    even_continuous := ?_
    odd_continuous := ?_
    even_legal := heLegal
    odd_legal := hoLegal
    even_pole := ?_
    odd_pole := ?_
    even_unit := heUnit
    odd_unit := hoUnit
    orthonormal := fun t ht => parity_unit_frame_orthonormal K (e t) (o t)
      (heLegal t ht) (hoLegal t ht) (heUnit t ht) (hoUnit t ht)
    energy_le := ?_ }⟩⟩
  · intro t ht
    exact (continuousAt_unitNormalize ue (continuousAt_neutralRepair .even K hK₂ u (htpos t ht))
      (hueNZ t ht)).continuousWithinAt
  · intro t ht
    exact (continuousAt_unitNormalize vo (continuousAt_neutralRepair .odd K hK₂ v (htpos t ht))
      (hvoNZ t ht)).continuousWithinAt
  · intro t ht
    change canonicalPoleEvenFunctional t K ((‖ue t‖ : ℂ)⁻¹ • ue t) = 0
    rw [map_smul]
    have hp := neutralRepair_pole .even (htpos t ht) K hK₂ u
    change canonicalPoleEvenFunctional t K (ue t) = 0 at hp
    rw [hp, smul_zero]
  · intro t ht
    change canonicalPoleOddFunctional t K ((‖vo t‖ : ℂ)⁻¹ • vo t) = 0
    rw [map_smul]
    have hp := neutralRepair_pole .odd (htpos t ht) K hK₂ v
    change canonicalPoleOddFunctional t K (vo t) = 0 at hp
    rw [hp, smul_zero]
  · intro t ht c d
    rw [fullCanonicalEnergy_parity_combination t K (e t) (o t) (heLegal t ht) (hoLegal t ht)]
    calc
      ‖c‖ ^ 2 * fullCanonicalEnergy t K (e t) + ‖d‖ ^ 2 * fullCanonicalEnergy t K (o t) ≤
          ‖c‖ ^ 2 * (-η) + ‖d‖ ^ 2 * (-η) :=
        add_le_add (mul_le_mul_of_nonneg_left (hGood t ht).1.le (sq_nonneg _))
          (mul_le_mul_of_nonneg_left (hGood t ht).2.le (sq_nonneg _))
      _ = -η * (‖c‖ ^ 2 + ‖d‖ ^ 2) := by ring

/-- R3-D03: one fixed finite cutoff and positive Rayleigh margin work on
each chosen closed interval; none is asserted uniform over the cofinal family. -/
theorem cofinally_uniform_neutral_interval_of_off_line_zero
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) (R : ℝ) :
    ∃ a b : ℝ, ∃ K : ℕ, ∃ η : ℝ, R < a ∧ 0 < a ∧ a < b ∧ 3 ≤ K ∧ 0 < η ∧
      Nonempty (UniformNeutralNegativeFrame a b K η) := by
  obtain ⟨L, hRL, hL, K, hK, hboth⟩ := cofinally_both_neutral_negative_of_off_line_zero ρ hoff R
  obtain ⟨a, b, η, hRa, ha, hab, hη, hframe⟩ :=
    exists_uniform_neutral_interval_of_both hL K hK hboth R hRL
  exact ⟨a, b, K, η, hRa, ha, hab, hK, hη, hframe⟩

end Zeta23.OPICARound3

#print axioms Zeta23.OPICARound3.cofinally_uniform_neutral_interval_of_off_line_zero
