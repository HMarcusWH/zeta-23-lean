import Zeta23.CCM.CanonicalPrimeFreeF04

noncomputable section

/-!
# F04 at every positive aperture

`CanonicalPrimeFreeF04` proves the three F04 fields on `0 < L < log 2`.  This
module adds the prime staircase.  Over any fixed range of `q`, the prime sum at
aperture `L` is a sum of terms switched on by the logarithmic indicator
`log q ≤ L`.  An entering term `(Λ(q)/√q) e_z(1 - log q/L)` has value `e_z(0) = 0`
and slope `e'_z(0) log q / L² = 0` at its seam `L = log q` (boundary-flat
vectors), and the entering term of the first channel has value and slope zero
because `e'_z(0) = e''_z(0) = 0`.  So every indicator term is differentiable at
its seam (`hasDerivAt_ite_le`, glued from the two one-sided derivatives), and
the three F04 fields hold at every `L > 0` and every `K`:

`productionContactF04DerivativeAuthority_of_pos`.

The identities are exact derivative-transport statements.  They carry no sign:
nothing here excludes a contact, proves an arithmetic inequality or bears on RH.
-/

namespace Zeta23.CCM

open MeasureTheory Set Filter Topology
open scoped Interval ArithmeticFunction ComplexConjugate

/-! ## Global F04: the prime staircase as logarithmic indicators -/

section GlobalF04

variable (K : ℕ)

/-- The prime staircase up to `e^L` as a sum over a fixed range with logarithmic
indicators. -/
theorem sum_Icc_floor_exp_eq_ite {L : ℝ} {N : ℕ} (hN : ⌊Real.exp L⌋₊ ≤ N) (F : ℕ → ℝ) :
    ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, F q =
      ∑ q ∈ Finset.Icc 2 N, if Real.log q ≤ L then F q else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext q
  simp only [Finset.mem_Icc, Finset.mem_filter]
  constructor
  · rintro ⟨h2, hq⟩
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    refine ⟨⟨h2, hq.trans hN⟩, (Real.log_le_iff_le_exp hqpos).mpr ?_⟩
    exact (Nat.le_floor_iff (Real.exp_pos L).le).mp hq
  · rintro ⟨⟨h2, -⟩, hlog⟩
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    exact ⟨h2, (Nat.le_floor_iff (Real.exp_pos L).le).mpr
      ((Real.log_le_iff_le_exp hqpos).mp hlog)⟩

theorem floor_exp_le_floor_exp {L L' : ℝ} (h : L ≤ L') :
    ⌊Real.exp L⌋₊ ≤ ⌊Real.exp L'⌋₊ :=
  Nat.floor_le_floor (Real.exp_le_exp.mpr h)

/-- **Seam gluing.**  A term switched on at `a` by a logarithmic indicator is
differentiable everywhere when it enters with zero value and zero slope. -/
theorem hasDerivAt_ite_le {ψ ψ' : ℝ → ℝ} {a L₀ : ℝ}
    (hψ : ∀ L, 0 < L → HasDerivAt ψ (ψ' L) L) (hL₀ : 0 < L₀)
    (h0 : ψ a = 0) (h1 : ψ' a = 0) :
    HasDerivAt (fun L => if a ≤ L then ψ L else 0) (if a ≤ L₀ then ψ' L₀ else 0) L₀ := by
  rcases lt_trichotomy L₀ a with h | h | h
  · rw [if_neg (not_le.mpr h)]
    refine (hasDerivAt_const L₀ (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with L hL
    rw [if_neg (not_le.mpr hL)]
  · subst a
    rw [if_pos le_rfl, h1]
    have hl : HasDerivWithinAt (fun L => if L₀ ≤ L then ψ L else 0) 0 (Iic L₀) L₀ := by
      refine (hasDerivWithinAt_const L₀ (Iic L₀) (0 : ℝ)).congr (fun y hy => ?_) ?_
      · by_cases hy' : L₀ ≤ y
        · have hyy : y = L₀ := le_antisymm hy hy'
          subst hyy
          simp [h0]
        · simp [hy']
      · simp [h0]
    have hr : HasDerivWithinAt (fun L => if L₀ ≤ L then ψ L else 0) 0 (Ici L₀) L₀ := by
      have h' := (hψ L₀ hL₀).hasDerivWithinAt (s := Ici L₀)
      rw [h1] at h'
      refine h'.congr (fun y hy => ?_) ?_
      · simp [show L₀ ≤ y from hy]
      · simp
    have hu := hl.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at hu
  · rw [if_pos h.le]
    refine (hψ L₀ hL₀).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds h] with L hL
    rw [if_pos hL.le]

theorem log_pos_of_two_le {q : ℕ} (hq : 2 ≤ q) : 0 < Real.log q :=
  Real.log_pos (by exact_mod_cast (by omega : 1 < q))

/-- The complete physical value in channel form (public copy of the real-channel
split). -/
theorem productionArithmeticRealValue_eq_channels_sum (L : ℝ) (f : ℝ → ℝ) :
    productionArithmeticRealValue L f =
      (∫ t in (0 : ℝ)..L, f t * completeSourcePoleWeight t) -
        (∫ t in (0 : ℝ)..L, f t * archDensity t) -
        ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, (Λ q / Real.sqrt q) * f (Real.log q) := by
  unfold productionArithmeticRealValue productionArithmeticComplexValue
    dictionaryCompletePhysicalRHS primeSourceWeight
  have hpole : Complex.re (∫ t in (0 : ℝ)..L, (f t : ℂ) * (completeSourcePoleWeight t : ℂ)) =
      ∫ t in (0 : ℝ)..L, f t * completeSourcePoleWeight t := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_re] using
      congrArg Complex.re (intervalIntegral.integral_ofReal
        (f := fun t : ℝ => f t * completeSourcePoleWeight t) (a := (0 : ℝ)) (b := L))
  have harch : Complex.re (∫ t in (0 : ℝ)..L, (f t : ℂ) * (archDensity t : ℂ)) =
      ∫ t in (0 : ℝ)..L, f t * archDensity t := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_re] using
      congrArg Complex.re (intervalIntegral.integral_ofReal
        (f := fun t : ℝ => f t * archDensity t) (a := (0 : ℝ)) (b := L))
  have hprime : Complex.re (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
      (((Λ q / Real.sqrt q : ℝ) : ℂ) * (f (Real.log q) : ℂ))) =
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, (Λ q / Real.sqrt q) * f (Real.log q) := by
    rw [← Complex.reCLM_apply, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  rw [Complex.sub_re, Complex.sub_re, hpole, harch, hprime]

/-- Regular channel form of the physical value of a test vanishing linearly at `0`,
for every `L > 0`. -/
theorem productionArithmeticRealValue_clamp_mul_id_sum {L : ℝ} (hL : 0 < L)
    {f : ℝ → ℝ} (h : ℝ → ℝ) (hfh : ∀ t, f t = t * h t) :
    productionArithmeticRealValue L (productionPhysicalClamp L f) =
      (∫ t in (0 : ℝ)..L, h t * poleScale t) -
        (∫ t in (0 : ℝ)..L, h t * regularizedArchScale t) -
        ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
          (Λ q / Real.sqrt q) * (Real.log q * h (Real.log q)) := by
  rw [productionArithmeticRealValue_congr_on_Icc hL (g := fun t => t * h t)
    (fun t ht => by rw [productionPhysicalClamp_eq ht, hfh]),
    productionArithmeticRealValue_eq_channels_sum]
  congr 2
  · exact intervalIntegral.integral_congr fun t _ => by unfold poleScale; ring
  · refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le hL.le] at ht
    rw [regularizedArchScale_eq_mul_archDensity ht.1.ne']
    ring

/-- Prime part of the first channel. -/
def primeFirstChannel (x : EuclideanSpace ℂ (Fin (2 * K + 1))) (L : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, (Λ q / Real.sqrt q) *
    (Real.log q * (sourceAtomRealEnergyDerivative K x (1 - Real.log q / L) * (1 / L ^ 2)))

/-- Prime part of the second channel. -/
def primeSecondChannel (x : EuclideanSpace ℂ (Fin (2 * K + 1))) (L : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, (Λ q / Real.sqrt q) *
    (Real.log q * (sourceAtomRealEnergySecondDerivative K x (1 - Real.log q / L) *
      (Real.log q / L ^ 4)))

/-- Prime part of the mixed channel. -/
def primeMixedChannel (x y : EuclideanSpace ℂ (Fin (2 * K + 1))) (L : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, (Λ q / Real.sqrt q) *
    (Real.log q * (Complex.re (sourceAtomPairingDerivative K x y (1 - Real.log q / L)) *
      (1 / L ^ 2)))

/-- Complete first channel. -/
def fullFirstChannel (x : EuclideanSpace ℂ (Fin (2 * K + 1))) (L : ℝ) : ℝ :=
  primeFreeFirstChannel K x L poleScale - primeFreeFirstChannel K x L regularizedArchScale -
    primeFirstChannel K x L

/-- The fixed even energy at every positive aperture, with the prime staircase as
logarithmic indicators over any range covering `⌊e^L⌋`. -/
theorem productionContactFixedEnergy_even_eq_ite {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ⌊Real.exp L⌋₊ ≤ N) (z : euclideanEvenBoundaryFlatSubspace K) :
    productionContactFixedEnergy .even L K z =
      (∫ t in (0 : ℝ)..L, sourceAtomRealEnergy K (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
          (1 - t / L) * completeSourcePoleWeight t) -
        ((∫ t in (0 : ℝ)..L, (sourceAtomRealEnergy K (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
            (1 - t / L) - sourceAtomRealEnergy K (z : EuclideanSpace ℂ (Fin (2 * K + 1))) 1 *
              Real.exp (-t / 2)) * archDensity t) +
          sourceAtomRealEnergy K (z : EuclideanSpace ℂ (Fin (2 * K + 1))) 1 * wCorrection L) -
        ∑ q ∈ Finset.Icc 2 N, if Real.log q ≤ L then (Λ q / Real.sqrt q) *
          sourceAtomRealEnergy K (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
            (1 - Real.log q / L) else 0 := by
  have h := parityCanonicalSourceEnergy_eq_matrixRealEnergy .even L K z
  unfold parityCanonicalSourceEnergy at h
  unfold productionContactFixedEnergy
  rw [h, matrixRealEnergy_canonical_eq_regularized K _ hL, sum_Icc_floor_exp_eq_ite hN]

/-- **First variation at every positive aperture.** -/
theorem productionContactFirstVariation_even_eq_full {L₀ : ℝ} (hL₀ : 0 < L₀)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    productionContactFirstVariation .even L₀ K z =
      fullFirstChannel K z L₀ := by
  set x : EuclideanSpace ℂ (Fin (2 * K + 1)) := (z : EuclideanSpace ℂ (Fin (2 * K + 1))) with hx
  have h0 := sourceAtomRealEnergyDerivative_zero_of_boundaryFlat K x
    (evenBoundaryFlatRawCoefficients_boundaryFlat K z)
  set N := ⌊Real.exp (L₀ + 1)⌋₊
  have hP := hasDerivAt_poleChannel K x hL₀
  have hG := hasDerivAt_archChannel K x hL₀
  have hw := (hasDerivAt_wCorrection hL₀).const_mul (sourceAtomRealEnergy K x 1)
  have hS : HasDerivAt (fun L => ∑ q ∈ Finset.Icc 2 N, if Real.log q ≤ L then
      (Λ q / Real.sqrt q) * sourceAtomRealEnergy K x (1 - Real.log q / L) else 0)
      (∑ q ∈ Finset.Icc 2 N, if Real.log q ≤ L₀ then (Λ q / Real.sqrt q) *
        (sourceAtomRealEnergyDerivative K x (1 - Real.log q / L₀) * (Real.log q / L₀ ^ 2))
        else 0) L₀ := by
    refine HasDerivAt.fun_sum fun q hq => ?_
    have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
    have ha := log_pos_of_two_le hq2
    refine hasDerivAt_ite_le (ψ := fun L => (Λ q / Real.sqrt q) *
        sourceAtomRealEnergy K x (1 - Real.log q / L))
      (ψ' := fun L => (Λ q / Real.sqrt q) *
        (sourceAtomRealEnergyDerivative K x (1 - Real.log q / L) * (Real.log q / L ^ 2)))
      (fun L hL => ((hasDerivAt_sourceAtomRealEnergy_transport K x _).comp L
        (hasDerivAt_one_sub_div_param (Real.log q) hL.ne')).const_mul _) hL₀ ?_ ?_
    · simp [div_self ha.ne', sourceAtomRealEnergy_zero]
    · simp [div_self ha.ne', h0]
  have hE := (hP.sub (hG.add hw)).sub hS
  have hE' := hE.congr_of_eventuallyEq
    (f₁ := fun s => productionContactFixedEnergy .even s K z) (by
      filter_upwards [Ioo_mem_nhds hL₀ (by linarith : L₀ < L₀ + 1)] with s hs
      exact productionContactFixedEnergy_even_eq_ite K hs.1
        (floor_exp_le_floor_exp hs.2.le) z)
  unfold productionContactFirstVariation
  rw [hE'.deriv, ← sum_Icc_floor_exp_eq_ite (floor_exp_le_floor_exp (by linarith : L₀ ≤ L₀ + 1))]
  unfold fullFirstChannel primeFreeFirstChannel primeFirstChannel poleScale
  have harch : (∫ t in (0 : ℝ)..L₀, sourceAtomRealEnergyDerivative K x (1 - t / L₀) *
      (t / L₀ ^ 2) * archDensity t) =
      ∫ t in (0 : ℝ)..L₀, sourceAtomRealEnergyDerivative K x (1 - t / L₀) * (1 / L₀ ^ 2) *
        regularizedArchScale t := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le hL₀.le] at ht
    rw [regularizedArchScale_eq_mul_archDensity ht.1.ne']
    ring
  have hpole : (∫ t in (0 : ℝ)..L₀, sourceAtomRealEnergyDerivative K x (1 - t / L₀) *
      (t / L₀ ^ 2) * completeSourcePoleWeight t) =
      ∫ t in (0 : ℝ)..L₀, sourceAtomRealEnergyDerivative K x (1 - t / L₀) * (1 / L₀ ^ 2) *
        (t * completeSourcePoleWeight t) :=
    intervalIntegral.integral_congr fun t _ => by ring
  have hprime : (∑ q ∈ Finset.Icc 2 ⌊Real.exp L₀⌋₊, (Λ q / Real.sqrt q) *
      (sourceAtomRealEnergyDerivative K x (1 - Real.log q / L₀) * (Real.log q / L₀ ^ 2))) =
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L₀⌋₊, (Λ q / Real.sqrt q) * (Real.log q *
        (sourceAtomRealEnergyDerivative K x (1 - Real.log q / L₀) * (1 / L₀ ^ 2))) :=
    Finset.sum_congr rfl fun q _ => by ring
  rw [← harch, ← hpole, ← hprime]
  ring

theorem productionFirstDerivativePhysicalValue_eq_full {L : ℝ} (hL : 0 < L)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    productionArithmeticRealValue L (productionFirstDerivativePhysicalTest L K z) =
      fullFirstChannel K z L := by
  unfold productionFirstDerivativePhysicalTest
  rw [productionArithmeticRealValue_clamp_mul_id_sum hL
    (fun t => sourceAtomRealEnergyDerivative K (z : EuclideanSpace ℂ (Fin (2 * K + 1)))
      (1 - t / L) * (1 / L ^ 2))
    (fun t => by unfold productionFirstDerivativePhysicalRaw; ring)]
  rfl

theorem productionSecondDerivativePhysicalValue_eq_full {L : ℝ} (hL : 0 < L)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    productionArithmeticRealValue L (productionSecondDerivativePhysicalTest L K z) =
      primeFreeSecondChannel K z L poleScale -
        primeFreeSecondChannel K z L regularizedArchScale - primeSecondChannel K z L := by
  unfold productionSecondDerivativePhysicalTest
  rw [productionArithmeticRealValue_clamp_mul_id_sum hL
    (fun t => sourceAtomRealEnergySecondDerivative K
      (z : EuclideanSpace ℂ (Fin (2 * K + 1))) (1 - t / L) * (t / L ^ 4))
    (fun t => by unfold productionSecondDerivativePhysicalRaw; ring)]
  rfl

theorem productionMixedDerivativePhysicalValue_eq_full {L : ℝ} (hL : 0 < L)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    productionArithmeticRealValue L (productionMixedDerivativePhysicalTest L K z w) =
      primeFreeMixedChannel K z w L poleScale -
        primeFreeMixedChannel K z w L regularizedArchScale - primeMixedChannel K z w L := by
  unfold productionMixedDerivativePhysicalTest
  rw [productionArithmeticRealValue_clamp_mul_id_sum hL
    (fun t => Complex.re (sourceAtomPairingDerivative K
      (z : EuclideanSpace ℂ (Fin (2 * K + 1))) (w : EuclideanSpace ℂ (Fin (2 * K + 1)))
        (1 - t / L)) * (1 / L ^ 2))
    (fun t => by unfold productionMixedDerivativePhysicalRaw; ring)]
  rfl

/-- **Second-order seam gluing.**  The prime part of the first channel is
differentiable at every positive aperture; entering atoms have zero value and
slope because `e'(0) = e''(0) = 0`. -/
theorem hasDerivAt_primeFirstChannel (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    {L₀ : ℝ} (hL₀ : 0 < L₀) (h0 : sourceAtomRealEnergyDerivative K x 0 = 0) :
    HasDerivAt (fun L => primeFirstChannel K x L)
      (primeSecondChannel K x L₀ - 2 / L₀ * primeFirstChannel K x L₀) L₀ := by
  set N := ⌊Real.exp (L₀ + 1)⌋₊
  have hS : HasDerivAt (fun L => ∑ q ∈ Finset.Icc 2 N, if Real.log q ≤ L then
      (Λ q / Real.sqrt q) * (Real.log q *
        (sourceAtomRealEnergyDerivative K x (1 - Real.log q / L) * (1 / L ^ 2))) else 0)
      (∑ q ∈ Finset.Icc 2 N, if Real.log q ≤ L₀ then (Λ q / Real.sqrt q) * (Real.log q *
        (sourceAtomRealEnergySecondDerivative K x (1 - Real.log q / L₀) *
            (Real.log q / L₀ ^ 2) * (1 / L₀ ^ 2) +
          sourceAtomRealEnergyDerivative K x (1 - Real.log q / L₀) * (-2 / L₀ ^ 3)))
        else 0) L₀ := by
    refine HasDerivAt.fun_sum fun q hq => ?_
    have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
    have ha := log_pos_of_two_le hq2
    refine hasDerivAt_ite_le (ψ := fun L => (Λ q / Real.sqrt q) * (Real.log q *
        (sourceAtomRealEnergyDerivative K x (1 - Real.log q / L) * (1 / L ^ 2))))
      (ψ' := fun L => (Λ q / Real.sqrt q) * (Real.log q *
        (sourceAtomRealEnergySecondDerivative K x (1 - Real.log q / L) *
            (Real.log q / L ^ 2) * (1 / L ^ 2) +
          sourceAtomRealEnergyDerivative K x (1 - Real.log q / L) * (-2 / L ^ 3))))
      (fun L hL => ((((hasDerivAt_sourceAtomRealEnergyDerivative_transport K x _).comp L
        (hasDerivAt_one_sub_div_param (Real.log q) hL.ne')).mul
          (hasDerivAt_inv_sq hL.ne')).const_mul _).const_mul _) hL₀ ?_ ?_
    · simp [div_self ha.ne', h0]
    · simp [div_self ha.ne', h0, sourceAtomRealEnergySecondDerivative_zero]
  have hS' := hS.congr_of_eventuallyEq (f₁ := fun L => primeFirstChannel K x L) (by
    filter_upwards [Ioo_mem_nhds hL₀ (by linarith : L₀ < L₀ + 1)] with s hs
    exact sum_Icc_floor_exp_eq_ite (floor_exp_le_floor_exp hs.2.le) _)
  refine hS'.congr_deriv ?_
  rw [← sum_Icc_floor_exp_eq_ite (floor_exp_le_floor_exp (by linarith : L₀ ≤ L₀ + 1))]
  unfold primeSecondChannel primeFirstChannel
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  field_simp
  ring

/-- **M65 extended: F04 derivative authority at every positive aperture.**  The
three F04 fields hold for the actual canonical even compressed family at every
`L > 0` and every `K`, across all prime seams. -/
theorem productionContactF04DerivativeAuthority_of_pos {L : ℝ} (hL : 0 < L) :
    ProductionContactF04DerivativeAuthority L K where
  first z := by
    rw [productionContactFirstVariation_even_eq_full K hL,
      productionFirstDerivativePhysicalValue_eq_full K hL]
  fixedSecondEuler z := by
    have h0 := sourceAtomRealEnergyDerivative_zero_of_boundaryFlat K
      (z : EuclideanSpace ℂ (Fin (2 * K + 1))) (evenBoundaryFlatRawCoefficients_boundaryFlat K z)
    have hd : HasDerivAt (fun s => fullFirstChannel K z s) _ L :=
      ((hasDerivAt_primeFreeFirstChannel K _ continuous_poleScale hL h0).sub
        (hasDerivAt_primeFreeFirstChannel K _ continuous_regularizedArchScale hL h0)).sub
        (hasDerivAt_primeFirstChannel K _ hL h0)
    have hev : (fun s => productionContactFirstVariation .even s K z) =ᶠ[𝓝 L]
        fun s => fullFirstChannel K z s := by
      filter_upwards [Ioi_mem_nhds hL] with s hs
      exact productionContactFirstVariation_even_eq_full K hs z
    unfold productionContactFixedSecondVariation
    rw [hev.deriv_eq, hd.deriv, productionContactFirstVariation_even_eq_full K hL,
      productionSecondDerivativePhysicalValue_eq_full K hL]
    unfold fullFirstChannel
    ring
  mixed z w := by
    rw [re_inner_canonicalEvenApertureFirst_polarization K hL,
      productionContactFirstVariation_even_eq_full K hL,
      productionContactFirstVariation_even_eq_full K hL,
      productionMixedDerivativePhysicalValue_eq_full K hL,
      primeFreeMixedChannel_polarization K _ _ continuous_poleScale,
      primeFreeMixedChannel_polarization K _ _ continuous_regularizedArchScale]
    have hp : primeMixedChannel K z w L =
        (primeFirstChannel K ((z : EuclideanSpace ℂ (Fin (2 * K + 1))) + w) L -
          primeFirstChannel K ((z : EuclideanSpace ℂ (Fin (2 * K + 1))) - w) L) / 4 := by
      unfold primeMixedChannel primeFirstChannel
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [sourceAtomPairingDerivative_re_polarization]
      ring
    rw [hp]
    unfold fullFirstChannel
    simp only [Submodule.coe_add, Submodule.coe_sub]
    ring

end GlobalF04

/-- Global form of the Euler-corrected saturation identity. -/
theorem canonicalSecondPairing_euler_eq_productionSaturationGap_of_pos
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    productionContactSaturationGap L K z w =
      canonicalContactSecondPairing L K z w +
        2 * productionContactFirstVariation .even L K z / L :=
  canonicalSecondPairing_euler_eq_productionSaturationGap hL K hK z w
    (productionContactF04DerivativeAuthority_of_pos K hL)

end Zeta23.CCM

#print axioms Zeta23.CCM.sum_Icc_floor_exp_eq_ite
#print axioms Zeta23.CCM.hasDerivAt_ite_le
#print axioms Zeta23.CCM.productionArithmeticRealValue_eq_channels_sum
#print axioms Zeta23.CCM.productionArithmeticRealValue_clamp_mul_id_sum
#print axioms Zeta23.CCM.productionContactFirstVariation_even_eq_full
#print axioms Zeta23.CCM.hasDerivAt_primeFirstChannel
#print axioms Zeta23.CCM.productionContactF04DerivativeAuthority_of_pos
#print axioms Zeta23.CCM.canonicalSecondPairing_euler_eq_productionSaturationGap_of_pos
