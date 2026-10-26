import Zeta23.OPICARound2.CausalProbe
import Zeta23.OPICAFollowup.ConfluentProfiles
import Zeta23.ExceptionalZero.NativeActualKernelZeroJets
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Fin.Rev
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!+# Literal Laplace-jet dual witnesses

The witnesses are the already constructed causal L2 exponential polynomials.
Ordinary jet factorials and the complex inner-product orientation are retained.
-/

noncomputable section

open Set MeasureTheory Matrix
open scoped Topology ENNReal BigOperators ComplexConjugate ComplexOrder

namespace Zeta23.OPICARound2

abbrev LaplaceJetIndex {r : ℕ} (m : Fin r → ℕ) := (i : Fin r) × Fin (m i)

def laplaceJetWitness {r : ℕ} (nodes : Fin r → ℂ) (hpos : ∀ i, 0 < (nodes i).re)
    (m : Fin r → ℕ) (p : LaplaceJetIndex m) : CausalProbeL2 :=
  CCM.nativeCausalExponentialWitness (nodes p.1) (hpos p.1) p.2.val

def laplaceJetGram {r : ℕ} (nodes : Fin r → ℂ) (hpos : ∀ i, 0 < (nodes i).re)
    (m : Fin r → ℕ) : Matrix (LaplaceJetIndex m) (LaplaceJetIndex m) ℂ :=
  Matrix.gram ℂ (laplaceJetWitness nodes hpos m)

theorem nativeExponential_zero_laplace (a : ℂ) (ha : 0 < a.re)
    (z : ℂ) (hz : 0 < z.re) :
    CCM.nativeCausalLaplaceMoment z 0
      (CCM.nativeCausalExponentialWitness a ha 0 : ProbeL2) = (z + conj a)⁻¹ := by
  have hsum : 0 < (z + conj a).re := by simpa only [Complex.add_re, Complex.conj_re] using add_pos hz ha
  rw [CCM.nativeCausalLaplaceMoment]
  calc
    _ = ∫ t : ℝ, (Ici (0 : ℝ)).indicator
        (fun t : ℝ => Complex.exp (-(z + conj a) * (t : ℂ))) t := by
      apply integral_congr_ae
      filter_upwards [CCM.nativeCausalExponentialPolynomialL2_coeFn a ha 0] with t ht
      change (t : ℂ) ^ 0 * Complex.exp (-z * (t : ℂ)) *
        CCM.nativeCausalExponentialPolynomialL2 a ha 0 t = _
      rw [ht]
      by_cases ht0 : 0 ≤ t
      · have hi : (Ici (0 : ℝ)).indicator
            (fun t : ℝ => Complex.exp (-(z + conj a) * (t : ℂ))) t =
            Complex.exp (-(z + conj a) * (t : ℂ)) :=
          Set.indicator_of_mem (show t ∈ Ici (0 : ℝ) from ht0) _
        rw [hi, CCM.nativeCausalExponentialPolynomial_of_nonneg _ _ ht0,
          CCM.nativeExponentialPolynomialProfile, pow_zero, one_mul, one_mul, ← Complex.exp_add]
        congr 1
        ring
      · have hi : (Ici (0 : ℝ)).indicator
            (fun t : ℝ => Complex.exp (-(z + conj a) * (t : ℂ))) t = 0 :=
          Set.indicator_of_notMem (show t ∉ Ici (0 : ℝ) from ht0) _
        rw [hi, CCM.nativeCausalExponentialPolynomial_zero_of_neg _ _ (lt_of_not_ge ht0), mul_zero]
    _ = ∫ t in Ioi (0 : ℝ), Complex.exp (-(z + conj a) * (t : ℂ)) := by
      rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
    _ = _ := by
      rw [integral_exp_mul_complex_Ioi (by simp only [Complex.neg_re]; linarith)]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq, one_div]

theorem nativeExponential_zero_moment (a : ℂ) (ha : 0 < a.re)
    (z : ℂ) (hz : 0 < z.re) (k : ℕ) :
    CCM.nativeCausalLaplaceMoment z k
      (CCM.nativeCausalExponentialWitness a ha 0 : ProbeL2) =
        (k.factorial : ℂ) / (z + conj a) ^ (k + 1) := by
  have he : (fun w : ℂ => CCM.nativeCausalLaplaceMoment w 0
      (CCM.nativeCausalExponentialWitness a ha 0 : ProbeL2)) =ᶠ[𝓝 z]
      fun w => (w + conj a)⁻¹ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
    exact nativeExponential_zero_laplace a ha w hw
  have hd := he.iteratedDeriv_eq k
  rw [CCM.nativeCausalLaplaceMoment_iteratedDeriv z hz k] at hd
  have hright : iteratedDeriv k (fun w : ℂ => (w + conj a)⁻¹) z =
      (-1 : ℂ) ^ k * (k.factorial : ℂ) / (z + conj a) ^ (k + 1) := by
    rw [iteratedDeriv_eq_iterate]
    have h := congrFun (iter_deriv_inv_linear k (1 : ℂ) (conj a)) z
    simp only [one_mul, one_pow, mul_one] at h
    rw [h]
    have hk : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) := by omega
    rw [hk, _root_.zpow_neg, zpow_natCast, div_eq_mul_inv]
  rw [hright] at hd
  apply mul_left_cancel₀ (pow_ne_zero k (by norm_num : (-1 : ℂ) ≠ 0))
  calc
    _ = (-1 : ℂ) ^ k * (k.factorial : ℂ) / (z + conj a) ^ (k + 1) := hd
    _ = _ := by ring

theorem nativeExponential_moment_shift (a : ℂ) (ha : 0 < a.re)
    (z : ℂ) (k l : ℕ) :
    CCM.nativeCausalLaplaceMoment z k
      (CCM.nativeCausalExponentialWitness a ha l : ProbeL2) =
    CCM.nativeCausalLaplaceMoment z (k + l)
      (CCM.nativeCausalExponentialWitness a ha 0 : ProbeL2) := by
  rw [CCM.nativeCausalLaplaceMoment, CCM.nativeCausalLaplaceMoment]
  apply integral_congr_ae
  filter_upwards [CCM.nativeCausalExponentialPolynomialL2_coeFn a ha l,
    CCM.nativeCausalExponentialPolynomialL2_coeFn a ha 0] with t hl h0
  change (t : ℂ) ^ k * Complex.exp (-z * (t : ℂ)) *
      CCM.nativeCausalExponentialPolynomialL2 a ha l t =
    (t : ℂ) ^ (k + l) * Complex.exp (-z * (t : ℂ)) *
      CCM.nativeCausalExponentialPolynomialL2 a ha 0 t
  rw [hl, h0]
  by_cases ht : 0 ≤ t
  · rw [CCM.nativeCausalExponentialPolynomial_of_nonneg _ _ ht,
      CCM.nativeCausalExponentialPolynomial_of_nonneg _ _ ht,
      CCM.nativeExponentialPolynomialProfile, CCM.nativeExponentialPolynomialProfile,
      pow_zero, one_mul, pow_add]
    ring
  · rw [CCM.nativeCausalExponentialPolynomial_zero_of_neg _ _ (lt_of_not_ge ht),
      CCM.nativeCausalExponentialPolynomial_zero_of_neg _ _ (lt_of_not_ge ht), mul_zero, mul_zero]

theorem laplaceJetGram_entry {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) (p q : LaplaceJetIndex m) :
    laplaceJetGram nodes hpos m p q =
      ((p.2.val + q.2.val).factorial : ℂ) /
        (nodes p.1 + conj (nodes q.1)) ^ (p.2.val + q.2.val + 1) := by
  rw [laplaceJetGram, Matrix.gram_apply]
  change inner ℂ (CCM.nativeCausalExponentialWitness (nodes p.1) (hpos p.1) p.2.val)
    (CCM.nativeCausalExponentialWitness (nodes q.1) (hpos q.1) q.2.val) = _
  rw [CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment,
    nativeExponential_moment_shift, nativeExponential_zero_moment _ _ _ (hpos p.1)]

theorem laplaceJetGram_posSemidef {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) :
    (laplaceJetGram nodes hpos m).PosSemidef :=
  Matrix.posSemidef_gram ℂ (laplaceJetWitness nodes hpos m)

theorem laplaceJetGram_not_posDef_of_repeated_nodes {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) {i j : Fin r}
    (hij : i ≠ j) (hnode : nodes i = nodes j) (hi : 0 < m i) (hj : 0 < m j) :
    ¬(laplaceJetGram nodes hpos m).PosDef := by
  intro hpd
  have hli := Matrix.linearIndependent_of_posDef_gram hpd
  let p : LaplaceJetIndex m := ⟨i, ⟨0, hi⟩⟩
  let q : LaplaceJetIndex m := ⟨j, ⟨0, hj⟩⟩
  have he : laplaceJetWitness nodes hpos m p = laplaceJetWitness nodes hpos m q := by
    simp only [laplaceJetWitness, p, q, hnode]
  have hpq : p = q := hli.injective he
  exact hij (congrArg Sigma.fst hpq)

theorem laplaceJetGram_det_zero_of_repeated_nodes {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) {i j : Fin r}
    (hij : i ≠ j) (hnode : nodes i = nodes j) (hi : 0 < m i) (hj : 0 < m j) :
    (laplaceJetGram nodes hpos m).det = 0 := by
  by_contra hdet
  exact laplaceJetGram_not_posDef_of_repeated_nodes nodes hpos m hij hnode hi hj
    ((laplaceJetGram_posSemidef nodes hpos m).posDef_iff_det_ne_zero.mpr hdet)

open Polynomial

open OPICAFollowup.OPICAConfluentAudit OPICAFollowup.OPICAGroupedConfluent

def dualNormalizedHermite {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ) :
    Matrix (Fin (∑ i, m i)) (Fin (∑ i, m i)) ℂ :=
  functionalMatrix
    (fun j => hasseFunctional (groupedNode nodes m j)
      (repeatedJetOrder (groupedNode nodes m) j))
    (fun i => X ^ (i : ℕ))

theorem dualNormalizedHermite_det {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ) :
    (dualNormalizedHermite nodes m).det =
      ∏ j, ∏ i ∈ Finset.Iio j, (nodes j - nodes i) ^ (m i * m j) := by
  rw [dualNormalizedHermite, normalizedHermite_determinant,
    grouped_gap_product nodes hnodes m]

theorem dualNormalizedHermite_entry {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ)
    (n : Fin (∑ i, m i)) (p : LaplaceJetIndex m) :
    dualNormalizedHermite nodes m n (groupEquiv m p) =
      hasseFunctional (nodes p.1) p.2.val (X ^ (n : ℕ)) := by
  change hasseFunctional (groupedNode nodes m (groupIndex m p))
    (repeatedJetOrder (groupedNode nodes m) (groupIndex m p)) (X ^ (n : ℕ)) = _
  rw [groupedNode_at, grouped_repeatedJetOrder nodes hnodes m]

def dualPolePolynomial {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ)
    (p : LaplaceJetIndex m) : ℂ[X] :=
  (∏ j ∈ Finset.univ.erase p.1, (X - C (nodes j)) ^ m j) *
    (X - C (nodes p.1)) ^ (m p.1 - p.2.val - 1)

def dualCommonDenominator {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ) : ℂ[X] :=
  ∏ j : Fin r, (X - C (nodes j)) ^ m j

theorem dualPolePolynomial_monic {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ)
    (p : LaplaceJetIndex m) : (dualPolePolynomial nodes m p).Monic := by
  apply Polynomial.Monic.mul
  · apply Polynomial.monic_prod_of_monic
    intro j _
    exact (Polynomial.monic_X_sub_C _).pow _
  · exact (Polynomial.monic_X_sub_C _).pow _

theorem dualPolePolynomial_clear_denominator {r : ℕ} (nodes : Fin r → ℂ)
    (m : Fin r → ℕ) (p : LaplaceJetIndex m) :
    dualPolePolynomial nodes m p * (X - C (nodes p.1)) ^ (p.2.val + 1) =
      dualCommonDenominator nodes m := by
  have hexp : m p.1 - p.2.val - 1 + (p.2.val + 1) = m p.1 := by omega
  rw [dualPolePolynomial, mul_assoc, ← pow_add, hexp, dualCommonDenominator]
  exact Finset.prod_erase_mul _ _ (Finset.mem_univ p.1)

def dualHermiteEvaluation {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ)
    (polys : Fin (∑ i, m i) → ℂ[X]) : Matrix (Fin (∑ i, m i)) (Fin (∑ i, m i)) ℂ :=
  functionalMatrix
    (fun j => hasseFunctional (groupedNode nodes m j)
      (repeatedJetOrder (groupedNode nodes m) j)) polys

def dualCoefficientMatrix {r : ℕ} (m : Fin r → ℕ)
    (polys : Fin (∑ i, m i) → ℂ[X]) : Matrix (Fin (∑ i, m i)) (Fin (∑ i, m i)) ℂ :=
  Matrix.of (fun i j => (polys j).coeff i)

theorem dualHermiteEvaluation_det {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ)
    (polys : Fin (∑ i, m i) → ℂ[X]) (hdeg : ∀ i, (polys i).natDegree < ∑ i, m i) :
    (dualHermiteEvaluation nodes m polys).det =
      (dualCoefficientMatrix m polys).det *
        (∏ j, ∏ i ∈ Finset.Iio j, (nodes j - nodes i) ^ (m i * m j)) := by
  rw [dualHermiteEvaluation, functionalMatrix_eq_coeff_mul _ polys hdeg,
    Matrix.det_mul, Matrix.det_transpose]
  change (dualCoefficientMatrix m polys).det * (dualNormalizedHermite nodes m).det = _
  rw [dualNormalizedHermite_det nodes hnodes m]


theorem dualCommonDenominator_monic {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ) :
    (dualCommonDenominator nodes m).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro j _
  exact (Polynomial.monic_X_sub_C _).pow _

theorem dualCommonDenominator_natDegree {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ) :
    (dualCommonDenominator nodes m).natDegree = ∑ i, m i := by
  rw [dualCommonDenominator, Polynomial.natDegree_prod_of_monic]
  · apply Finset.sum_congr rfl
    intro j _
    rw [(Polynomial.monic_X_sub_C _).natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  · intro j _
    exact (Polynomial.monic_X_sub_C (nodes j)).pow (m j)

theorem dualPolePolynomial_natDegree_lt {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ)
    (p : LaplaceJetIndex m) : (dualPolePolynomial nodes m p).natDegree < ∑ i, m i := by
  have h := Polynomial.natDegree_mul (dualPolePolynomial_monic nodes m p).ne_zero
    ((Polynomial.monic_X_sub_C (nodes p.1)).pow (p.2.val + 1)).ne_zero
  rw [dualPolePolynomial_clear_denominator, dualCommonDenominator_natDegree,
    (Polynomial.monic_X_sub_C _).natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at h
  omega

theorem dualTaylor_linear (a : ℂ) : Polynomial.taylor a (X - C a) = X := by
  rw [Polynomial.taylor_apply, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
  ring

theorem dualHasse_zero_of_power_dvd (p : ℂ[X]) (a : ℂ) (n k : ℕ)
    (hdiv : (X - C a) ^ n ∣ p) (hk : k < n) : hasseFunctional a k p = 0 := by
  rw [hasseFunctional_eq_taylor_coeff]
  apply (Polynomial.X_pow_dvd_iff.mp ?_) k hk
  rcases hdiv with ⟨q, hq⟩
  refine ⟨Polynomial.taylor a q, ?_⟩
  rw [hq, Polynomial.taylor_mul, Polynomial.taylor_pow, dualTaylor_linear]

theorem dualPolePolynomial_cross_hasse_zero {r : ℕ} (nodes : Fin r → ℂ)
    (m : Fin r → ℕ) (p : LaplaceJetIndex m) {i : Fin r} (hne : i ≠ p.1)
    (k : ℕ) (hk : k < m i) : hasseFunctional (nodes i) k (dualPolePolynomial nodes m p) = 0 := by
  apply dualHasse_zero_of_power_dvd _ _ (m i) k ?_ hk
  have hi : i ∈ Finset.univ.erase p.1 := by simp [hne]
  have hd : (X - C (nodes i)) ^ m i ∣
      ∏ j ∈ Finset.univ.erase p.1, (X - C (nodes j)) ^ m j :=
    Finset.dvd_prod_of_mem _ hi
  exact dvd_mul_of_dvd_left hd _

theorem dualPolePolynomial_own_hasse_zero {r : ℕ} (nodes : Fin r → ℂ)
    (m : Fin r → ℕ) (p : LaplaceJetIndex m) (k : ℕ)
    (hk : k < m p.1 - p.2.val - 1) :
    hasseFunctional (nodes p.1) k (dualPolePolynomial nodes m p) = 0 := by
  apply dualHasse_zero_of_power_dvd _ _ _ k ?_ hk
  exact dvd_mul_left _ _

theorem dualPolePolynomial_own_leading {r : ℕ} (nodes : Fin r → ℂ)
    (m : Fin r → ℕ) (p : LaplaceJetIndex m) :
    hasseFunctional (nodes p.1) (m p.1 - p.2.val - 1) (dualPolePolynomial nodes m p) =
      ∏ j ∈ Finset.univ.erase p.1, (nodes p.1 - nodes j) ^ m j := by
  rw [hasseFunctional_eq_taylor_coeff, dualPolePolynomial, Polynomial.taylor_mul,
    Polynomial.taylor_pow, dualTaylor_linear, mul_comm]
  rw [Polynomial.coeff_X_pow_mul']
  simp only [le_refl, ↓reduceIte, Nat.sub_self]
  rw [Polynomial.taylor_coeff_zero]
  simp only [Polynomial.eval_prod, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]


def dualPoleFamily {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ)
    (n : Fin (∑ i, m i)) : ℂ[X] := dualPolePolynomial nodes m ((groupEquiv m).symm n)

def dualBlockReverse {r : ℕ} (m : Fin r → ℕ) : Equiv.Perm (Fin (∑ i, m i)) :=
  (groupEquiv m).symm.trans ((Equiv.sigmaCongrRight
    (fun i : Fin r => (Fin.revPerm : Equiv.Perm (Fin (m i))))).trans (groupEquiv m))

theorem dualBlockReverse_apply {r : ℕ} (m : Fin r → ℕ) (p : LaplaceJetIndex m) :
    dualBlockReverse m (groupEquiv m p) = groupEquiv m ⟨p.1, p.2.rev⟩ := by
  simp [dualBlockReverse]

def dualPoleReversedEvaluation {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ) :
    Matrix (Fin (∑ i, m i)) (Fin (∑ i, m i)) ℂ :=
  (dualHermiteEvaluation nodes m (dualPoleFamily nodes m)).submatrix (dualBlockReverse m) id

def dualPoleGap {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ) (i : Fin r) : ℂ :=
  ∏ j ∈ Finset.univ.erase i, (nodes i - nodes j) ^ m j

theorem dualPoleReversedEvaluation_entry {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ) (p q : LaplaceJetIndex m) :
    dualPoleReversedEvaluation nodes m (groupEquiv m p) (groupEquiv m q) =
      hasseFunctional (nodes q.1) q.2.val (dualPolePolynomial nodes m ⟨p.1, p.2.rev⟩) := by
  change dualHermiteEvaluation nodes m (dualPoleFamily nodes m)
    (dualBlockReverse m (groupEquiv m p)) (groupEquiv m q) = _
  rw [dualBlockReverse_apply]
  change hasseFunctional (groupedNode nodes m (groupIndex m q))
    (repeatedJetOrder (groupedNode nodes m) (groupIndex m q))
    (dualPolePolynomial nodes m ((groupEquiv m).symm (groupEquiv m ⟨p.1, p.2.rev⟩))) = _
  rw [groupedNode_at, grouped_repeatedJetOrder nodes hnodes m, Equiv.symm_apply_apply]

theorem dualPoleReversedEvaluation_upper {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ) :
    (dualPoleReversedEvaluation nodes m).IsUpperTriangular := by
  intro n j hjn
  rcases (groupEquiv m).surjective n with ⟨p, rfl⟩
  rcases (groupEquiv m).surjective j with ⟨q, rfl⟩
  rw [dualPoleReversedEvaluation_entry nodes hnodes m]
  by_cases he : q.1 = p.1
  · rw [show nodes q.1 = nodes p.1 from congrArg nodes he]
    apply dualPolePolynomial_own_hasse_zero nodes m ⟨p.1, p.2.rev⟩ q.2.val
    have hb : blockStart m q.1 = blockStart m p.1 := congrArg (blockStart m) he
    change blockStart m q.1 + q.2.val < blockStart m p.1 + p.2.val at hjn
    dsimp only [Sigma.fst, Sigma.snd]
    rw [Fin.val_rev]
    omega
  · exact dualPolePolynomial_cross_hasse_zero nodes m ⟨p.1, p.2.rev⟩ he q.2.val q.2.isLt

theorem dualPoleReversedEvaluation_diagonal {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ) (p : LaplaceJetIndex m) :
    dualPoleReversedEvaluation nodes m (groupEquiv m p) (groupEquiv m p) =
      dualPoleGap nodes m p.1 := by
  rw [dualPoleReversedEvaluation_entry nodes hnodes m]
  have he : p.2.val = m p.1 - p.2.rev.val - 1 := by rw [Fin.val_rev]; omega
  rw [he]
  exact dualPolePolynomial_own_leading nodes m ⟨p.1, p.2.rev⟩

theorem dualPoleReversedEvaluation_det {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ) :
    (dualPoleReversedEvaluation nodes m).det = ∏ i : Fin r, dualPoleGap nodes m i ^ m i := by
  rw [Matrix.det_of_isUpperTriangular (dualPoleReversedEvaluation_upper nodes hnodes m)]
  calc
    _ = ∏ p : LaplaceJetIndex m, dualPoleGap nodes m p.1 := by
      rw [← (groupEquiv m).prod_comp]
      apply Finset.prod_congr rfl
      intro p _
      exact dualPoleReversedEvaluation_diagonal nodes hnodes m p
    _ = _ := by rw [Fintype.prod_sigma]; simp only [Fin.prod_const]

theorem dual_norm_det_permute {n : Type*} [Fintype n] [DecidableEq n]
    (σ : Equiv.Perm n) (A : Matrix n n ℂ) :
    ‖(A.submatrix σ id).det‖ = ‖A.det‖ := by
  rw [Matrix.det_permute, norm_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem dualPoleGap_ne_zero {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ) (i : Fin r) :
    dualPoleGap nodes m i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.2
  intro j hj
  apply pow_ne_zero
  apply sub_ne_zero.2
  intro h
  exact (Finset.mem_erase.mp hj).1 (hnodes h).symm

theorem dualPoleReversedEvaluation_det_ne_zero {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ) :
    (dualPoleReversedEvaluation nodes m).det ≠ 0 := by
  rw [dualPoleReversedEvaluation_det nodes hnodes m]
  apply Finset.prod_ne_zero_iff.2
  intro i _
  exact pow_ne_zero _ (dualPoleGap_ne_zero nodes hnodes m i)

theorem dualPoleEvaluation_det_ne_zero {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ) :
    (dualHermiteEvaluation nodes m (dualPoleFamily nodes m)).det ≠ 0 := by
  intro hzero
  apply dualPoleReversedEvaluation_det_ne_zero nodes hnodes m
  rw [dualPoleReversedEvaluation, Matrix.det_permute, hzero, mul_zero]

theorem dualPoleCoefficient_det_ne_zero {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ) :
    (dualCoefficientMatrix m (dualPoleFamily nodes m)).det ≠ 0 := by
  have h := dualPoleEvaluation_det_ne_zero nodes hnodes m
  have hdeg : ∀ i, (dualPoleFamily nodes m i).natDegree < ∑ i, m i :=
    fun i => dualPolePolynomial_natDegree_lt nodes m ((groupEquiv m).symm i)
  rw [dualHermiteEvaluation_det nodes hnodes m (dualPoleFamily nodes m) hdeg] at h
  exact left_ne_zero_of_mul h

theorem dualPoleEvaluation_det_norm {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ) :
    ‖(dualHermiteEvaluation nodes m (dualPoleFamily nodes m)).det‖ =
      ∏ i : Fin r, ‖dualPoleGap nodes m i‖ ^ m i := by
  rw [← dual_norm_det_permute (dualBlockReverse m)]
  change ‖(dualPoleReversedEvaluation nodes m).det‖ = _
  rw [dualPoleReversedEvaluation_det nodes hnodes m, norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [norm_pow]


theorem dualInverse_deriv (a z : ℂ) (k : ℕ) :
    iteratedDeriv k (fun w : ℂ => (w - a)⁻¹) z =
      (-1 : ℂ) ^ k * (k.factorial : ℂ) / (z - a) ^ (k + 1) := by
  rw [iteratedDeriv_eq_iterate]
  have h := congrFun (iter_deriv_inv_linear_sub k (1 : ℂ) a) z
  simp only [one_mul, one_pow, mul_one] at h
  rw [h]
  have hk : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) := by omega
  rw [hk, _root_.zpow_neg, zpow_natCast, div_eq_mul_inv]

def dualRationalColumn (a : ℂ) (l : ℕ) (z : ℂ) : ℂ :=
  ((-1 : ℂ) ^ l / (l.factorial : ℂ)) * iteratedDeriv l (fun w : ℂ => (w - a)⁻¹) z

theorem dualRationalColumn_eq (a : ℂ) (l : ℕ) (z : ℂ) :
    dualRationalColumn a l z = ((z - a) ^ (l + 1))⁻¹ := by
  have hf : (l.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero l
  have hs : (-1 : ℂ) ^ l * (-1 : ℂ) ^ l = 1 := by rw [← mul_pow]; norm_num
  have hc : ((-1 : ℂ) ^ l / (l.factorial : ℂ)) *
      ((-1 : ℂ) ^ l * (l.factorial : ℂ)) = 1 := by
    calc
      _ = ((-1 : ℂ) ^ l * (-1 : ℂ) ^ l) * ((l.factorial : ℂ) / (l.factorial : ℂ)) := by ring
      _ = _ := by rw [hs, div_self hf, mul_one]
  rw [dualRationalColumn, dualInverse_deriv, ← mul_div_assoc, hc, one_div]

theorem dualRationalColumn_deriv (a : ℂ) (l k : ℕ) (z : ℂ) :
    iteratedDeriv k (dualRationalColumn a l) z =
      ((-1 : ℂ) ^ k / (l.factorial : ℂ)) *
        ((k + l).factorial : ℂ) / (z - a) ^ (k + l + 1) := by
  have hi : iteratedDeriv k (iteratedDeriv l (fun w : ℂ => (w - a)⁻¹)) z =
      iteratedDeriv (k + l) (fun w : ℂ => (w - a)⁻¹) z := by
    simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]
  have hs : (-1 : ℂ) ^ l * (-1 : ℂ) ^ l = 1 := by rw [← mul_pow]; norm_num
  unfold dualRationalColumn
  rw [iteratedDeriv_const_mul_field, hi, dualInverse_deriv, pow_add]
  calc
    _ = (((-1 : ℂ) ^ l * (-1 : ℂ) ^ l) *
      ((-1 : ℂ) ^ k / (l.factorial : ℂ))) *
        ((k + l).factorial : ℂ) / (z - a) ^ (k + l + 1) := by ring
    _ = _ := by rw [hs, one_mul]

theorem dualRationalColumn_analytic {a z : ℂ} (hza : z ≠ a) (l : ℕ) :
    AnalyticAt ℂ (dualRationalColumn a l) z := by
  have he : dualRationalColumn a l = fun z : ℂ => ((z - a) ^ (l + 1))⁻¹ :=
    funext (dualRationalColumn_eq a l)
  rw [he]
  exact ((analyticAt_id.sub analyticAt_const).pow (l + 1)).inv
    (pow_ne_zero _ (sub_ne_zero.2 hza))


def dualJetBlock {r : ℕ} (m : Fin r → ℕ) (n : Fin (∑ i, m i)) : Fin r :=
  ((groupEquiv m).symm n).1

def dualJetOrder {r : ℕ} (m : Fin r → ℕ) (n : Fin (∑ i, m i)) : ℕ :=
  ((groupEquiv m).symm n).2.val

@[simp] theorem dualJetBlock_at {r : ℕ} (m : Fin r → ℕ) (p : LaplaceJetIndex m) :
    dualJetBlock m (groupEquiv m p) = p.1 := by simp [dualJetBlock]

@[simp] theorem dualJetOrder_at {r : ℕ} (m : Fin r → ℕ) (p : LaplaceJetIndex m) :
    dualJetOrder m (groupEquiv m p) = p.2.val := by
  change ((groupEquiv m).symm (groupEquiv m p)).2.val = p.2.val
  rw [Equiv.symm_apply_apply]

theorem dualHermiteEvaluation_entry {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ)
    (polys : Fin (∑ i, m i) → ℂ[X]) (n : Fin (∑ i, m i)) (p : LaplaceJetIndex m) :
    dualHermiteEvaluation nodes m polys n (groupEquiv m p) =
      hasseFunctional (nodes p.1) p.2.val (polys n) := by
  change hasseFunctional (groupedNode nodes m (groupIndex m p))
    (repeatedJetOrder (groupedNode nodes m) (groupIndex m p)) (polys n) = _
  rw [groupedNode_at, grouped_repeatedJetOrder nodes hnodes m]

def dualOrdinaryHermiteEvaluation {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ)
    (polys : Fin (∑ i, m i) → ℂ[X]) : Matrix (Fin (∑ i, m i)) (Fin (∑ i, m i)) ℂ :=
  fun n q => iteratedDeriv (dualJetOrder m q) (fun z : ℂ => (polys n).eval z)
    (nodes (dualJetBlock m q))

theorem dualOrdinaryHermiteEvaluation_eq {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ)
    (polys : Fin (∑ i, m i) → ℂ[X]) :
    dualOrdinaryHermiteEvaluation nodes m polys =
      dualHermiteEvaluation nodes m polys *
        Matrix.diagonal (fun q => ((dualJetOrder m q).factorial : ℂ)) := by
  ext n q
  rcases (groupEquiv m).surjective q with ⟨p, rfl⟩
  rw [Matrix.mul_diagonal, dualHermiteEvaluation_entry nodes hnodes m]
  simp only [dualOrdinaryHermiteEvaluation, dualJetOrder_at, dualJetBlock_at]
  change iteratedDeriv p.2.val (fun z : ℂ => (polys n).eval z) (nodes p.1) =
    (Polynomial.hasseDeriv p.2.val (polys n)).eval (nodes p.1) * (p.2.val.factorial : ℂ)
  rw [hasse_eq_normalized_iteratedDeriv]
  have hf : (p.2.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p.2.val
  field_simp [hf]

theorem dualOrdinaryHermiteEvaluation_det {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ)
    (polys : Fin (∑ i, m i) → ℂ[X]) (hdeg : ∀ i, (polys i).natDegree < ∑ i, m i) :
    (dualOrdinaryHermiteEvaluation nodes m polys).det =
      (dualCoefficientMatrix m polys).det *
        (∏ j, ∏ i ∈ Finset.Iio j, (nodes j - nodes i) ^ (m i * m j)) *
          ∏ q : Fin (∑ i, m i), ((dualJetOrder m q).factorial : ℂ) := by
  rw [dualOrdinaryHermiteEvaluation_eq nodes hnodes m,
    Matrix.det_mul, Matrix.det_diagonal, dualHermiteEvaluation_det nodes hnodes m polys hdeg]

def dualOrdinaryRational {r : ℕ} (x y : Fin r → ℂ) (m : Fin r → ℕ) :
    Matrix (Fin (∑ i, m i)) (Fin (∑ i, m i)) ℂ :=
  fun n q => iteratedDeriv (dualJetOrder m n)
    (dualRationalColumn (y (dualJetBlock m q)) (dualJetOrder m q))
      (x (dualJetBlock m n))

def dualMultiplicationJet {r : ℕ} (x : Fin r → ℂ) (m : Fin r → ℕ) (D : ℂ[X]) :
    Matrix (Fin (∑ i, m i)) (Fin (∑ i, m i)) ℂ :=
  fun n s => if dualJetBlock m s = dualJetBlock m n ∧ dualJetOrder m s ≤ dualJetOrder m n then
    ((dualJetOrder m n).choose (dualJetOrder m s) : ℂ) *
      iteratedDeriv (dualJetOrder m n - dualJetOrder m s)
        (fun z : ℂ => D.eval z) (x (dualJetBlock m n)) else 0


theorem dualRationalColumn_mul_common {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ)
    (p : LaplaceJetIndex m) (z : ℂ) (hz : z ≠ nodes p.1) :
    dualRationalColumn (nodes p.1) p.2.val z * (dualCommonDenominator nodes m).eval z =
      (dualPolePolynomial nodes m p).eval z := by
  have he := congrArg (fun f : ℂ[X] => f.eval z) (dualPolePolynomial_clear_denominator nodes m p)
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C] at he
  rw [dualRationalColumn_eq, ← he]
  have hn : (z - nodes p.1) ^ (p.2.val + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hz)
  calc
    _ = (dualPolePolynomial nodes m p).eval z *
      (((z - nodes p.1) ^ (p.2.val + 1))⁻¹ * (z - nodes p.1) ^ (p.2.val + 1)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hn, mul_one]

theorem dualPoleProduct_deriv {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ)
    (p : LaplaceJetIndex m) (z : ℂ) (hz : z ≠ nodes p.1) (k : ℕ) :
    iteratedDeriv k (fun w : ℂ => (dualPolePolynomial nodes m p).eval w) z =
      ∑ s ∈ Finset.range (k + 1), (k.choose s : ℂ) *
        iteratedDeriv s (dualRationalColumn (nodes p.1) p.2.val) z *
          iteratedDeriv (k - s) (fun w : ℂ => (dualCommonDenominator nodes m).eval w) z := by
  have he : (fun w : ℂ => dualRationalColumn (nodes p.1) p.2.val w *
      (dualCommonDenominator nodes m).eval w) =ᶠ[𝓝 z]
      fun w => (dualPolePolynomial nodes m p).eval w := by
    filter_upwards [(isOpen_ne : IsOpen {w : ℂ | w ≠ nodes p.1}).mem_nhds hz] with w hw
    exact dualRationalColumn_mul_common nodes m p w hw
  have hD : AnalyticAt ℂ (fun w : ℂ => (dualCommonDenominator nodes m).eval w) z :=
    (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (dualCommonDenominator nodes m)) z (Set.mem_univ z)
  have h := he.iteratedDeriv_eq k
  rw [iteratedDeriv_fun_mul (dualRationalColumn_analytic hz p.2.val).contDiffAt hD.contDiffAt] at h
  exact h.symm

theorem dualMultiplicationJet_lower {r : ℕ} (x : Fin r → ℂ) (m : Fin r → ℕ) (D : ℂ[X]) :
    (dualMultiplicationJet x m D).IsLowerTriangular := by
  intro n j hnj
  rcases (groupEquiv m).surjective n with ⟨p, rfl⟩
  rcases (groupEquiv m).surjective j with ⟨q, rfl⟩
  simp only [dualMultiplicationJet, dualJetOrder_at, dualJetBlock_at]
  split_ifs with h
  · have hb : blockStart m q.1 = blockStart m p.1 := congrArg (blockStart m) h.1
    change blockStart m p.1 + p.2.val < blockStart m q.1 + q.2.val at hnj
    omega
  · rfl

theorem dualMultiplicationJet_diagonal {r : ℕ} (x : Fin r → ℂ) (m : Fin r → ℕ) (D : ℂ[X])
    (p : LaplaceJetIndex m) :
    dualMultiplicationJet x m D (groupEquiv m p) (groupEquiv m p) = D.eval (x p.1) := by
  simp only [dualMultiplicationJet, dualJetOrder_at, dualJetBlock_at, eq_self_iff_true,
    le_refl, and_self, ↓reduceIte, Nat.choose_self, Nat.cast_one, Nat.sub_self,
    iteratedDeriv_zero, one_mul]

theorem dualMultiplicationJet_det {r : ℕ} (x : Fin r → ℂ) (m : Fin r → ℕ) (D : ℂ[X]) :
    (dualMultiplicationJet x m D).det = ∏ i : Fin r, D.eval (x i) ^ m i := by
  rw [Matrix.det_of_isLowerTriangular _ (dualMultiplicationJet_lower x m D)]
  calc
    _ = ∏ p : LaplaceJetIndex m, D.eval (x p.1) := by
      rw [← (groupEquiv m).prod_comp]
      apply Finset.prod_congr rfl
      intro p _
      exact dualMultiplicationJet_diagonal x m D p
    _ = _ := by rw [Fintype.prod_sigma]; simp only [Fin.prod_const]


theorem dualFin_jet_sum (N k : ℕ) (hk : k < N) (F : ℕ → ℂ) :
    (∑ s : Fin N, if s.val ≤ k then F s.val else 0) = ∑ s ∈ Finset.range (k + 1), F s := by
  calc
    _ = ∑ s ∈ Finset.range N, if s ≤ k then F s else 0 :=
      Fin.sum_univ_eq_sum_range (fun s : ℕ => if s ≤ k then F s else 0) N
    _ = _ := by
      rw [← Finset.sum_filter]
      congr 1
      ext s
      simp only [Finset.mem_filter, Finset.mem_range]
      omega

theorem dualOrdinary_product_matrix {r : ℕ} (x y : Fin r → ℂ) (m : Fin r → ℕ)
    (hxy : ∀ i j, x i ≠ y j) :
    (dualOrdinaryHermiteEvaluation x m (dualPoleFamily y m)).transpose =
      dualMultiplicationJet x m (dualCommonDenominator y m) * dualOrdinaryRational x y m := by
  ext n q
  rcases (groupEquiv m).surjective n with ⟨p, rfl⟩
  rcases (groupEquiv m).surjective q with ⟨c, rfl⟩
  rw [Matrix.mul_apply]
  have hsum : (∑ s : Fin (∑ i, m i),
      dualMultiplicationJet x m (dualCommonDenominator y m) (groupEquiv m p) s *
        dualOrdinaryRational x y m s (groupEquiv m c)) =
      ∑ s : Fin (m p.1), if s.val ≤ p.2.val then
        (p.2.val.choose s.val : ℂ) *
          iteratedDeriv (p.2.val - s.val) (fun z : ℂ => (dualCommonDenominator y m).eval z) (x p.1) *
          iteratedDeriv s.val (dualRationalColumn (y c.1) c.2.val) (x p.1) else 0 := by
    rw [← (groupEquiv m).sum_comp, Fintype.sum_sigma, Fintype.sum_eq_single p.1]
    · apply Finset.sum_congr rfl
      intro s _
      simp only [dualMultiplicationJet, dualOrdinaryRational, dualJetOrder_at, dualJetBlock_at,
        eq_self_iff_true, true_and, ite_mul, zero_mul]
    · intro i hi
      apply Finset.sum_eq_zero
      intro s _
      simp only [dualMultiplicationJet, dualJetOrder_at, dualJetBlock_at,
        hi, false_and, ↓reduceIte, zero_mul]
  rw [hsum]
  let F : ℕ → ℂ := fun s => (p.2.val.choose s : ℂ) *
    iteratedDeriv (p.2.val - s) (fun z : ℂ => (dualCommonDenominator y m).eval z) (x p.1) *
      iteratedDeriv s (dualRationalColumn (y c.1) c.2.val) (x p.1)
  simp only [Matrix.transpose_apply, dualOrdinaryHermiteEvaluation, dualJetOrder_at,
    dualJetBlock_at, dualPoleFamily, Equiv.symm_apply_apply]
  change iteratedDeriv p.2.val (fun z : ℂ => (dualPolePolynomial y m c).eval z) (x p.1) =
    ∑ s : Fin (m p.1), if s.val ≤ p.2.val then F s.val else 0
  rw [dualFin_jet_sum (m p.1) p.2.val p.2.isLt F]
  rw [dualPoleProduct_deriv y m c (x p.1) (hxy p.1 c.1) p.2.val]
  apply Finset.sum_congr rfl
  intro s _
  dsimp only [F]
  ring


def dualVandermonde {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ) : ℂ :=
  ∏ j, ∏ i ∈ Finset.Iio j, (nodes j - nodes i) ^ (m i * m j)

theorem dualVandermonde_ne_zero {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ) : dualVandermonde nodes m ≠ 0 := by
  apply Finset.prod_ne_zero_iff.2
  intro j _
  apply Finset.prod_ne_zero_iff.2
  intro i hi
  apply pow_ne_zero
  apply sub_ne_zero.2
  intro he
  exact (ne_of_gt (Finset.mem_Iio.mp hi)) (hnodes he)

theorem dualOrdinaryRational_det_ne_zero {r : ℕ} (x y : Fin r → ℂ)
    (hx : Function.Injective x) (hy : Function.Injective y) (m : Fin r → ℕ)
    (hxy : ∀ i j, x i ≠ y j) : (dualOrdinaryRational x y m).det ≠ 0 := by
  have hdeg : ∀ i, (dualPoleFamily y m i).natDegree < ∑ i, m i :=
    fun i => dualPolePolynomial_natDegree_lt y m ((groupEquiv m).symm i)
  have hH : (dualOrdinaryHermiteEvaluation x m (dualPoleFamily y m)).det ≠ 0 := by
    rw [dualOrdinaryHermiteEvaluation_det x hx m (dualPoleFamily y m) hdeg]
    apply mul_ne_zero
    · exact mul_ne_zero (dualPoleCoefficient_det_ne_zero y hy m) (dualVandermonde_ne_zero x hx m)
    · apply Finset.prod_ne_zero_iff.2
      intro q _
      exact_mod_cast Nat.factorial_ne_zero (dualJetOrder m q)
  have he := congrArg Matrix.det (dualOrdinary_product_matrix x y m hxy)
  rw [Matrix.det_transpose, Matrix.det_mul] at he
  rw [he] at hH
  exact right_ne_zero_of_mul hH

def dualReindexedGram {r : ℕ} (nodes : Fin r → ℂ) (hpos : ∀ i, 0 < (nodes i).re)
    (m : Fin r → ℕ) : Matrix (Fin (∑ i, m i)) (Fin (∑ i, m i)) ℂ :=
  (laplaceJetGram nodes hpos m).submatrix (groupEquiv m).symm (groupEquiv m).symm

theorem dualOrdinaryRational_actual {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) :
    dualOrdinaryRational nodes (fun i => -conj (nodes i)) m =
      Matrix.diagonal (fun n => (-1 : ℂ) ^ dualJetOrder m n) *
        dualReindexedGram nodes hpos m *
          Matrix.diagonal (fun q => (((dualJetOrder m q).factorial : ℂ))⁻¹) := by
  ext n q
  rcases (groupEquiv m).surjective n with ⟨p, rfl⟩
  rcases (groupEquiv m).surjective q with ⟨c, rfl⟩
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [dualOrdinaryRational, dualReindexedGram, dualJetOrder_at, dualJetBlock_at,
    Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [dualRationalColumn_deriv, laplaceJetGram_entry]
  simp only [sub_neg_eq_add, div_eq_mul_inv]
  ring

theorem laplaceJetGram_det_ne_zero {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) :
    (laplaceJetGram nodes hpos m).det ≠ 0 := by
  have hy : Function.Injective (fun i : Fin r => -conj (nodes i)) := by
    intro i j h
    apply hnodes
    have hc := congrArg (fun z : ℂ => -conj z) h
    simpa using hc
  have hxy : ∀ i j, nodes i ≠ -conj (nodes j) := by
    intro i j h
    have hr := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.conj_re] at hr
    linarith [hpos i, hpos j]
  have hR := dualOrdinaryRational_det_ne_zero nodes (fun i => -conj (nodes i)) hnodes hy m hxy
  intro hzero
  apply hR
  rw [dualOrdinaryRational_actual nodes hpos m, Matrix.det_mul, Matrix.det_mul,
    dualReindexedGram, Matrix.det_submatrix_equiv_self, hzero, mul_zero, zero_mul]

theorem laplaceJetGram_posDef {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) :
    (laplaceJetGram nodes hpos m).PosDef :=
  (laplaceJetGram_posSemidef nodes hpos m).posDef_iff_det_ne_zero.mpr
    (laplaceJetGram_det_ne_zero nodes hnodes hpos m)


theorem dual_symmetric_product {r : ℕ} (F : Fin r → Fin r → ℝ)
    (hsym : ∀ i j, F i j = F j i) :
    (∏ i : Fin r, ∏ j : Fin r, F i j) =
      (∏ i : Fin r, F i i) * (∏ i : Fin r, ∏ j ∈ Finset.Iio i, F i j) ^ 2 := by
  have hterm : ∀ i j, F i j =
      (if j < i then F i j else 1) * (if i = j then F i j else 1) *
        (if i < j then F i j else 1) := by
    intro i j
    by_cases he : i = j
    · subst j
      simp
    · rcases lt_or_gt_of_ne he with h | h
      · simp [h, not_lt_of_ge h.le, he]
      · simp [h, not_lt_of_ge h.le, he]
  have hlo : (∏ i : Fin r, ∏ j : Fin r, if j < i then F i j else 1) =
      ∏ i : Fin r, ∏ j ∈ Finset.Iio i, F i j := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  have hdiag : (∏ i : Fin r, ∏ j : Fin r, if i = j then F i j else 1) = ∏ i : Fin r, F i i := by
    apply Finset.prod_congr rfl
    intro i _
    simp
  have hup : (∏ i : Fin r, ∏ j : Fin r, if i < j then F i j else 1) =
      ∏ i : Fin r, ∏ j : Fin r, if j < i then F i j else 1 := by
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j _
    split_ifs with h
    · exact hsym j i
    · rfl
  calc
    _ = ∏ i : Fin r, ∏ j : Fin r,
        (if j < i then F i j else 1) * (if i = j then F i j else 1) *
          (if i < j then F i j else 1) := by
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro j _
      exact hterm i j
    _ = (∏ i : Fin r, ∏ j : Fin r, if j < i then F i j else 1) *
        (∏ i : Fin r, ∏ j : Fin r, if i = j then F i j else 1) *
        (∏ i : Fin r, ∏ j : Fin r, if i < j then F i j else 1) := by
      simp only [Finset.prod_mul_distrib]
    _ = _ := by rw [hup, hlo, hdiag]; ring

def dualNormVandermonde {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ) : ℝ :=
  ∏ j, ∏ i ∈ Finset.Iio j, ‖nodes j - nodes i‖ ^ (m i * m j)

theorem dualVandermonde_norm {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ) :
    ‖dualVandermonde nodes m‖ = dualNormVandermonde nodes m := by
  simp only [dualVandermonde, dualNormVandermonde, norm_prod, norm_pow]

theorem dualNormVandermonde_pos {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ) : 0 < dualNormVandermonde nodes m := by
  rw [← dualVandermonde_norm]
  exact norm_pos_iff.2 (dualVandermonde_ne_zero nodes hnodes m)


theorem dualPoleGap_norm_product {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ) :
    (∏ i : Fin r, ‖dualPoleGap nodes m i‖ ^ m i) = dualNormVandermonde nodes m ^ 2 := by
  let F : Fin r → Fin r → ℝ := fun i j =>
    if i = j then 1 else ‖nodes i - nodes j‖ ^ (m i * m j)
  have hsym : ∀ i j, F i j = F j i := by
    intro i j
    by_cases h : i = j
    · subst j
      rfl
    · simp only [F, if_neg h, if_neg (Ne.symm h), norm_sub_rev, Nat.mul_comm]
  have hrow : ∀ i : Fin r, ‖dualPoleGap nodes m i‖ ^ m i = ∏ j : Fin r, F i j := by
    intro i
    have hprod := Finset.prod_erase_mul Finset.univ (F i) (Finset.mem_univ i)
    rw [← hprod]
    simp only [F, if_pos rfl, mul_one]
    rw [dualPoleGap, norm_prod, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    rw [if_neg (Ne.symm hji), norm_pow, ← pow_mul, Nat.mul_comm]
  have hlo : (∏ i : Fin r, ∏ j ∈ Finset.Iio i, F i j) = dualNormVandermonde nodes m := by
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j hj
    have hji := Finset.mem_Iio.mp hj
    simp only [F, if_neg (ne_of_gt hji), dualNormVandermonde, Nat.mul_comm]
  calc
    _ = ∏ i : Fin r, ∏ j : Fin r, F i j := by
      apply Finset.prod_congr rfl
      intro i _
      exact hrow i
    _ = (∏ i : Fin r, F i i) * (∏ i : Fin r, ∏ j ∈ Finset.Iio i, F i j) ^ 2 :=
      dual_symmetric_product F hsym
    _ = _ := by rw [hlo]; simp only [F, if_pos rfl, Finset.prod_const_one, one_mul]

theorem dualPoleCoefficient_det_norm {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ) :
    ‖(dualCoefficientMatrix m (dualPoleFamily nodes m)).det‖ = dualNormVandermonde nodes m := by
  have hdeg : ∀ i, (dualPoleFamily nodes m i).natDegree < ∑ i, m i :=
    fun i => dualPolePolynomial_natDegree_lt nodes m ((groupEquiv m).symm i)
  have he := congrArg norm (dualHermiteEvaluation_det nodes hnodes m (dualPoleFamily nodes m) hdeg)
  rw [dualPoleEvaluation_det_norm nodes hnodes m, norm_mul] at he
  change (∏ i : Fin r, ‖dualPoleGap nodes m i‖ ^ m i) =
    ‖(dualCoefficientMatrix m (dualPoleFamily nodes m)).det‖ * ‖dualVandermonde nodes m‖ at he
  rw [dualVandermonde_norm, dualPoleGap_norm_product] at he
  apply mul_right_cancel₀ (ne_of_gt (dualNormVandermonde_pos nodes hnodes m))
  calc
    _ = dualNormVandermonde nodes m ^ 2 := he.symm
    _ = _ := pow_two _

def dualJetFactorialProduct {r : ℕ} (m : Fin r → ℕ) : ℝ :=
  ∏ q : Fin (∑ i, m i), ((dualJetOrder m q).factorial : ℝ)

theorem dualJetFactorialProduct_pos {r : ℕ} (m : Fin r → ℕ) : 0 < dualJetFactorialProduct m := by
  apply Finset.prod_pos
  intro q _
  exact_mod_cast Nat.factorial_pos (dualJetOrder m q)

theorem dualOrdinaryHermiteEvaluation_det_norm {r : ℕ} (x y : Fin r → ℂ)
    (hx : Function.Injective x) (hy : Function.Injective y) (m : Fin r → ℕ) :
    ‖(dualOrdinaryHermiteEvaluation x m (dualPoleFamily y m)).det‖ =
      dualNormVandermonde y m * dualNormVandermonde x m * dualJetFactorialProduct m := by
  have hdeg : ∀ i, (dualPoleFamily y m i).natDegree < ∑ i, m i :=
    fun i => dualPolePolynomial_natDegree_lt y m ((groupEquiv m).symm i)
  rw [dualOrdinaryHermiteEvaluation_det x hx m (dualPoleFamily y m) hdeg,
    norm_mul, norm_mul, dualPoleCoefficient_det_norm y hy m]
  change dualNormVandermonde y m * ‖dualVandermonde x m‖ *
      ‖∏ q : Fin (∑ i, m i), ((dualJetOrder m q).factorial : ℂ)‖ = _
  rw [dualVandermonde_norm, norm_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro q _
  exact Complex.norm_natCast _


theorem dualOrdinaryRational_actual_det_norm {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) :
    ‖(dualOrdinaryRational nodes (fun i => -conj (nodes i)) m).det‖ =
      ‖(laplaceJetGram nodes hpos m).det‖ / dualJetFactorialProduct m := by
  rw [dualOrdinaryRational_actual nodes hpos m, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_diagonal, norm_mul, norm_mul, norm_prod, norm_prod]
  simp only [norm_pow, norm_neg, norm_one, one_pow, Finset.prod_const_one, one_mul,
    norm_inv, Complex.norm_natCast]
  rw [dualReindexedGram, Matrix.det_submatrix_equiv_self, Finset.prod_inv_distrib,
    dualJetFactorialProduct, div_eq_mul_inv]

theorem dualNormVandermonde_neg_conj {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ) :
    dualNormVandermonde (fun i => -conj (nodes i)) m = dualNormVandermonde nodes m := by
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  have he : -conj (nodes j) - -conj (nodes i) = -conj (nodes j - nodes i) := by
    simp only [map_sub]
    ring
  rw [he, norm_neg, Complex.norm_conj]

def dualGramDenominator {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ) : ℝ :=
  ∏ i : Fin r, ∏ j : Fin r, ‖nodes i + conj (nodes j)‖ ^ (m i * m j)

theorem dualGramDenominator_pos {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) : 0 < dualGramDenominator nodes m := by
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j _
  apply pow_pos
  apply norm_pos_iff.2
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at hr
  linarith [hpos i, hpos j]

theorem dualMultiplicationJet_actual_det_norm {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ) :
    ‖(dualMultiplicationJet nodes m (dualCommonDenominator (fun i => -conj (nodes i)) m)).det‖ =
      dualGramDenominator nodes m := by
  rw [dualMultiplicationJet_det, norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [norm_pow, dualCommonDenominator, Polynomial.eval_prod, norm_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    norm_pow, ← pow_mul, sub_neg_eq_add, Nat.mul_comm]

theorem laplaceJetGram_det_norm_allpairs {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) :
    ‖(laplaceJetGram nodes hpos m).det‖ =
      dualJetFactorialProduct m ^ 2 * dualNormVandermonde nodes m ^ 2 /
        dualGramDenominator nodes m := by
  have hy : Function.Injective (fun i : Fin r => -conj (nodes i)) := by
    intro i j h
    apply hnodes
    have hc := congrArg (fun z : ℂ => -conj z) h
    simpa using hc
  have hxy : ∀ i j, nodes i ≠ -conj (nodes j) := by
    intro i j h
    have hr := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.conj_re] at hr
    linarith [hpos i, hpos j]
  have he := congrArg (fun A : Matrix (Fin (∑ i, m i)) (Fin (∑ i, m i)) ℂ => ‖A.det‖)
    (dualOrdinary_product_matrix nodes (fun i => -conj (nodes i)) m hxy)
  rw [Matrix.det_transpose, Matrix.det_mul, norm_mul,
    dualOrdinaryHermiteEvaluation_det_norm nodes _ hnodes hy m,
    dualNormVandermonde_neg_conj, dualMultiplicationJet_actual_det_norm,
    dualOrdinaryRational_actual_det_norm nodes hpos m] at he
  apply (eq_div_iff (ne_of_gt (dualGramDenominator_pos nodes hpos m))).2
  have hF := ne_of_gt (dualJetFactorialProduct_pos m)
  field_simp [hF] at he
  nlinarith [he]


theorem dualNorm_add_conj_symm (a b : ℂ) : ‖a + conj b‖ = ‖b + conj a‖ := by
  have he : b + conj a = conj (a + conj b) := by simp; ring
  rw [he, Complex.norm_conj]

theorem dualJetFactorialProduct_square {r : ℕ} (m : Fin r → ℕ) :
    dualJetFactorialProduct m ^ 2 =
      ∏ i : Fin r, ∏ k : Fin (m i), (k.val.factorial : ℝ) ^ 2 := by
  rw [dualJetFactorialProduct, ← Finset.prod_pow, ← (groupEquiv m).prod_comp, Fintype.prod_sigma]
  simp only [dualJetOrder_at]

theorem dualNormVandermonde_square {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ) :
    dualNormVandermonde nodes m ^ 2 =
      ∏ j : Fin r, ∏ i ∈ Finset.Iio j, ‖nodes i - nodes j‖ ^ (2 * m i * m j) := by
  rw [dualNormVandermonde, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_mul, norm_sub_rev]
  congr 1
  ring

theorem dualGramDenominator_report {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) :
    dualGramDenominator nodes m =
      (∏ i : Fin r, (2 * (nodes i).re) ^ (m i ^ 2)) *
        (∏ j : Fin r, ∏ i ∈ Finset.Iio j, ‖nodes i + conj (nodes j)‖ ^ (2 * m i * m j)) := by
  let F : Fin r → Fin r → ℝ := fun i j => ‖nodes i + conj (nodes j)‖ ^ (m i * m j)
  have hs : ∀ i j, F i j = F j i := by
    intro i j
    simp only [F, dualNorm_add_conj_symm (nodes i) (nodes j), Nat.mul_comm]
  have hd : (∏ i : Fin r, F i i) = ∏ i : Fin r, (2 * (nodes i).re) ^ (m i ^ 2) := by
    apply Finset.prod_congr rfl
    intro i _
    have he : nodes i + conj (nodes i) = ((2 * (nodes i).re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp <;> ring
    simp only [F, he, Complex.norm_of_nonneg (by linarith [hpos i] : 0 ≤ 2 * (nodes i).re), pow_two]
  have hc : (∏ j : Fin r, ∏ i ∈ Finset.Iio j, F j i) ^ 2 =
      ∏ j : Fin r, ∏ i ∈ Finset.Iio j, ‖nodes i + conj (nodes j)‖ ^ (2 * m i * m j) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro j _
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    dsimp only [F]
    rw [← pow_mul, dualNorm_add_conj_symm (nodes j) (nodes i)]
    congr 1
    ring
  change (∏ i : Fin r, ∏ j : Fin r, F i j) = _
  rw [dual_symmetric_product F hs, hd, hc]

def laplaceJetCauchyDeterminant {r : ℕ} (nodes : Fin r → ℂ) (m : Fin r → ℕ) : ℝ :=
  ((∏ i : Fin r, ∏ k : Fin (m i), (k.val.factorial : ℝ) ^ 2) *
    (∏ j : Fin r, ∏ i ∈ Finset.Iio j, ‖nodes i - nodes j‖ ^ (2 * m i * m j))) /
      ((∏ i : Fin r, (2 * (nodes i).re) ^ (m i ^ 2)) *
        (∏ j : Fin r, ∏ i ∈ Finset.Iio j, ‖nodes i + conj (nodes j)‖ ^ (2 * m i * m j)))

theorem laplaceJetGram_det_eq_norm {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) :
    (laplaceJetGram nodes hpos m).det = (‖(laplaceJetGram nodes hpos m).det‖ : ℂ) := by
  have hdet := (laplaceJetGram_posSemidef nodes hpos m).det_nonneg
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    exact Complex.re_eq_norm.mpr hdet
  · simp only [Complex.ofReal_im]
    exact (Complex.nonneg_iff.mp hdet).2.symm

theorem laplaceJetGram_confluent_determinant {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) :
    (laplaceJetGram nodes hpos m).det = (laplaceJetCauchyDeterminant nodes m : ℂ) := by
  rw [laplaceJetGram_det_eq_norm, laplaceJetGram_det_norm_allpairs nodes hnodes hpos m,
    dualJetFactorialProduct_square, dualNormVandermonde_square, dualGramDenominator_report nodes hpos m]
  rfl

theorem laplace_jet_gram {r : ℕ} (nodes : Fin r → ℂ) (hnodes : Function.Injective nodes)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) (hm : ∀ i, 1 ≤ m i) :
    (∀ p q : LaplaceJetIndex m, laplaceJetGram nodes hpos m p q =
      ((p.2.val + q.2.val).factorial : ℂ) /
        (nodes p.1 + conj (nodes q.1)) ^ (p.2.val + q.2.val + 1)) ∧
      (laplaceJetGram nodes hpos m).PosDef ∧
      (laplaceJetGram nodes hpos m).det = (laplaceJetCauchyDeterminant nodes m : ℂ) :=
  ⟨laplaceJetGram_entry nodes hpos m, laplaceJetGram_posDef nodes hnodes hpos m,
    laplaceJetGram_confluent_determinant nodes hnodes hpos m⟩


def dualJetOutput {r : ℕ} (nodes : Fin r → ℂ) (hpos : ∀ i, 0 < (nodes i).re)
    (m : Fin r → ℕ) (x : LaplaceJetIndex m → ℂ) : CausalProbeL2 :=
  ∑ p : LaplaceJetIndex m, x p • laplaceJetWitness nodes hpos m p

def dualJetSynthesis {r : ℕ} (nodes : Fin r → ℂ) (hpos : ∀ i, 0 < (nodes i).re)
    (m : Fin r → ℕ) : (LaplaceJetIndex m → ℂ) →ₗ[ℂ] CausalProbeL2 :=
  Fintype.linearCombination ℂ (laplaceJetWitness nodes hpos m)

def dualJetSpace {r : ℕ} (nodes : Fin r → ℂ) (hpos : ∀ i, 0 < (nodes i).re)
    (m : Fin r → ℕ) : Submodule ℂ CausalProbeL2 := (dualJetSynthesis nodes hpos m).range

instance dualJetSpace_finiteDimensional {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) : FiniteDimensional ℂ (dualJetSpace nodes hpos m) :=
  LinearMap.finiteDimensional_range (dualJetSynthesis nodes hpos m)

instance dualJetSpace_complete {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) : CompleteSpace (dualJetSpace nodes hpos m) :=
  FiniteDimensional.complete ℂ (dualJetSpace nodes hpos m)

def dualJetProjection {r : ℕ} (nodes : Fin r → ℂ) (hpos : ∀ i, 0 < (nodes i).re)
    (m : Fin r → ℕ) (f : CausalProbeL2) : CausalProbeL2 :=
  ((dualJetSpace nodes hpos m).orthogonalProjectionOnto f : CausalProbeL2)

theorem dualJetProjection_mem {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) (f : CausalProbeL2) :
    dualJetProjection nodes hpos m f ∈ dualJetSpace nodes hpos m :=
  ((dualJetSpace nodes hpos m).orthogonalProjectionOnto f).property

def dualJetPairings {r : ℕ} (nodes : Fin r → ℂ) (hpos : ∀ i, 0 < (nodes i).re)
    (m : Fin r → ℕ) (f : CausalProbeL2) (p : LaplaceJetIndex m) : ℂ :=
  inner ℂ (laplaceJetWitness nodes hpos m p) f

def dualJetCoefficients {r : ℕ} (nodes : Fin r → ℂ) (hpos : ∀ i, 0 < (nodes i).re)
    (m : Fin r → ℕ) (f : CausalProbeL2) : LaplaceJetIndex m → ℂ :=
  (laplaceJetGram nodes hpos m)⁻¹ *ᵥ dualJetPairings nodes hpos m f

theorem dualJetCoefficients_normal {r : ℕ} (nodes : Fin r → ℂ) (hnodes : Function.Injective nodes)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) (f : CausalProbeL2) :
    laplaceJetGram nodes hpos m *ᵥ dualJetCoefficients nodes hpos m f = dualJetPairings nodes hpos m f := by
  unfold dualJetCoefficients
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.2 (laplaceJetGram_det_ne_zero nodes hnodes hpos m)), Matrix.one_mulVec]

theorem dualJetWitness_inner_output {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) (p : LaplaceJetIndex m)
    (x : LaplaceJetIndex m → ℂ) :
    inner ℂ (laplaceJetWitness nodes hpos m p) (dualJetOutput nodes hpos m x) =
      (laplaceJetGram nodes hpos m *ᵥ x) p := by
  simp only [dualJetOutput, inner_sum, inner_smul_right (𝕜 := ℂ) (E := CausalProbeL2),
    laplaceJetGram, Matrix.gram_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem dualJetResidual_inner_witness {r : ℕ} (nodes : Fin r → ℂ) (hnodes : Function.Injective nodes)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) (f : CausalProbeL2) (p : LaplaceJetIndex m) :
    inner ℂ (laplaceJetWitness nodes hpos m p)
      (f - dualJetOutput nodes hpos m (dualJetCoefficients nodes hpos m f)) = 0 := by
  rw [inner_sub_right, dualJetWitness_inner_output]
  have hn := congrFun (dualJetCoefficients_normal nodes hnodes hpos m f) p
  change dualJetPairings nodes hpos m f p - _ = 0
  rw [hn, sub_self]

theorem dualJetResidual_inner_space {r : ℕ} (nodes : Fin r → ℂ) (hnodes : Function.Injective nodes)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) (f : CausalProbeL2)
    {g : CausalProbeL2} (hg : g ∈ dualJetSpace nodes hpos m) :
    inner ℂ (f - dualJetOutput nodes hpos m (dualJetCoefficients nodes hpos m f)) g = 0 := by
  rcases hg with ⟨x, rfl⟩
  change inner ℂ (f - dualJetOutput nodes hpos m (dualJetCoefficients nodes hpos m f))
    (∑ p : LaplaceJetIndex m, x p • laplaceJetWitness nodes hpos m p) = 0
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro p _
  rw [inner_smul_right (𝕜 := ℂ) (E := CausalProbeL2)]
  have hz : inner ℂ (f - dualJetOutput nodes hpos m (dualJetCoefficients nodes hpos m f))
      (laplaceJetWitness nodes hpos m p) = 0 := by
    rw [← inner_conj_symm, dualJetResidual_inner_witness nodes hnodes hpos m f p, map_zero]
  rw [hz, mul_zero]

theorem dualJetProjection_eq_coefficients {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (hpos : ∀ i, 0 < (nodes i).re)
    (m : Fin r → ℕ) (f : CausalProbeL2) :
    dualJetProjection nodes hpos m f = dualJetOutput nodes hpos m (dualJetCoefficients nodes hpos m f) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨dualJetCoefficients nodes hpos m f, rfl⟩
  · intro g hg
    exact dualJetResidual_inner_space nodes hnodes hpos m f hg

theorem dualJetTarget_inner_output {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ)
    (f : CausalProbeL2) (x : LaplaceJetIndex m → ℂ) :
    inner ℂ f (dualJetOutput nodes hpos m x) = star (dualJetPairings nodes hpos m f) ⬝ᵥ x := by
  simp only [dualJetOutput, inner_sum, inner_smul_right (𝕜 := ℂ) (E := CausalProbeL2),
    dotProduct, Pi.star_apply, dualJetPairings]
  apply Finset.sum_congr rfl
  intro p _
  rw [← inner_conj_symm]
  simp only [RCLike.star_def]
  ring

theorem dualJetProjection_norm_sq {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (hpos : ∀ i, 0 < (nodes i).re)
    (m : Fin r → ℕ) (f : CausalProbeL2) :
    ((‖dualJetProjection nodes hpos m f‖ ^ 2 : ℝ) : ℂ) =
      star (dualJetPairings nodes hpos m f) ⬝ᵥ
        ((laplaceJetGram nodes hpos m)⁻¹ *ᵥ dualJetPairings nodes hpos m f) := by
  have hz := dualJetResidual_inner_space nodes hnodes hpos m f (dualJetProjection_mem nodes hpos m f)
  rw [← dualJetProjection_eq_coefficients nodes hnodes hpos m f, inner_sub_left] at hz
  have hi := sub_eq_zero.mp hz
  calc
    _ = inner ℂ (dualJetProjection nodes hpos m f) (dualJetProjection nodes hpos m f) := by
      rw [inner_self_eq_norm_sq_to_K]
      simp only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow]
    _ = inner ℂ f (dualJetProjection nodes hpos m f) := hi.symm
    _ = _ := by
      rw [dualJetProjection_eq_coefficients nodes hnodes hpos m f, dualJetTarget_inner_output]
      rfl

theorem dualJetPairings_target_derivative {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) (p : LaplaceJetIndex m) :
    dualJetPairings nodes hpos m probeTarget p = (-1 : ℂ) ^ p.2.val *
      iteratedDeriv p.2.val (probeLaplace probeV) (nodes p.1) := by
  have he : (fun z : ℂ => CCM.nativeCausalLaplaceMoment z 0 (probeTarget : ProbeL2)) =
      probeLaplace probeV := funext probeTarget_laplace_eq_physical
  have hd := CCM.nativeCausalLaplaceMoment_iteratedDeriv (nodes p.1) (hpos p.1) p.2.val probeTarget
  rw [he] at hd
  rw [dualJetPairings, laplaceJetWitness,
    CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment, hd]
  have hs : (-1 : ℂ) ^ p.2.val * (-1 : ℂ) ^ p.2.val = 1 := by rw [← mul_pow]; norm_num
  rw [← mul_assoc, hs, one_mul]

theorem dualActualZero_annihilates_closure (rho : zetaZeroConfig.carrier)
    (hright : (1 / 2 : ℝ) < (rho : ℂ).re) (k : ℕ) (hk : k < zeroMult (rho : ℂ))
    {f : CausalProbeL2} (hf : f ∈ closure (Set.range probeOperator)) :
    inner ℂ (CCM.nativeCausalExponentialWitness ((rho : ℂ) - 1 / 2)
      (by simp only [Complex.sub_re]; norm_num; linarith) k) f = 0 := by
  have hw : 0 < ((rho : ℂ) - 1 / 2).re := by simp only [Complex.sub_re]; norm_num; linarith
  have hord := ExceptionalZero.nativeActualKernelLaplace_order_of_zero 0 (le_rfl) rho
    ((rho : ℂ) - 1 / 2) hw (by simp)
  apply CCM.nativeCausalExponentialWitness_annihilates_rangeClosure_of_kernel_moments 0 (le_rfl)
    ((rho : ℂ) - 1 / 2) hw k
  · intro j hj
    exact CCM.nativeCompletionKernelLaplaceMoment_vanishes_below_analyticOrder 0 (le_rfl)
      ((rho : ℂ) - 1 / 2) hw (zeroMult (rho : ℂ)) (le_of_eq hord.symm) j (by omega)
  · exact hf


def dualJetBound {r : ℕ} (nodes : Fin r → ℂ) (hpos : ∀ i, 0 < (nodes i).re)
    (m : Fin r → ℕ) (f : CausalProbeL2) : ℝ :=
  (star (dualJetPairings nodes hpos m f) ⬝ᵥ
    ((laplaceJetGram nodes hpos m)⁻¹ *ᵥ dualJetPairings nodes hpos m f)).re

theorem dualJetBound_eq_norm_sq {r : ℕ} (nodes : Fin r → ℂ) (hnodes : Function.Injective nodes)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) (f : CausalProbeL2) :
    dualJetBound nodes hpos m f = ‖dualJetProjection nodes hpos m f‖ ^ 2 := by
  have h := congrArg Complex.re (dualJetProjection_norm_sq nodes hnodes hpos m f)
  simpa only [Complex.ofReal_re, dualJetBound] using h.symm

theorem dualJetProjection_zero_of_pairings {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) (f : CausalProbeL2)
    (hz : ∀ p : LaplaceJetIndex m, dualJetPairings nodes hpos m f p = 0) :
    dualJetProjection nodes hpos m f = 0 := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact (dualJetSpace nodes hpos m).zero_mem
  · intro g hg
    rcases hg with ⟨x, rfl⟩
    change inner ℂ (f - 0) (∑ p : LaplaceJetIndex m, x p • laplaceJetWitness nodes hpos m p) = 0
    rw [sub_zero, inner_sum]
    apply Finset.sum_eq_zero
    intro p _
    rw [inner_smul_right (𝕜 := ℂ) (E := CausalProbeL2)]
    have hp : inner ℂ f (laplaceJetWitness nodes hpos m p) = 0 := by
      rw [← inner_conj_symm]
      change conj (dualJetPairings nodes hpos m f p) = 0
      rw [hz p, map_zero]
    rw [hp, mul_zero]

theorem dualJetProjection_le_infDist {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ)
    (v : CausalProbeL2) (S : Set CausalProbeL2) (hS : S.Nonempty)
    (hAnn : ∀ f ∈ S, ∀ p : LaplaceJetIndex m, dualJetPairings nodes hpos m f p = 0) :
    ‖dualJetProjection nodes hpos m v‖ ≤ Metric.infDist v S := by
  apply (Metric.le_infDist hS).2
  intro f hf
  have hp := dualJetProjection_zero_of_pairings nodes hpos m f (hAnn f hf)
  have hn := (dualJetSpace nodes hpos m).norm_starProjection_apply_le (v - f)
  rw [map_sub] at hn
  change (dualJetSpace nodes hpos m).starProjection f = 0 at hp
  rw [hp, sub_zero] at hn
  simpa only [dist_eq_norm, dualJetProjection, Submodule.starProjection_apply] using hn

def dualZeroNodes {r : ℕ} (rho : Fin r → zetaZeroConfig.carrier) (i : Fin r) : ℂ :=
  (rho i : ℂ) - 1 / 2

theorem dualZeroNodes_positive {r : ℕ} (rho : Fin r → zetaZeroConfig.carrier)
    (hright : ∀ i, (1 / 2 : ℝ) < (rho i : ℂ).re) : ∀ i, 0 < (dualZeroNodes rho i).re := by
  intro i
  simp only [dualZeroNodes, Complex.sub_re]
  norm_num
  linarith [hright i]

theorem dualZeroNodes_injective {r : ℕ} (rho : Fin r → zetaZeroConfig.carrier)
    (hdistinct : Function.Injective (fun i => (rho i : ℂ))) : Function.Injective (dualZeroNodes rho) := by
  intro i j h
  apply hdistinct
  have he := congrArg (fun z : ℂ => z + 1 / 2) h
  simpa only [dualZeroNodes, sub_add_cancel] using he

theorem dualZeroProjection_distance {r : ℕ} (rho : Fin r → zetaZeroConfig.carrier)
    (hdistinct : Function.Injective (fun i => (rho i : ℂ)))
    (hright : ∀ i, (1 / 2 : ℝ) < (rho i : ℂ).re) (m : Fin r → ℕ)
    (hallow : ∀ i, m i ≤ zeroMult (rho i : ℂ)) :
    ‖dualJetProjection (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m probeTarget‖ ≤
      Metric.infDist probeTarget (closure (Set.range probeOperator)) := by
  apply dualJetProjection_le_infDist
  · exact ⟨0, subset_closure ⟨0, by simp⟩⟩
  · intro f hf p
    exact dualActualZero_annihilates_closure (rho p.1) (hright p.1) p.2.val
      (Nat.lt_of_lt_of_le p.2.isLt (hallow p.1)) hf

theorem dualZeroBound_distance {r : ℕ} (rho : Fin r → zetaZeroConfig.carrier)
    (hdistinct : Function.Injective (fun i => (rho i : ℂ)))
    (hright : ∀ i, (1 / 2 : ℝ) < (rho i : ℂ).re) (m : Fin r → ℕ)
    (hallow : ∀ i, m i ≤ zeroMult (rho i : ℂ)) :
    dualJetBound (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m probeTarget ≤
      Metric.infDist probeTarget (closure (Set.range probeOperator)) ^ 2 := by
  rw [dualJetBound_eq_norm_sq _ (dualZeroNodes_injective rho hdistinct)]
  exact pow_le_pow_left₀ (norm_nonneg _) (dualZeroProjection_distance rho hdistinct hright m hallow) 2

theorem dualZeroBound_complex_distance {r : ℕ} (rho : Fin r → zetaZeroConfig.carrier)
    (hdistinct : Function.Injective (fun i => (rho i : ℂ)))
    (hright : ∀ i, (1 / 2 : ℝ) < (rho i : ℂ).re) (m : Fin r → ℕ)
    (hallow : ∀ i, m i ≤ zeroMult (rho i : ℂ)) :
    star (dualJetPairings (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m probeTarget) ⬝ᵥ
      ((laplaceJetGram (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m)⁻¹ *ᵥ
        dualJetPairings (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m probeTarget) ≤
      ((Metric.infDist probeTarget (closure (Set.range probeOperator)) ^ 2 : ℝ) : ℂ) := by
  rw [← dualJetProjection_norm_sq _ (dualZeroNodes_injective rho hdistinct)]
  apply Complex.le_def.2
  constructor
  · exact pow_le_pow_left₀ (norm_nonneg _) (dualZeroProjection_distance rho hdistinct hright m hallow) 2
  · rfl


theorem dualJetWitness_mem_space {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) (p : LaplaceJetIndex m) :
    laplaceJetWitness nodes hpos m p ∈ dualJetSpace nodes hpos m := by
  classical
  refine ⟨Pi.single p 1, ?_⟩
  change dualJetOutput nodes hpos m (Pi.single p 1) = _
  simp [dualJetOutput]

theorem dualJetSpace_le_of_embedding {r s : ℕ} (nodes : Fin r → ℂ) (nodes' : Fin s → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (hpos' : ∀ i, 0 < (nodes' i).re)
    (m : Fin r → ℕ) (m' : Fin s → ℕ) (e : LaplaceJetIndex m → LaplaceJetIndex m')
    (heNode : ∀ p, nodes' (e p).1 = nodes p.1) (heOrder : ∀ p, (e p).2.val = p.2.val) :
    dualJetSpace nodes hpos m ≤ dualJetSpace nodes' hpos' m' := by
  rintro g ⟨x, rfl⟩
  change (∑ p : LaplaceJetIndex m, x p • laplaceJetWitness nodes hpos m p) ∈
    dualJetSpace nodes' hpos' m'
  apply Submodule.sum_mem
  intro p _
  apply Submodule.smul_mem
  have hw : laplaceJetWitness nodes hpos m p = laplaceJetWitness nodes' hpos' m' (e p) := by
    simp only [laplaceJetWitness, heNode p, heOrder p]
  rw [hw]
  exact dualJetWitness_mem_space nodes' hpos' m' (e p)

theorem dualJetProjection_norm_sq_mono {r s : ℕ} (nodes : Fin r → ℂ) (nodes' : Fin s → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (hpos' : ∀ i, 0 < (nodes' i).re)
    (m : Fin r → ℕ) (m' : Fin s → ℕ)
    (hspace : dualJetSpace nodes hpos m ≤ dualJetSpace nodes' hpos' m') (f : CausalProbeL2) :
    ‖dualJetProjection nodes hpos m f‖ ^ 2 ≤ ‖dualJetProjection nodes' hpos' m' f‖ ^ 2 := by
  let u := dualJetProjection nodes hpos m f
  let v := dualJetProjection nodes' hpos' m' f
  have hu : u ∈ dualJetSpace nodes hpos m := dualJetProjection_mem nodes hpos m f
  have hz1 : inner ℂ (f - u) u = 0 :=
    (dualJetSpace nodes hpos m).starProjection_inner_eq_zero f u hu
  have hz2 : inner ℂ (f - v) u = 0 :=
    (dualJetSpace nodes' hpos' m').starProjection_inner_eq_zero f u (hspace hu)
  have hz : inner ℂ (v - u) u = 0 := by
    calc
      _ = inner ℂ (f - u) u - inner ℂ (f - v) u := by
        rw [inner_sub_left, inner_sub_left, inner_sub_left]
        ring
      _ = 0 := by rw [hz1, hz2, sub_self]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v - u) u hz
  rw [sub_add_cancel] at hp
  simp only [← pow_two] at hp
  change ‖u‖ ^ 2 ≤ ‖v‖ ^ 2
  nlinarith [sq_nonneg ‖v - u‖]

theorem dualJetBound_mono_of_embedding {r s : ℕ} (nodes : Fin r → ℂ) (nodes' : Fin s → ℂ)
    (hnodes : Function.Injective nodes) (hnodes' : Function.Injective nodes')
    (hpos : ∀ i, 0 < (nodes i).re) (hpos' : ∀ i, 0 < (nodes' i).re)
    (m : Fin r → ℕ) (m' : Fin s → ℕ) (e : LaplaceJetIndex m → LaplaceJetIndex m')
    (heNode : ∀ p, nodes' (e p).1 = nodes p.1) (heOrder : ∀ p, (e p).2.val = p.2.val)
    (f : CausalProbeL2) : dualJetBound nodes hpos m f ≤ dualJetBound nodes' hpos' m' f := by
  rw [dualJetBound_eq_norm_sq nodes hnodes hpos m f,
    dualJetBound_eq_norm_sq nodes' hnodes' hpos' m' f]
  exact dualJetProjection_norm_sq_mono nodes nodes' hpos hpos' m m'
    (dualJetSpace_le_of_embedding nodes nodes' hpos hpos' m m' e heNode heOrder) f

theorem dualActualZero_kernel_moment (rho : zetaZeroConfig.carrier)
    (hright : (1 / 2 : ℝ) < (rho : ℂ).re) (k : ℕ) (hk : k < zeroMult (rho : ℂ)) :
    CCM.nativeCompletionKernelLaplaceMoment 0 ((rho : ℂ) - 1 / 2) k = 0 := by
  have hw : 0 < ((rho : ℂ) - 1 / 2).re := by simp only [Complex.sub_re]; norm_num; linarith
  have hord := ExceptionalZero.nativeActualKernelLaplace_order_of_zero 0 (le_rfl) rho
    ((rho : ℂ) - 1 / 2) hw (by simp)
  exact CCM.nativeCompletionKernelLaplaceMoment_vanishes_below_analyticOrder 0 (le_rfl)
    ((rho : ℂ) - 1 / 2) hw (zeroMult (rho : ℂ)) (le_of_eq hord.symm) k hk

theorem dualActualZero_mem_adjointKernel (rho : zetaZeroConfig.carrier)
    (hright : (1 / 2 : ℝ) < (rho : ℂ).re) (k : ℕ) (hk : k < zeroMult (rho : ℂ)) :
    CCM.nativeDampedCompletionCausalL2Adjoint 0 (le_rfl)
      (CCM.nativeCausalExponentialWitness ((rho : ℂ) - 1 / 2)
        (by simp only [Complex.sub_re]; norm_num; linarith) k) = 0 := by
  apply CCM.nativeCausalExponentialWitness_mem_adjointKernel_of_kernel_moments 0 (le_rfl)
    ((rho : ℂ) - 1 / 2) (by simp only [Complex.sub_re]; norm_num; linarith) k
  intro j hj
  exact dualActualZero_kernel_moment rho hright j (by omega)

theorem dualZeroSpace_le_adjointKernel {r : ℕ} (rho : Fin r → zetaZeroConfig.carrier)
    (hright : ∀ i, (1 / 2 : ℝ) < (rho i : ℂ).re) (m : Fin r → ℕ)
    (hallow : ∀ i, m i ≤ zeroMult (rho i : ℂ)) :
    dualJetSpace (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m ≤
      (CCM.nativeDampedCompletionCausalL2Adjoint 0 (le_rfl)).ker := by
  rintro g ⟨x, rfl⟩
  change CCM.nativeDampedCompletionCausalL2Adjoint 0 (le_rfl)
    (∑ p : LaplaceJetIndex m, x p • laplaceJetWitness (dualZeroNodes rho)
      (dualZeroNodes_positive rho hright) m p) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro p _
  rw [map_smul]
  have hz := dualActualZero_mem_adjointKernel (rho p.1) (hright p.1) p.2.val
    (Nat.lt_of_lt_of_le p.2.isLt (hallow p.1))
  change x p • CCM.nativeDampedCompletionCausalL2Adjoint 0 (le_rfl)
    (CCM.nativeCausalExponentialWitness ((rho p.1 : ℂ) - 1 / 2) _ p.2.val) = 0
  rw [hz, smul_zero]


theorem simultaneous_zero_distance {r : ℕ} (rho : Fin r → zetaZeroConfig.carrier)
    (hdistinct : Function.Injective (fun i => (rho i : ℂ)))
    (hright : ∀ i, (1 / 2 : ℝ) < (rho i : ℂ).re) (m : Fin r → ℕ)
    (hm : ∀ i, 1 ≤ m i) (hallow : ∀ i, m i ≤ zeroMult (rho i : ℂ)) :
    (dualJetSpace (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m ≤
      (CCM.nativeDampedCompletionCausalL2Adjoint 0 (le_rfl)).ker) ∧
    (∀ p : LaplaceJetIndex m,
      dualJetPairings (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m probeTarget p =
        (-1 : ℂ) ^ p.2.val * iteratedDeriv p.2.val (probeLaplace probeV) (dualZeroNodes rho p.1)) ∧
    (0 ≤ dualJetBound (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m probeTarget) ∧
    (star (dualJetPairings (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m probeTarget) ⬝ᵥ
      ((laplaceJetGram (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m)⁻¹ *ᵥ
        dualJetPairings (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m probeTarget) ≤
      ((Metric.infDist probeTarget (closure (Set.range probeOperator)) ^ 2 : ℝ) : ℂ)) ∧
    (∀ (s : ℕ) (rho' : Fin s → zetaZeroConfig.carrier)
      (hdistinct' : Function.Injective (fun i => (rho' i : ℂ)))
      (hright' : ∀ i, (1 / 2 : ℝ) < (rho' i : ℂ).re) (m' : Fin s → ℕ)
      (hm' : ∀ i, 1 ≤ m' i) (hallow' : ∀ i, m' i ≤ zeroMult (rho' i : ℂ))
      (e : LaplaceJetIndex m → LaplaceJetIndex m') (he : Function.Injective e)
      (heNode : ∀ p, dualZeroNodes rho' (e p).1 = dualZeroNodes rho p.1)
      (heOrder : ∀ p, (e p).2.val = p.2.val),
      dualJetBound (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m probeTarget ≤
        dualJetBound (dualZeroNodes rho') (dualZeroNodes_positive rho' hright') m' probeTarget ∧
      dualJetBound (dualZeroNodes rho') (dualZeroNodes_positive rho' hright') m' probeTarget ≤
        Metric.infDist probeTarget (closure (Set.range probeOperator)) ^ 2) := by
  refine ⟨dualZeroSpace_le_adjointKernel rho hright m hallow,
    dualJetPairings_target_derivative _ _ _, ?_,
    dualZeroBound_complex_distance rho hdistinct hright m hallow, ?_⟩
  · rw [dualJetBound_eq_norm_sq _ (dualZeroNodes_injective rho hdistinct)]
    exact sq_nonneg _
  · intro s rho' hdistinct' hright' m' hm' hallow' e he heNode heOrder
    constructor
    · exact dualJetBound_mono_of_embedding _ _ (dualZeroNodes_injective rho hdistinct)
        (dualZeroNodes_injective rho' hdistinct') _ _ m m' e heNode heOrder probeTarget
    · exact dualZeroBound_distance rho' hdistinct' hright' m' hallow'


theorem dualSingleCauchyDet (a : ℂ) (n : ℕ) :
    laplaceJetCauchyDeterminant (fun _ : Fin 1 => a) (fun _ => n) =
      (∏ k : Fin n, (k.val.factorial : ℝ) ^ 2) / (2 * a.re) ^ (n ^ 2) := by
  simp [laplaceJetCauchyDeterminant, Fin.prod_univ_succ]

theorem dualSingleCauchyRatio (a : ℂ) (ha : 0 < a.re) (n : ℕ) :
    laplaceJetCauchyDeterminant (fun _ : Fin 1 => a) (fun _ => n) /
      laplaceJetCauchyDeterminant (fun _ : Fin 1 => a) (fun _ => n + 1) =
        (2 * a.re) ^ (2 * n + 1) / (n.factorial : ℝ) ^ 2 := by
  rw [dualSingleCauchyDet, dualSingleCauchyDet, Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have hA : (∏ k : Fin n, (k.val.factorial : ℝ) ^ 2) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.2
    intro k _
    exact pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero k.val)
  have hc : (2 * a.re) ≠ 0 := ne_of_gt (by linarith : 0 < 2 * a.re)
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [show (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) by ring, pow_add]
  field_simp [hA, hc, hf] <;> ring

theorem dualSingleNativeGram_ratio (a : ℂ) (ha : 0 < a.re) (n : ℕ) :
    (laplaceJetGram (fun _ : Fin 1 => a) (fun _ => ha) (fun _ => n)).det /
      (laplaceJetGram (fun _ : Fin 1 => a) (fun _ => ha) (fun _ => n + 1)).det =
        (((2 * a.re) ^ (2 * n + 1) / (n.factorial : ℝ) ^ 2 : ℝ) : ℂ) := by
  have hinj : Function.Injective (fun _ : Fin 1 => a) := fun _ _ _ => Subsingleton.elim _ _
  rw [laplaceJetGram_confluent_determinant _ hinj, laplaceJetGram_confluent_determinant _ hinj,
    ← Complex.ofReal_div, dualSingleCauchyRatio a ha n]

/-- This is a reuse/normalization comparison with the existing literal
Laguerre tail, not a new obstruction theorem or an inverse-entry premise. -/
theorem dualSingleNativeGram_ratio_laguerre (a : ℂ) (ha : 0 < a.re) (n : ℕ) :
    (laplaceJetGram (fun _ : Fin 1 => a) (fun _ => ha) (fun _ => n)).det /
      (laplaceJetGram (fun _ : Fin 1 => a) (fun _ => ha) (fun _ => n + 1)).det =
        (((‖OPICAFollowup.monicLaguerreTailL2 n a 0 ha‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hL := (OPICAFollowup.laguerre_tail_norm (n + 1) (by omega) a ha 0).2.2.2.2.1
  have hn : ‖OPICAFollowup.monicLaguerreTailL2 n a 0 ha‖ ^ 2 =
      (n.factorial : ℝ) ^ 2 / (2 * a.re) ^ (2 * n + 1) := by simpa using hL
  rw [dualSingleNativeGram_ratio a ha n, hn, _root_.inv_div]


end Zeta23.OPICARound2
