import Zeta23.CCM.CanonicalSourceMomentJets
import Mathlib.LinearAlgebra.Vandermonde

noncomputable section

namespace Zeta23.CCM

open Matrix Finset Module
open scoped BigOperators ComplexConjugate

/-!
# POST284-M15: full finite source-moment hierarchy

The compiled endpoint-jet theorem
`iteratedDeriv_odd_sourceAtomRealEnergy_eq_moment_normSq_of_prefix`
(`CanonicalSourceMomentJets`) gives `e^(2r+1)(0) = 2 (-(2π)^2)^r |M_r|^2`
whenever `M_k = 0` for every `k < r`.  This module adds the complex Vandermonde
filtration that controls which `r` can occur:

* the centered moments `M_0, …, M_{2K}` separate points of `ℂ^(2K+1)`
  (complex Vandermonde on the distinct nodes `-K, …, K`);
* the moment filtration `F_r = {M_0 = ⋯ = M_{r-1} = 0}` has complex
  codimension exactly `r` for `r ≤ 2K+1`, and `F_{2K+1} = 0`;
* on `F_r` the first surviving endpoint jet is the rank-one form
  `2 (-(2π)^2)^r |M_r|^2`;
* on the even boundary-flat carrier the first surviving order is
  `4j+1` with `2 ≤ j ≤ K` and the jet is strictly positive; on the odd
  carrier it is `4j+3` with `1 ≤ j ≤ K-1` and the jet is strictly negative.

The first surviving order depends on the fixed vector; nothing here is a
uniform semidefinite statement, and nothing applies to aperture-dependent
vectors (see the moving-vector controls in the post-284 falsifier suite).
-/

/-! ## Vandermonde separation -/

/-- The centered moments of order `≤ 2K` separate points (complex Vandermonde
on the distinct centered nodes). -/
theorem eq_zero_of_centeredMoment_eq_zero {K : ℕ} {u : Fin (2 * K + 1) → ℂ}
    (h : ∀ k : ℕ, k ≤ 2 * K → centeredMoment K k u = 0) : u = 0 := by
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
    (f := fun i => ((centeredIndex K i : ℤ) : ℂ))
  · intro i j hij
    exact centeredIndex_injective K (Int.cast_injective hij)
  · intro i
    have hi := i.2
    have hk := h i (by omega)
    unfold centeredMoment at hk
    rw [← hk]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- A nonzero centered vector has a first surviving moment of order `≤ 2K`. -/
theorem exists_first_nonzero_centeredMoment {K : ℕ} {u : Fin (2 * K + 1) → ℂ}
    (hu : u ≠ 0) :
    ∃ r : ℕ, r ≤ 2 * K ∧ centeredMoment K r u ≠ 0 ∧
      ∀ k : ℕ, k < r → centeredMoment K k u = 0 := by
  classical
  have hex : ∃ r, centeredMoment K r u ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (eq_zero_of_centeredMoment_eq_zero (fun k _ => h k))
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, fun k hk => ?_⟩
  · by_contra hlt
    push Not at hlt
    apply hu
    apply eq_zero_of_centeredMoment_eq_zero
    intro k hk
    exact not_not.mp (Nat.find_min hex (by omega))
  · exact not_not.mp (Nat.find_min hex hk)

/-- Every even centered moment vanishes on the odd reversal sector. -/
theorem centeredMoment_even_eq_zero_of_odd
    {K k : ℕ} {u : Fin (2 * K + 1) → ℂ}
    (hu : u ∈ oddCoefficientSubspace K) (hk : Even k) :
    centeredMoment K k u = 0 := by
  have hodd : reverseCoefficients K u = -u :=
    (mem_oddCoefficientSubspace_iff K u).mp hu
  have hrev := centeredMoment_reverseCoefficients K k u
  have hneg : centeredMoment K k (-u) = -centeredMoment K k u := by
    simp [centeredMoment, Finset.sum_neg_distrib]
  rw [hodd, hk.neg_one_pow, one_mul, hneg] at hrev
  have htwo : (2 : ℂ) * centeredMoment K k u = 0 := by
    linear_combination -hrev
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-! ## The moment filtration -/

/-- Prefix moment map `u ↦ (M_0 u, …, M_{r-1} u)`. -/
def momentPrefixMap (K r : ℕ) : (Fin (2 * K + 1) → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
  LinearMap.pi fun k => centeredMomentLinearMap K k

@[simp] theorem momentPrefixMap_apply (K r : ℕ) (u : Fin (2 * K + 1) → ℂ) (k : Fin r) :
    momentPrefixMap K r u k = centeredMoment K k u := rfl

/-- Moment filtration `F_r = {M_0 = ⋯ = M_{r-1} = 0}`. -/
def momentFiltration (K r : ℕ) : Submodule ℂ (Fin (2 * K + 1) → ℂ) :=
  LinearMap.ker (momentPrefixMap K r)

theorem mem_momentFiltration_iff (K r : ℕ) (u : Fin (2 * K + 1) → ℂ) :
    u ∈ momentFiltration K r ↔ ∀ k : ℕ, k < r → centeredMoment K k u = 0 := by
  constructor
  · intro hu k hk
    have := congrFun (LinearMap.mem_ker.mp hu) ⟨k, hk⟩
    simpa using this
  · intro hu
    apply LinearMap.mem_ker.mpr
    funext k
    exact hu k k.2

theorem momentFiltration_antitone (K : ℕ) {r s : ℕ} (h : r ≤ s) :
    momentFiltration K s ≤ momentFiltration K r := by
  intro u hu
  rw [mem_momentFiltration_iff] at hu ⊢
  exact fun k hk => hu k (by omega)

/-- The top filtration step is zero. -/
theorem momentFiltration_top_eq_bot (K : ℕ) :
    momentFiltration K (2 * K + 1) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro u hu
  rw [mem_momentFiltration_iff] at hu
  exact eq_zero_of_centeredMoment_eq_zero (fun k hk => hu k (by omega))

/-- Transposed centered Vandermonde matrix `V k i = (centeredIndex i)^k`. -/
def centeredMomentMatrix (K : ℕ) : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  (Matrix.vandermonde fun i => ((centeredIndex K i : ℤ) : ℂ))ᵀ

theorem centeredMomentMatrix_mulVec (K : ℕ) (u : Fin (2 * K + 1) → ℂ)
    (k : Fin (2 * K + 1)) :
    (centeredMomentMatrix K *ᵥ u) k = centeredMoment K k u := by
  simp [centeredMomentMatrix, Matrix.mulVec, dotProduct, centeredMoment,
    Matrix.vandermonde_apply]

theorem centeredMomentMatrix_det_ne_zero (K : ℕ) :
    (centeredMomentMatrix K).det ≠ 0 := by
  rw [centeredMomentMatrix, Matrix.det_transpose]
  apply Matrix.det_vandermonde_ne_zero_iff.mpr
  intro i j hij
  exact centeredIndex_injective K (Int.cast_injective hij)

/-- The prefix moment map is surjective for `r ≤ 2K+1`. -/
theorem momentPrefixMap_surjective (K r : ℕ) (hr : r ≤ 2 * K + 1) :
    Function.Surjective (momentPrefixMap K r) := by
  intro y
  let y' : Fin (2 * K + 1) → ℂ := fun k => if h : (k : ℕ) < r then y ⟨k, h⟩ else 0
  have hdet : IsUnit (centeredMomentMatrix K).det :=
    isUnit_iff_ne_zero.mpr (centeredMomentMatrix_det_ne_zero K)
  refine ⟨(centeredMomentMatrix K)⁻¹ *ᵥ y', ?_⟩
  funext k
  have hk : (k : ℕ) < 2 * K + 1 := by omega
  have := centeredMomentMatrix_mulVec K ((centeredMomentMatrix K)⁻¹ *ᵥ y') ⟨k, hk⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at this
  rw [momentPrefixMap_apply]
  rw [← this]
  simp [y']

/-- Exact complex codimension of the moment filtration. -/
theorem finrank_momentFiltration (K r : ℕ) (hr : r ≤ 2 * K + 1) :
    finrank ℂ (momentFiltration K r) = 2 * K + 1 - r := by
  have h := LinearMap.finrank_range_add_finrank_ker (momentPrefixMap K r)
  rw [LinearMap.range_eq_top.mpr (momentPrefixMap_surjective K r hr),
    finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
  unfold momentFiltration
  omega

/-- Successive filtration quotients have dimension exactly one below the top. -/
theorem finrank_momentFiltration_succ (K r : ℕ) (hr : r < 2 * K + 1) :
    finrank ℂ (momentFiltration K r) =
      finrank ℂ (momentFiltration K (r + 1)) + 1 := by
  rw [finrank_momentFiltration K r hr.le, finrank_momentFiltration K (r + 1) hr]
  omega

/-! ## Leading endpoint jets on the filtration -/

/-- Below the first surviving moment every endpoint jet vanishes. -/
theorem iteratedDeriv_sourceAtomRealEnergy_eq_zero_below
    (K r : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hprefix : ∀ k : ℕ, k < r →
      centeredMoment K k ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) = 0) :
    ∀ j : ℕ, j < 2 * r + 1 → iteratedDeriv j (sourceAtomRealEnergy K x) 0 = 0 := by
  intro j hj
  rcases Nat.even_or_odd j with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [show i + i = 2 * i by ring]
    exact iteratedDeriv_even_sourceAtomRealEnergy_zero K x i
  · have hi : i < r := by omega
    rw [iteratedDeriv_odd_sourceAtomRealEnergy_eq_moment_normSq_of_prefix K i x
      (fun k hk => hprefix k (by omega)), hprefix i hi]
    simp

/-- On `F_r` the `(2r+1)`-st endpoint jet is the rank-one form
`2 (-(2π)^2)^r |M_r|^2`, and all lower jets vanish. -/
theorem sourceAtomRealEnergy_jet_on_momentFiltration
    (K r : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hx : (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x ∈ momentFiltration K r) :
    (∀ j : ℕ, j < 2 * r + 1 → iteratedDeriv j (sourceAtomRealEnergy K x) 0 = 0) ∧
      iteratedDeriv (2 * r + 1) (sourceAtomRealEnergy K x) 0 =
        2 * (-(2 * Real.pi) ^ 2) ^ r *
          Complex.normSq
            (centeredMoment K r ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) := by
  rw [mem_momentFiltration_iff] at hx
  exact ⟨iteratedDeriv_sourceAtomRealEnergy_eq_zero_below K r x hx,
    iteratedDeriv_odd_sourceAtomRealEnergy_eq_moment_normSq_of_prefix K r x hx⟩

theorem euclideanEquiv_ne_zero {K : ℕ} {x : EuclideanSpace ℂ (Fin (2 * K + 1))}
    (hx : x ≠ 0) : (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x ≠ 0 := by
  intro h
  apply hx
  have := congrArg (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ).symm h
  simpa using this

/-- **Even carrier first-jet theorem.**  A nonzero even boundary-flat vector
has first surviving endpoint jet of order `4j+1` with `2 ≤ j ≤ K`, equal to
`2 (2π)^(4j) |M_(2j)|^2 > 0`. -/
theorem sourceAtomRealEnergy_first_jet_even_carrier
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hx : x ∈ euclideanEvenBoundaryFlatSubspace K) (hx0 : x ≠ 0) :
    ∃ j : ℕ, 2 ≤ j ∧ j ≤ K ∧
      (∀ i : ℕ, i < 4 * j + 1 → iteratedDeriv i (sourceAtomRealEnergy K x) 0 = 0) ∧
      iteratedDeriv (4 * j + 1) (sourceAtomRealEnergy K x) 0 =
        2 * (2 * Real.pi) ^ (4 * j) *
          Complex.normSq
            (centeredMoment K (2 * j) ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) ∧
      0 < iteratedDeriv (4 * j + 1) (sourceAtomRealEnergy K x) 0 := by
  set u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x with hu_def
  have hmem : u ∈ evenBoundaryFlatSubspace K :=
    (mem_euclideanEvenBoundaryFlatSubspace_iff K x).mp hx
  obtain ⟨hflat, heven⟩ := hmem
  replace hflat := (mem_boundaryFlatSubspace_iff K u).mp hflat
  obtain ⟨r, hr, hne, hpre⟩ := exists_first_nonzero_centeredMoment (euclideanEquiv_ne_zero hx0)
  have hr_even : Even r := by
    by_contra h
    exact hne (centeredMoment_odd_eq_zero_of_even heven (Nat.not_even_iff_odd.mp h))
  obtain ⟨j, rfl⟩ := hr_even
  have hr0 : j + j ≠ 0 := by
    intro h
    rw [h] at hne
    exact hne hflat.1
  have hr2 : j + j ≠ 2 := by
    intro h
    rw [h] at hne
    exact hne hflat.2.2
  have hj2 : 2 ≤ j := by omega
  have hjK : j ≤ K := by omega
  have hval := iteratedDeriv_odd_sourceAtomRealEnergy_eq_moment_normSq_of_prefix K (j + j) x hpre
  have hpow : (-(2 * Real.pi) ^ 2) ^ (j + j) = (2 * Real.pi) ^ (4 * j) := by
    rw [show j + j = 2 * j by ring, pow_mul, neg_sq, ← pow_mul, ← pow_mul]
    ring_nf
  have hval' : iteratedDeriv (4 * j + 1) (sourceAtomRealEnergy K x) 0 =
      2 * (2 * Real.pi) ^ (4 * j) * Complex.normSq (centeredMoment K (2 * j) u) := by
    rw [show 4 * j + 1 = 2 * (j + j) + 1 by ring, hval, hpow, show 2 * j = j + j by ring]
  refine ⟨j, hj2, hjK, ?_, hval', ?_⟩
  · intro i hi
    exact iteratedDeriv_sourceAtomRealEnergy_eq_zero_below K (j + j) x hpre i (by omega)
  · rw [hval']
    have hpi : 0 < (2 * Real.pi) ^ (4 * j) := pow_pos (by positivity) _
    have hns : 0 < Complex.normSq (centeredMoment K (2 * j) u) := by
      apply Complex.normSq_pos.mpr
      rw [show 2 * j = j + j by ring]
      exact hne
    positivity

/-- **Odd carrier first-jet theorem.**  A nonzero odd boundary-flat vector has
first surviving endpoint jet of order `4j+3` with `1 ≤ j ≤ K-1`, equal to
`-2 (2π)^(4j+2) |M_(2j+1)|^2 < 0`. -/
theorem sourceAtomRealEnergy_first_jet_odd_carrier
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hx : x ∈ euclideanOddBoundaryFlatSubspace K) (hx0 : x ≠ 0) :
    ∃ j : ℕ, 1 ≤ j ∧ j + 1 ≤ K ∧
      (∀ i : ℕ, i < 4 * j + 3 → iteratedDeriv i (sourceAtomRealEnergy K x) 0 = 0) ∧
      iteratedDeriv (4 * j + 3) (sourceAtomRealEnergy K x) 0 =
        -(2 * (2 * Real.pi) ^ (4 * j + 2) *
          Complex.normSq
            (centeredMoment K (2 * j + 1)
              ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))) ∧
      iteratedDeriv (4 * j + 3) (sourceAtomRealEnergy K x) 0 < 0 := by
  set u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x with hu_def
  have hmem : u ∈ oddBoundaryFlatSubspace K :=
    (mem_euclideanOddBoundaryFlatSubspace_iff K x).mp hx
  obtain ⟨hflat, hodd⟩ := hmem
  replace hflat := (mem_boundaryFlatSubspace_iff K u).mp hflat
  obtain ⟨r, hr, hne, hpre⟩ := exists_first_nonzero_centeredMoment (euclideanEquiv_ne_zero hx0)
  have hr_odd : Odd r := by
    by_contra h
    exact hne (centeredMoment_even_eq_zero_of_odd hodd (Nat.not_odd_iff_even.mp h))
  obtain ⟨j, rfl⟩ := hr_odd
  have hr1 : 2 * j + 1 ≠ 1 := by
    intro h
    rw [h] at hne
    exact hne hflat.2.1
  have hj1 : 1 ≤ j := by omega
  have hjK : j + 1 ≤ K := by omega
  have hval :=
    iteratedDeriv_odd_sourceAtomRealEnergy_eq_moment_normSq_of_prefix K (2 * j + 1) x hpre
  have hpow : (-(2 * Real.pi) ^ 2) ^ (2 * j + 1) = -(2 * Real.pi) ^ (4 * j + 2) := by
    rw [pow_succ, pow_mul, neg_sq, ← pow_mul, ← pow_mul]
    ring_nf
  have hval' : iteratedDeriv (4 * j + 3) (sourceAtomRealEnergy K x) 0 =
      -(2 * (2 * Real.pi) ^ (4 * j + 2) *
        Complex.normSq (centeredMoment K (2 * j + 1) u)) := by
    rw [show 4 * j + 3 = 2 * (2 * j + 1) + 1 by ring, hval, hpow]
    ring
  refine ⟨j, hj1, hjK, ?_, hval', ?_⟩
  · intro i hi
    exact iteratedDeriv_sourceAtomRealEnergy_eq_zero_below K (2 * j + 1) x hpre i (by omega)
  · rw [hval', neg_lt_zero]
    have hpi : 0 < (2 * Real.pi) ^ (4 * j + 2) := pow_pos (by positivity) _
    have hns : 0 < Complex.normSq (centeredMoment K (2 * j + 1) u) :=
      Complex.normSq_pos.mpr hne
    positivity

end Zeta23.CCM

#print axioms Zeta23.CCM.eq_zero_of_centeredMoment_eq_zero
#print axioms Zeta23.CCM.exists_first_nonzero_centeredMoment
#print axioms Zeta23.CCM.centeredMoment_even_eq_zero_of_odd
#print axioms Zeta23.CCM.momentFiltration_top_eq_bot
#print axioms Zeta23.CCM.finrank_momentFiltration
#print axioms Zeta23.CCM.finrank_momentFiltration_succ
#print axioms Zeta23.CCM.sourceAtomRealEnergy_jet_on_momentFiltration
#print axioms Zeta23.CCM.sourceAtomRealEnergy_first_jet_even_carrier
#print axioms Zeta23.CCM.sourceAtomRealEnergy_first_jet_odd_carrier
