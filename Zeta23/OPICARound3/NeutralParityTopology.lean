import Zeta23.OPICARound3.NeutralParityCover
import Zeta23.CCM.CanonicalGroundContinuity
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

namespace Zeta23.OPICARound3

open CCM Matrix Set Filter
open scoped BigOperators Topology

/-! The correction is made in the fixed legal parity carrier. Its normal
is the native, aperture-independent witness, and its denominator is proved
nonzero on the entire positive aperture axis. -/

def parityNormal (p : ReversalParity) (K : ℕ) (hK : 2 ≤ K) :
    EuclideanSpace ℂ (Fin (2 * K + 1)) :=
  match p with
  | .even => canonicalPoleEvenNonzeroWitness K hK
  | .odd => canonicalPoleOddNonzeroWitness K hK

theorem parityNormal_mem (p : ReversalParity) (K : ℕ) (hK : 2 ≤ K) :
    parityNormal p K hK ∈ euclideanParityBoundaryFlatSubspace p K := by
  cases p
  · exact (canonicalPoleEvenNonzeroWitness K hK).property
  · exact (canonicalPoleOddNonzeroWitness K hK).property

theorem parityNormal_pole_ne_zero (p : ReversalParity) {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) :
    parityPoleFunctional p L K (parityNormal p K hK) ≠ 0 := by
  cases p
  · exact canonicalPoleEvenFunctional_nonzeroWitness hL K hK
  · exact canonicalPoleOddFunctional_nonzeroWitness hL K hK

theorem continuousAt_parityPoleFunctional_apply (p : ReversalParity) (K : ℕ)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) {L : ℝ} (hL : 0 < L) :
    ContinuousAt (fun t : ℝ => parityPoleFunctional p t K u) L := by
  cases p
  · change ContinuousAt (fun t : ℝ => ∑ i, poleEvenProfile t K i * u i) L
    apply tendsto_finsetSum
    intro i _
    have hd : L ^ 2 + 16 * Real.pi ^ 2 * (centeredIndex K i : ℝ) ^ 2 ≠ 0 := by
      apply ne_of_gt
      positivity
    have hr : ContinuousAt
        (fun t : ℝ => t / (t ^ 2 + 16 * Real.pi ^ 2 * (centeredIndex K i : ℝ) ^ 2)) L :=
      continuousAt_id.div (by fun_prop) hd
    exact (Complex.continuous_ofReal.continuousAt.comp hr).mul continuousAt_const
  · change ContinuousAt (fun t : ℝ => ∑ i, poleOddProfile t K i * u i) L
    apply tendsto_finsetSum
    intro i _
    have hd : L ^ 2 + 16 * Real.pi ^ 2 * (centeredIndex K i : ℝ) ^ 2 ≠ 0 := by
      apply ne_of_gt
      positivity
    have hr : ContinuousAt
        (fun t : ℝ => (4 * Real.pi * (centeredIndex K i : ℝ)) /
          (t ^ 2 + 16 * Real.pi ^ 2 * (centeredIndex K i : ℝ) ^ 2)) L :=
      continuousAt_const.div (by fun_prop) hd
    exact (Complex.continuous_ofReal.continuousAt.comp hr).mul continuousAt_const

def neutralRepair (p : ReversalParity) (K : ℕ) (hK : 2 ≤ K)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) (L : ℝ) :
    EuclideanSpace ℂ (Fin (2 * K + 1)) :=
  u - (parityPoleFunctional p L K u /
    parityPoleFunctional p L K (parityNormal p K hK)) • parityNormal p K hK

theorem neutralRepair_mem (p : ReversalParity) (K : ℕ) (hK : 2 ≤ K)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hu : u ∈ euclideanParityBoundaryFlatSubspace p K) (L : ℝ) :
    neutralRepair p K hK u L ∈ euclideanParityBoundaryFlatSubspace p K := by
  exact (euclideanParityBoundaryFlatSubspace p K).sub_mem hu
    ((euclideanParityBoundaryFlatSubspace p K).smul_mem _ (parityNormal_mem p K hK))

theorem neutralRepair_pole (p : ReversalParity) {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    parityPoleFunctional p L K (neutralRepair p K hK u L) = 0 := by
  unfold neutralRepair
  rw [map_sub, map_smul]
  simp only [smul_eq_mul]
  rw [div_mul_cancel₀ _ (parityNormal_pole_ne_zero p hL K hK), sub_self]

theorem neutralRepair_eq_self (p : ReversalParity) (L : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hu : parityPoleFunctional p L K u = 0) : neutralRepair p K hK u L = u := by
  simp [neutralRepair, hu]

theorem continuousAt_neutralRepair (p : ReversalParity) (K : ℕ) (hK : 2 ≤ K)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) {L : ℝ} (hL : 0 < L) :
    ContinuousAt (neutralRepair p K hK u) L := by
  exact continuousAt_const.sub
    (((continuousAt_parityPoleFunctional_apply p K u hL).div
      (continuousAt_parityPoleFunctional_apply p K (parityNormal p K hK) hL)
      (parityNormal_pole_ne_zero p hL K hK)).smul continuousAt_const)

/-- Uses the complete production matrix, including its already-proved
continuity at every logarithmic prime seam. -/
theorem continuousAt_fullCanonicalEnergy (K : ℕ)
    (u : ℝ → EuclideanSpace ℂ (Fin (2 * K + 1))) {L : ℝ} (hL : 0 < L)
    (hu : ContinuousAt u L) : ContinuousAt (fun t => fullCanonicalEnergy t K (u t)) L := by
  have hA := ((continuousOn_canonicalSourceMatrix_toEuclideanCLM_Ioi K) L hL).continuousAt
    (isOpen_Ioi.mem_nhds hL)
  have h : ContinuousAt
      (fun t => inner ℂ ((Matrix.toEuclideanCLM (n := Fin (2 * K + 1)) (𝕜 := ℂ)
        (canonicalSourceMatrix t K)) (u t)) (u t)) L :=
    (hA.clm_apply hu).inner hu
  exact Complex.continuous_re.continuousAt.comp h

def NeutralParityApertures (p : ReversalParity) : Set ℝ :=
  {L | 0 < L ∧ ∃ K : ℕ, 3 ≤ K ∧ PoleNeutralParityNegative p L K}

theorem isOpen_neutralParityApertures (p : ReversalParity) :
    IsOpen (NeutralParityApertures p) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro L ⟨hL, K, hK, hneg⟩
  obtain ⟨u, hlegal, hpole, henergy⟩ := (poleNeutralParityNegative_iff_ambient p L K).mp hneg
  let hK₂ : 2 ≤ K := by omega
  let v := neutralRepair p K hK₂ u
  have hv : v L = u := neutralRepair_eq_self p L K hK₂ u hpole
  have hcont := continuousAt_fullCanonicalEnergy K v hL (continuousAt_neutralRepair p K hK₂ u hL)
  have hstrict : fullCanonicalEnergy L K (v L) < 0 := by rw [hv]; exact henergy
  have hevent : ∀ᶠ t in 𝓝 L, fullCanonicalEnergy t K (v t) < 0 :=
    hcont.tendsto.eventually (isOpen_Iio.mem_nhds hstrict)
  filter_upwards [isOpen_Ioi.mem_nhds hL, hevent] with t ht hnegative
  exact ⟨ht, K, hK, (poleNeutralParityNegative_iff_ambient p t K).mpr
    ⟨v t, neutralRepair_mem p K hK₂ u hlegal t, neutralRepair_pole p ht K hK₂ u, hnegative⟩⟩

/-- Two open cofinal sets covering a tail overlap cofinally. The tail cover
is an explicit hypothesis; separate cofinality alone cannot replace it. -/
theorem cofinal_open_overlap (U V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : ∃ T : ℝ, ∀ L : ℝ, T < L → L ∈ U ∨ L ∈ V)
    (hUcofinal : ∀ R : ℝ, ∃ L : ℝ, R < L ∧ L ∈ U)
    (hVcofinal : ∀ R : ℝ, ∃ L : ℝ, R < L ∧ L ∈ V) (R : ℝ) :
    ∃ L : ℝ, R < L ∧ L ∈ U ∩ V := by
  obtain ⟨T, hT⟩ := hcover
  obtain ⟨e, he, heU⟩ := hUcofinal (max T R)
  obtain ⟨o, ho, hoV⟩ := hVcofinal (max T R)
  have hsub : Ioi (max T R) ⊆ U ∪ V := by
    intro L hL
    exact hT L ((le_max_left T R).trans_lt hL)
  obtain ⟨L, hL, hLU, hLV⟩ := (isPreconnected_Ioi : IsPreconnected (Ioi (max T R)))
    U V hU hV hsub ⟨e, he, heU⟩ ⟨o, ho, hoV⟩
  exact ⟨L, (le_max_right T R).trans_lt hL, hLU, hLV⟩

end Zeta23.OPICARound3

#print axioms Zeta23.OPICARound3.isOpen_neutralParityApertures
#print axioms Zeta23.OPICARound3.cofinal_open_overlap
