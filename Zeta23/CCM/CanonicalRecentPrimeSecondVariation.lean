import Zeta23.CCM.CanonicalSourceOddEndpointQuantitative
import Zeta23.CCM.CanonicalCenteredIndexPoincare
import Zeta23.CCM.FirstCrossingProductionRemainder

noncomputable section

namespace Zeta23.CCM

open Matrix Finset
open scoped BigOperators ComplexConjugate

/-!
# POST284 follow-up M49: quantitative near-edge prime benefit (Steps 84, 90)

Let `v` be an even ground eigenvector of the actual canonical even compressed
operator at aperture `L`, with positive parity gap
`δ = λ_odd - λ_even > 0` and `‖v‖ = 1`; write `z` for its raw coefficients,
`Dz` for the centered-index image (`sourceIndexAction`), `H = explicitCanonicalSourceMoment`
and `M₄ = M₄(z)`.  Then `Dz` is legal odd with `M₃(Dz) = M₄(z)`, and the existing
parity-gap theorem `δ ‖Dz‖² ≤ |H(v)| |M₄|` together with a coercivity bound
`‖v‖² ≤ c ‖Dz‖²` (`c = C_K`, M46, or `c = 4`, M73) gives

* `|M₄| ≥ δ / (c |H(v)|)` and `|M₄| / ‖Dz‖ ≥ δ / (|H(v)| √c)`;
* for `0 ≤ ω` with `(2πω)² A_K |H(v)| √c ≤ 5δ` (the contact angle `θ_*`), M45 applies
  to `Dz`:

  `e_{Dz}(ω) ≤ -(π⁶/90) |M₄|² ω⁷ ≤ -(π⁶/90) (δ / (c |H(v)|))² ω⁷`.

At a prime-power sample `t = log q`, `ω_q = 1 - log q / L`, the physical prime
term `-β_q e_{Dz}(ω_q)` with `β_q = Λ(q)(log q)²/√q ≥ 0` is therefore at least
`(π⁶/90) β_q (δ / (c |H(v)|))² ω_q⁷`.  The plan's `B_H = ‖H‖` is replaced by the
value `|H(v)| ≤ B_H` at the actual vector, which only enlarges the angle.

Scope: these are lower bounds for individual near-edge prime terms (`0 ≤ ω_q ≤ θ_*`).
They say nothing about older primes (`ω_q > θ_*`), the pole/archimedean part `P`,
or the complete test; no contact is excluded.  The angle may contain no prime
sample at all.
-/

/-- The centered-index image of a legal even vector is legal odd. -/
theorem indexMatrix_mulVec_mem_oddBoundaryFlat {K : ℕ} {z : Fin (2 * K + 1) → ℂ}
    (hz : z ∈ evenBoundaryFlatSubspace K) :
    indexMatrix K *ᵥ z ∈ oddBoundaryFlatSubspace K :=
  (evenToOddIndexLinearMap K ⟨z, hz⟩).property

/-- `M₃(Dz) = M₄(z)`. -/
theorem centeredMoment_three_indexMatrix_mulVec (K : ℕ) (z : Fin (2 * K + 1) → ℂ) :
    centeredMoment K 3 (indexMatrix K *ᵥ z) = centeredMoment K 4 z := by
  unfold centeredMoment
  apply Finset.sum_congr rfl
  intro i _
  simp [indexMatrix, Matrix.mulVec_diagonal]
  ring

/-- `sourceIndexAction` is the Euclidean centered-index map. -/
theorem sourceIndexAction_eq_euclideanIndexLinearMap (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    sourceIndexAction K x = euclideanIndexLinearMap K x := by
  apply (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ).injective
  rw [euclideanIndexLinearMap_coordinates]
  simp only [sourceIndexAction, ContinuousLinearEquiv.apply_symm_apply]

/-- **M45 on `Dz` (even form).**  For legal even `z` and `0 ≤ ω` with
`(2πω)² B(Dz) ≤ 5 |M₄(z)|`, `Re e_{Dz}(ω) ≤ -(π⁶/90) |M₄(z)|² ω⁷`. -/
theorem re_quadraticForm_index_le_of_mem_evenBoundaryFlat
    {K : ℕ} {z : Fin (2 * K + 1) → ℂ} (hz : z ∈ evenBoundaryFlatSubspace K)
    {ω : ℝ} (hω : 0 ≤ ω)
    (hθ : (2 * Real.pi * ω) ^ 2 * sourceOddTaylorWeight K (indexMatrix K *ᵥ z) ≤
      5 * ‖centeredMoment K 4 z‖) :
    (quadraticForm (sourceMatrix ω K) (indexMatrix K *ᵥ z)).re ≤
      -(Real.pi ^ 6 / 90) * ‖centeredMoment K 4 z‖ ^ 2 * ω ^ 7 := by
  have h := re_quadraticForm_sourceMatrix_le_of_mem_oddBoundaryFlat
    (indexMatrix_mulVec_mem_oddBoundaryFlat hz) hω
    (by rw [centeredMoment_three_indexMatrix_mulVec]; exact hθ)
  rwa [centeredMoment_three_indexMatrix_mulVec] at h

/-- **M49 (generic coercivity constant).**  At an even ground eigenvector with
positive parity gap `δ`, normalized `‖v‖ = 1`, and any proved coercivity bound
`‖v‖² ≤ c ‖Dz‖²`, every source coordinate `0 ≤ ω` inside the contact angle
`(2πω)² A_K |H(v)| √c ≤ 5δ` gives
`e_{Dz}(ω) ≤ -(π⁶/90) |M₄|² ω⁷ ≤ -(π⁶/90) (δ / (c |H(v)|))² ω⁷`. -/
theorem sourceAtomRealEnergy_index_le_of_contactAngle
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hveig :
      parityCompressedCanonical .even L K v =
        (parityRayleighBottom .even L K : ℂ) • v)
    (hδ : 0 < parityRayleighBottom .odd L K - parityRayleighBottom .even L K)
    (hv1 : ‖v‖ = 1) {c : ℝ} (hc0 : 0 < c)
    (hc : ‖(v : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ ^ 2 ≤
      c * ‖euclideanIndexLinearMap K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ ^ 2)
    {ω : ℝ} (hω : 0 ≤ ω)
    (hθ : (2 * Real.pi * ω) ^ 2 *
      (sourceOddTaylorConstant K * ‖explicitCanonicalSourceMoment L K v‖ * Real.sqrt c) ≤
        5 * (parityRayleighBottom .odd L K - parityRayleighBottom .even L K)) :
    sourceAtomRealEnergy K (sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))) ω ≤
        -(Real.pi ^ 6 / 90) * ‖centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)‖ ^ 2 *
          ω ^ 7 ∧
      -(Real.pi ^ 6 / 90) * ‖centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)‖ ^ 2 *
          ω ^ 7 ≤
        -(Real.pi ^ 6 / 90) *
          ((parityRayleighBottom .odd L K - parityRayleighBottom .even L K) /
            (c * ‖explicitCanonicalSourceMoment L K v‖)) ^ 2 * ω ^ 7 := by
  set δ := parityRayleighBottom .odd L K - parityRayleighBottom .even L K with hδdef
  set z := evenBoundaryFlatRawCoefficients K v with hzdef
  set x := sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1))) with hxdef
  set h := ‖explicitCanonicalSourceMoment L K v‖ with hhdef
  set m := ‖centeredMoment K 4 z‖ with hmdef
  set A := sourceOddTaylorConstant K with hAdef
  have hpi := Real.pi_pos
  have hz : z ∈ evenBoundaryFlatSubspace K :=
    (mem_euclideanEvenBoundaryFlatSubspace_iff K _).mp v.property
  have hxe : x = euclideanIndexLinearMap K (v : EuclideanSpace ℂ (Fin (2 * K + 1))) :=
    sourceIndexAction_eq_euclideanIndexLinearMap K _
  have hux : (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x = indexMatrix K *ᵥ z := by
    rw [hxdef]
    simp only [sourceIndexAction, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  -- the parity-gap inequality in index form
  have hgapThm := parityGap_mul_evenIndex_norm_sq_le_re_star_source_mul_momentFour hL K hK v hveig
  rw [← hδdef] at hgapThm
  have hnormD : ‖euclideanEvenToOddIndexLinearMap K v‖ = ‖x‖ := by
    rw [hxe]
    rfl
  rw [hnormD] at hgapThm
  have hre : Complex.re (star (explicitCanonicalSourceMoment L K v) * centeredMoment K 4 z) ≤
      h * m := by
    calc _ ≤ ‖star (explicitCanonicalSourceMoment L K v) * centeredMoment K 4 z‖ :=
          Complex.re_le_norm _
      _ = h * m := by rw [norm_mul, norm_star]
  have hgap : δ * ‖x‖ ^ 2 ≤ h * m := hgapThm.trans hre
  -- coercivity: 1 ≤ c ‖x‖²
  have hcx : 1 ≤ c * ‖x‖ ^ 2 := by
    have hv1' : ‖(v : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ = 1 := hv1
    rw [hv1', hxe.symm] at hc
    simpa using hc
  have hx0 : 0 < ‖x‖ := by
    rcases (norm_nonneg x).eq_or_lt with h0 | h0
    · rw [← h0] at hcx; simp at hcx; linarith
    · exact h0
  have hh0 : 0 ≤ h := norm_nonneg _
  have hm0 : 0 ≤ m := norm_nonneg _
  have hδc : δ ≤ c * (h * m) := by
    have := mul_le_mul_of_nonneg_left hgap hc0.le
    nlinarith
  have hhpos : 0 < h := by
    rcases hh0.eq_or_lt with h0 | h0
    · rw [← h0] at hδc; simp at hδc; linarith
    · exact h0
  -- the M45 aperture hypothesis for `Dz`
  have hB : sourceOddTaylorWeight K (indexMatrix K *ᵥ z) ≤ A * ‖x‖ := by
    have hN : ‖x‖ = Real.sqrt (∑ i, ‖(indexMatrix K *ᵥ z) i‖ ^ 2) := by
      rw [EuclideanSpace.norm_eq x, ← hux]
      rfl
    rw [hN]
    exact sourceOddTaylorWeight_le K _
  have hA0 : 0 ≤ A := sourceOddTaylorConstant_nonneg K
  have hsc : Real.sqrt c * ‖x‖ ≥ 1 := by
    have h1 : (1 : ℝ) ≤ (Real.sqrt c * ‖x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc0.le]
      exact hcx
    have hy : 0 ≤ Real.sqrt c * ‖x‖ := by positivity
    have := (one_le_sq_iff_one_le_abs _).mp h1
    rwa [abs_of_nonneg hy] at this
  set s := (2 * Real.pi * ω) ^ 2 with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hθ' : (2 * Real.pi * ω) ^ 2 * sourceOddTaylorWeight K (indexMatrix K *ᵥ z) ≤ 5 * m := by
    -- s A ‖x‖ h ≤ s A h √c ‖x‖² ≤ 5 δ ‖x‖² ≤ 5 h m
    have step1 : s * (A * ‖x‖) * h ≤ s * (A * h * Real.sqrt c) * ‖x‖ ^ 2 := by
      have : s * (A * ‖x‖) * h * 1 ≤ s * (A * ‖x‖) * h * (Real.sqrt c * ‖x‖) :=
        mul_le_mul_of_nonneg_left hsc (by positivity)
      nlinarith
    have step2 : s * (A * h * Real.sqrt c) * ‖x‖ ^ 2 ≤ 5 * δ * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hθ (by positivity)
    have step3 : 5 * δ * ‖x‖ ^ 2 ≤ 5 * (h * m) := by linarith
    have hsAx : s * (A * ‖x‖) ≤ 5 * m := by
      have : s * (A * ‖x‖) * h ≤ 5 * m * h := by linarith
      exact le_of_mul_le_mul_right this hhpos
    calc s * sourceOddTaylorWeight K (indexMatrix K *ᵥ z) ≤ s * (A * ‖x‖) :=
          mul_le_mul_of_nonneg_left hB hs0
      _ ≤ 5 * m := hsAx
  have hmain := re_quadraticForm_index_le_of_mem_evenBoundaryFlat hz hω hθ'
  refine ⟨?_, ?_⟩
  · change (quadraticForm (sourceMatrix ω K) ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)).re ≤ _
    rw [hux]
    exact hmain
  · -- |M₄| ≥ δ / (c h)
    have hlow : δ / (c * h) ≤ m := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hδ0 : 0 ≤ δ / (c * h) := by positivity
    have hsq : (δ / (c * h)) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ hδ0 hlow 2
    have hω7 : 0 ≤ ω ^ 7 := pow_nonneg hω 7
    have hk : 0 ≤ Real.pi ^ 6 / 90 := by positivity
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hk) hω7
    linarith

/-- **M49 with the M46 constant `C_K`** (the plan's `θ_*`, with `|H(v)| ≤ B_H`). -/
theorem sourceAtomRealEnergy_index_le_of_contactAngle_coercivity
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hveig :
      parityCompressedCanonical .even L K v =
        (parityRayleighBottom .even L K : ℂ) • v)
    (hδ : 0 < parityRayleighBottom .odd L K - parityRayleighBottom .even L K)
    (hv1 : ‖v‖ = 1) {ω : ℝ} (hω : 0 ≤ ω)
    (hθ : (2 * Real.pi * ω) ^ 2 *
      (sourceOddTaylorConstant K * ‖explicitCanonicalSourceMoment L K v‖ *
        Real.sqrt (centeredCoercivityConstant K)) ≤
        5 * (parityRayleighBottom .odd L K - parityRayleighBottom .even L K)) :
    sourceAtomRealEnergy K (sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))) ω ≤
      -(Real.pi ^ 6 / 90) *
        ((parityRayleighBottom .odd L K - parityRayleighBottom .even L K) /
          (centeredCoercivityConstant K * ‖explicitCanonicalSourceMoment L K v‖)) ^ 2 * ω ^ 7 := by
  have hc0 : 0 < centeredCoercivityConstant K :=
    lt_of_lt_of_le one_pos (one_le_centeredCoercivityConstant K)
  have hflat := evenBoundaryFlatRawCoefficients_boundaryFlat K v
  have hc := norm_sq_le_centeredCoercivityConstant_mul_norm_index_sq K
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) hflat.1
  obtain ⟨h1, h2⟩ := sourceAtomRealEnergy_index_le_of_contactAngle hL K hK v hveig hδ hv1 hc0 hc
    hω hθ
  exact h1.trans h2

/-- **M49 with the M73 constant `4`.** -/
theorem sourceAtomRealEnergy_index_le_of_contactAngle_four
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hveig :
      parityCompressedCanonical .even L K v =
        (parityRayleighBottom .even L K : ℂ) • v)
    (hδ : 0 < parityRayleighBottom .odd L K - parityRayleighBottom .even L K)
    (hv1 : ‖v‖ = 1) {ω : ℝ} (hω : 0 ≤ ω)
    (hθ : (2 * Real.pi * ω) ^ 2 *
      (sourceOddTaylorConstant K * ‖explicitCanonicalSourceMoment L K v‖ * 2) ≤
        5 * (parityRayleighBottom .odd L K - parityRayleighBottom .even L K)) :
    sourceAtomRealEnergy K (sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))) ω ≤
      -(Real.pi ^ 6 / 90) *
        ((parityRayleighBottom .odd L K - parityRayleighBottom .even L K) /
          (4 * ‖explicitCanonicalSourceMoment L K v‖)) ^ 2 * ω ^ 7 := by
  have hflat := evenBoundaryFlatRawCoefficients_boundaryFlat K v
  have hc := norm_sq_le_four_mul_norm_index_sq K
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) hflat.1
  have hsqrt : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  obtain ⟨h1, h2⟩ := sourceAtomRealEnergy_index_le_of_contactAngle hL K hK v hveig hδ hv1
    (by norm_num : (0 : ℝ) < 4) hc hω (by rw [hsqrt]; exact hθ)
  exact h1.trans h2

/-- **M49 prime-term form.**  For a prime-power sample `t = log q` with
`0 ≤ ω_q = 1 - log q / L` inside the contact angle and any weight `β ≥ 0`
(the physical weight is `Λ(q)(log q)²/√q`), the physical prime term of the
actual production index energy satisfies
`-β e_{Dz}(ω_q) ≥ (π⁶/90) β (δ / (4 |H(v)|))² ω_q⁷`. -/
theorem primeTerm_ge_of_contactAngle_four
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hveig :
      parityCompressedCanonical .even L K v =
        (parityRayleighBottom .even L K : ℂ) • v)
    (hδ : 0 < parityRayleighBottom .odd L K - parityRayleighBottom .even L K)
    (hv1 : ‖v‖ = 1) {t : ℝ} (hω : 0 ≤ 1 - t / L)
    (hθ : (2 * Real.pi * (1 - t / L)) ^ 2 *
      (sourceOddTaylorConstant K * ‖explicitCanonicalSourceMoment L K v‖ * 2) ≤
        5 * (parityRayleighBottom .odd L K - parityRayleighBottom .even L K))
    {β : ℝ} (hβ : 0 ≤ β) :
    Real.pi ^ 6 / 90 * β *
        ((parityRayleighBottom .odd L K - parityRayleighBottom .even L K) /
          (4 * ‖explicitCanonicalSourceMoment L K v‖)) ^ 2 * (1 - t / L) ^ 7 ≤
      -(β * productionContactIndexEnergy L K v t) := by
  have h := sourceAtomRealEnergy_index_le_of_contactAngle_four hL K hK v hveig hδ hv1 hω hθ
  have hE : productionContactIndexEnergy L K v t =
      sourceAtomRealEnergy K (sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1))))
        (1 - t / L) := rfl
  rw [hE]
  have := mul_le_mul_of_nonneg_left h hβ
  nlinarith

end Zeta23.CCM

#print axioms Zeta23.CCM.indexMatrix_mulVec_mem_oddBoundaryFlat
#print axioms Zeta23.CCM.centeredMoment_three_indexMatrix_mulVec
#print axioms Zeta23.CCM.sourceIndexAction_eq_euclideanIndexLinearMap
#print axioms Zeta23.CCM.re_quadraticForm_index_le_of_mem_evenBoundaryFlat
#print axioms Zeta23.CCM.sourceAtomRealEnergy_index_le_of_contactAngle
#print axioms Zeta23.CCM.sourceAtomRealEnergy_index_le_of_contactAngle_coercivity
#print axioms Zeta23.CCM.sourceAtomRealEnergy_index_le_of_contactAngle_four
#print axioms Zeta23.CCM.primeTerm_ge_of_contactAngle_four
