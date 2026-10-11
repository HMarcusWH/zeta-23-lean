import Zeta23.CCM.WeightedRemainderIdentity
import Zeta23.CCM.CanonicalRecentPrimeSecondVariation
import Zeta23.CCM.CanonicalPrimeFreeSecondTest

noncomputable section

namespace Zeta23.CCM

open Matrix Finset
open scoped BigOperators ComplexConjugate ArithmeticFunction

/-!
# POST284 follow-up M50: older-prime budget at a stationary contact (Step 91)

At a stationary generated strict-even contact `c` (aperture `L = L*`, cutoff `K`,
normalized even kernel vector `z`, stationary response `w`, response cost
`C = ⟪A w, w⟫ ≥ 0`), the test `h(t) = t² e_{Dz}(1 - t/L)` splits as

`P - ∑_{2 ≤ q ≤ e^L} β_q e_{Dz}(ω_q) = -(2 L⁴/(2π)²) C`,

with the pole/archimedean part `P = ∫₀ᴸ h (e^{-t/2} + e^{t/2}) - ∫₀ᴸ h ρ`,
`β_q = Λ(q)(log q)²/√q` and `ω_q = 1 - log q / L ∈ [0, 1]`.  This is the M09
balance.  F04 enters only there, through the proved production-derivative transport
at every `L > 0` (`secondPhysicalValue_eq_two_mul_responseCost`), so no F04
hypothesis remains in the statements below.  Split the samples at any `θ` inside the M49 contact
angle `(2πθ)² A_K |H(z)| · 2 ≤ 5 λ_odd`: near `N = {ω_q ≤ θ}`, older `O = {ω_q > θ}`.
Then, with `b = (π⁶/90)(λ_odd/(4|H(z)|))²`,

* (91.1) `∑_O β_q e_{Dz}(ω_q) ≥ P + (2L⁴/(2π)²) C + b ∑_N β_q ω_q⁷`;
* (91.2) `P + (2L⁴/(2π)²) C + b ∑_N β_q ω_q⁷ ≤ 2(2K+1)K² ∑_O β_q ω_q`,

the latter from the prime-free size bound `|Re e_{Dz}(ω)| ≤ 2ω(2K+1)K²‖z‖²`.  Every
active sample has `0 ≤ ω_q ≤ 1` (`primeSourceCoordinate_mem_of_mem_Icc`), including an
endpoint sample `q = e^L` with `ω_q = 0`; for `θ ≥ 0` it lies in `N` and contributes
`0` to both sides.

These are **necessary conditions** satisfied by every stationary generated
contact.  They exclude nothing: `P` may be negative, the older set may be
nonempty, and no lower bound for `P` or upper bound for the adverse older
terms is proved (M51 stays OPEN).
-/

/-! ## Pole/archimedean part and prime samples -/

/-- The pole-minus-archimedean part `P_L[f]` of the production value. -/
def productionPoleArchValue (L : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..L, f x * completeSourcePoleWeight x) -
    ∫ x in (0 : ℝ)..L, f x * archDensity x

/-- `A_L[f] = P_L[f] - ∑_{2 ≤ q ≤ e^L} Λ(q)/√q f(log q)` for real tests. -/
theorem productionArithmeticRealValue_eq_poleArch_sub_primes (L : ℝ) (f : ℝ → ℝ) :
    productionArithmeticRealValue L f =
      productionPoleArchValue L f -
        ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, Λ q / Real.sqrt q * f (Real.log q) := by
  unfold productionArithmeticRealValue productionArithmeticComplexValue
    dictionaryCompletePhysicalRHS productionPoleArchValue
  have h1 : ∀ w : ℝ → ℝ, (∫ x in (0 : ℝ)..L, (f x : ℂ) * (w x : ℂ)) =
      ((∫ x in (0 : ℝ)..L, f x * w x : ℝ) : ℂ) := by
    intro w
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun x _ => ?_
    push_cast
    ring
  rw [h1 completeSourcePoleWeight, h1 archDensity, Complex.sub_re, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_re, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [primeSourceWeight]

/-- The prime-sample weight `β_q = Λ(q)(log q)²/√q`. -/
def contactPrimeWeight (q : ℕ) : ℝ :=
  Λ q / Real.sqrt q * Real.log q ^ 2

theorem contactPrimeWeight_nonneg (q : ℕ) : 0 ≤ contactPrimeWeight q := by
  unfold contactPrimeWeight
  have := ArithmeticFunction.vonMangoldt_nonneg (n := q)
  positivity

/-- Every active sample has source coordinate `ω_q = 1 - log q / L ∈ [0, 1]`. -/
theorem primeSourceCoordinate_mem_of_mem_Icc {L : ℝ} (hL : 0 < L) {q : ℕ}
    (hq : q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊) :
    0 ≤ primeSourceCoordinate q L ∧ primeSourceCoordinate q L ≤ 1 := by
  obtain ⟨hq2, hqL⟩ := Finset.mem_Icc.mp hq
  have hq2' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq0 : (0 : ℝ) < q := by linarith
  have hqe : (q : ℝ) ≤ Real.exp L :=
    le_trans (by exact_mod_cast hqL) (Nat.floor_le (Real.exp_pos L).le)
  have hlog : Real.log q ≤ L := by
    rw [Real.log_le_iff_le_exp hq0]
    exact hqe
  have hlog0 : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  unfold primeSourceCoordinate
  constructor
  · rw [sub_nonneg, div_le_one hL]
    exact hlog
  · have : 0 ≤ Real.log q / L := div_nonneg hlog0 hL.le
    linarith

/-! ## Elementary size bound -/

/-- For a normalized legal even `z`, `e_{Dz}(ω) ≤ 2ω (2K+1) K²` at `ω ≥ 0`. -/
theorem productionContactIndexEnergy_le_of_norm_eq_one {L : ℝ} (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) (hv1 : ‖v‖ = 1) {t : ℝ}
    (hω : 0 ≤ 1 - t / L) :
    productionContactIndexEnergy L K v t ≤ 2 * (1 - t / L) * ((2 * K + 1) * K ^ 2) := by
  set ω := 1 - t / L with hωdef
  set z := evenBoundaryFlatRawCoefficients K v with hzdef
  have hE : productionContactIndexEnergy L K v t =
      (quadraticForm (sourceMatrix ω K) (indexMatrix K *ᵥ z)).re := by
    change matrixRealEnergy (sourceMatrix ω K)
      (sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))) = _
    unfold matrixRealEnergy
    congr 2
  have hz1 : ∑ i, Complex.normSq (z i) = 1 := by
    have h := EuclideanSpace.norm_sq_eq (v : EuclideanSpace ℂ (Fin (2 * K + 1)))
    have hv : ‖(v : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ = 1 := hv1
    rw [hv, one_pow] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.normSq_eq_norm_sq]
    rfl
  rw [hE]
  have h := abs_re_quadraticForm_index_le hω K z
  rw [hz1, mul_one] at h
  calc (quadraticForm (sourceMatrix ω K) (indexMatrix K *ᵥ z)).re
      ≤ |(quadraticForm (sourceMatrix ω K) (indexMatrix K *ᵥ z)).re| := le_abs_self _
    _ ≤ 2 * ω * (2 * K + 1) * K ^ 2 := h
    _ = 2 * ω * ((2 * K + 1) * K ^ 2) := by ring

/-! ## The contact budget -/

/-- Response cost `C = ⟪A w, w⟫` of the stationary response at a stationary
generated contact. -/
def GeneratedStrictEvenContact.stationaryResponseCost
    (c : GeneratedStrictEvenContact)
    (hst : productionContactFirstVariation .even c.generated.shell.Lstar
      (c.generated.shell.k + 1) c.z = 0) : ℝ :=
  productionContactResponseCost c.generated.shell.Lstar (c.generated.shell.k + 1)
    (canonicalStationaryEvenResponse c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
      c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hst)

theorem GeneratedStrictEvenContact.stationaryResponseCost_nonneg
    (c : GeneratedStrictEvenContact)
    (hst : productionContactFirstVariation .even c.generated.shell.Lstar
      (c.generated.shell.k + 1) c.z = 0) :
    0 ≤ c.stationaryResponseCost hst :=
  productionContactResponseCost_nonnegative c.evenGround_zero _

/-- **M50 sample form of the contact balance.**
`P - ∑_q β_q e_{Dz}(ω_q) = -(2 L⁴/(2π)²) C` at a stationary generated contact. -/
theorem GeneratedStrictEvenContact.poleArch_sub_primeSamples_eq
    (c : GeneratedStrictEvenContact)
    (hst : productionContactFirstVariation .even c.generated.shell.Lstar
      (c.generated.shell.k + 1) c.z = 0) :
    productionPoleArchValue c.generated.shell.Lstar
        (fun t => t ^ 2 * productionContactIndexEnergy c.generated.shell.Lstar
          (c.generated.shell.k + 1) c.z t) -
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp c.generated.shell.Lstar⌋₊,
        contactPrimeWeight q * productionContactIndexEnergy c.generated.shell.Lstar
          (c.generated.shell.k + 1) c.z (Real.log q) =
      -(2 * c.generated.shell.Lstar ^ 4 / (2 * Real.pi) ^ 2) * c.stationaryResponseCost hst := by
  have h := c.indexEnergyValue_eq_neg_responseCost hst
  rw [productionArithmeticRealValue_eq_poleArch_sub_primes] at h
  rw [GeneratedStrictEvenContact.stationaryResponseCost, ← h]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold contactPrimeWeight
  ring

/-- **M50 (91.1), older-prime dominance.**  For any split threshold `θ` inside the
M49 contact angle, the older samples carry at least
`P + (2L⁴/(2π)²) C + b ∑_N β_q ω_q⁷`, `b = (π⁶/90)(λ_odd/(4|H(z)|))²`.
A necessary condition, not an exclusion. -/
theorem GeneratedStrictEvenContact.olderPrimeBudget
    (c : GeneratedStrictEvenContact)
    (hst : productionContactFirstVariation .even c.generated.shell.Lstar
      (c.generated.shell.k + 1) c.z = 0)
    {θ : ℝ}
    (hθ : (2 * Real.pi * θ) ^ 2 *
        (sourceOddTaylorConstant (c.generated.shell.k + 1) *
          ‖explicitCanonicalSourceMoment c.generated.shell.Lstar (c.generated.shell.k + 1) c.z‖ *
            2) ≤
      5 * parityRayleighBottom .odd c.generated.shell.Lstar (c.generated.shell.k + 1)) :
    productionPoleArchValue c.generated.shell.Lstar
        (fun t => t ^ 2 * productionContactIndexEnergy c.generated.shell.Lstar
          (c.generated.shell.k + 1) c.z t) +
      2 * c.generated.shell.Lstar ^ 4 / (2 * Real.pi) ^ 2 * c.stationaryResponseCost hst +
      Real.pi ^ 6 / 90 *
          (parityRayleighBottom .odd c.generated.shell.Lstar (c.generated.shell.k + 1) /
            (4 * ‖explicitCanonicalSourceMoment c.generated.shell.Lstar
              (c.generated.shell.k + 1) c.z‖)) ^ 2 *
        ∑ q ∈ (Finset.Icc 2 ⌊Real.exp c.generated.shell.Lstar⌋₊).filter
            (fun q => primeSourceCoordinate q c.generated.shell.Lstar ≤ θ),
          contactPrimeWeight q * primeSourceCoordinate q c.generated.shell.Lstar ^ 7 ≤
      ∑ q ∈ (Finset.Icc 2 ⌊Real.exp c.generated.shell.Lstar⌋₊).filter
          (fun q => ¬ primeSourceCoordinate q c.generated.shell.Lstar ≤ θ),
        contactPrimeWeight q * productionContactIndexEnergy c.generated.shell.Lstar
          (c.generated.shell.k + 1) c.z (Real.log q) := by
  set L := c.generated.shell.Lstar with hLdef
  set K := c.generated.shell.k + 1 with hKdef
  have hL : 0 < L := c.Lstar_pos
  set S := Finset.Icc 2 ⌊Real.exp L⌋₊ with hSdef
  set e : ℕ → ℝ := fun q => productionContactIndexEnergy L K c.z (Real.log q) with hedef
  set b := Real.pi ^ 6 / 90 *
    (parityRayleighBottom .odd L K / (4 * ‖explicitCanonicalSourceMoment L K c.z‖)) ^ 2 with hbdef
  have hbal := c.poleArch_sub_primeSamples_eq hst
  rw [← Finset.sum_filter_add_sum_filter_not S
    (fun q => primeSourceCoordinate q L ≤ θ)] at hbal
  -- near samples: β_q e(ω_q) ≤ -b β_q ω_q⁷
  have hveig : parityCompressedCanonical .even L K c.z =
      (parityRayleighBottom .even L K : ℂ) • c.z := by
    rw [c.evenGround_zero, Complex.ofReal_zero, zero_smul]
    exact c.z_kernel
  have hδ : 0 < parityRayleighBottom .odd L K - parityRayleighBottom .even L K := by
    rw [c.evenGround_zero, sub_zero]
    exact c.odd_positive
  have hnear : ∀ q ∈ S.filter (fun q => primeSourceCoordinate q L ≤ θ),
      contactPrimeWeight q * e q ≤ -(b * (contactPrimeWeight q * primeSourceCoordinate q L ^ 7)) := by
    intro q hq
    obtain ⟨hqS, hqθ⟩ := Finset.mem_filter.mp hq
    obtain ⟨hω0, _⟩ := primeSourceCoordinate_mem_of_mem_Icc hL hqS
    have hangle : (2 * Real.pi * (1 - Real.log q / L)) ^ 2 *
        (sourceOddTaylorConstant K * ‖explicitCanonicalSourceMoment L K c.z‖ * 2) ≤
          5 * (parityRayleighBottom .odd L K - parityRayleighBottom .even L K) := by
      rw [c.evenGround_zero, sub_zero]
      have hsq : (2 * Real.pi * (1 - Real.log q / L)) ^ 2 ≤ (2 * Real.pi * θ) ^ 2 := by
        have hpi := Real.pi_pos
        unfold primeSourceCoordinate at hω0 hqθ
        exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2
      have hX : 0 ≤ sourceOddTaylorConstant K * ‖explicitCanonicalSourceMoment L K c.z‖ * 2 := by
        have := sourceOddTaylorConstant_nonneg K
        positivity
      exact le_trans (mul_le_mul_of_nonneg_right hsq hX) hθ
    have h := primeTerm_ge_of_contactAngle_four hL K c.two_le_K c.z hveig hδ c.z_norm
      (t := Real.log q) hω0 hangle (contactPrimeWeight_nonneg q)
    rw [c.evenGround_zero, sub_zero] at h
    unfold primeSourceCoordinate
    simp only [hedef, hbdef]
    nlinarith
  have hN : ∑ q ∈ S.filter (fun q => primeSourceCoordinate q L ≤ θ), contactPrimeWeight q * e q ≤
      -(b * ∑ q ∈ S.filter (fun q => primeSourceCoordinate q L ≤ θ),
        contactPrimeWeight q * primeSourceCoordinate q L ^ 7) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum hnear
  have hC := c.stationaryResponseCost_nonneg hst
  linarith

/-- **M50 (91.2), finite form.**  With `|e_{Dz}(ω)| ≤ 2ω(2K+1)K²` for the
normalized contact vector,
`P + (2L⁴/(2π)²) C + b ∑_N β_q ω_q⁷ ≤ 2(2K+1)K² ∑_O β_q ω_q`.
A necessary condition, not an exclusion. -/
theorem GeneratedStrictEvenContact.olderPrimeBudget_finite
    (c : GeneratedStrictEvenContact)
    (hst : productionContactFirstVariation .even c.generated.shell.Lstar
      (c.generated.shell.k + 1) c.z = 0)
    {θ : ℝ}
    (hθ : (2 * Real.pi * θ) ^ 2 *
        (sourceOddTaylorConstant (c.generated.shell.k + 1) *
          ‖explicitCanonicalSourceMoment c.generated.shell.Lstar (c.generated.shell.k + 1) c.z‖ *
            2) ≤
      5 * parityRayleighBottom .odd c.generated.shell.Lstar (c.generated.shell.k + 1)) :
    productionPoleArchValue c.generated.shell.Lstar
        (fun t => t ^ 2 * productionContactIndexEnergy c.generated.shell.Lstar
          (c.generated.shell.k + 1) c.z t) +
      2 * c.generated.shell.Lstar ^ 4 / (2 * Real.pi) ^ 2 * c.stationaryResponseCost hst +
      Real.pi ^ 6 / 90 *
          (parityRayleighBottom .odd c.generated.shell.Lstar (c.generated.shell.k + 1) /
            (4 * ‖explicitCanonicalSourceMoment c.generated.shell.Lstar
              (c.generated.shell.k + 1) c.z‖)) ^ 2 *
        ∑ q ∈ (Finset.Icc 2 ⌊Real.exp c.generated.shell.Lstar⌋₊).filter
            (fun q => primeSourceCoordinate q c.generated.shell.Lstar ≤ θ),
          contactPrimeWeight q * primeSourceCoordinate q c.generated.shell.Lstar ^ 7 ≤
      2 * (2 * ((c.generated.shell.k + 1 : ℕ) : ℝ) + 1) *
          ((c.generated.shell.k + 1 : ℕ) : ℝ) ^ 2 *
        ∑ q ∈ (Finset.Icc 2 ⌊Real.exp c.generated.shell.Lstar⌋₊).filter
            (fun q => ¬ primeSourceCoordinate q c.generated.shell.Lstar ≤ θ),
          contactPrimeWeight q * primeSourceCoordinate q c.generated.shell.Lstar := by
  refine (c.olderPrimeBudget hst hθ).trans ?_
  have hL : 0 < c.generated.shell.Lstar := c.Lstar_pos
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  obtain ⟨hqS, _⟩ := Finset.mem_filter.mp hq
  obtain ⟨hω0, _⟩ := primeSourceCoordinate_mem_of_mem_Icc hL hqS
  have h := productionContactIndexEnergy_le_of_norm_eq_one (L := c.generated.shell.Lstar)
    (c.generated.shell.k + 1) c.z c.z_norm (t := Real.log q) hω0
  have hβ := contactPrimeWeight_nonneg q
  have := mul_le_mul_of_nonneg_left h hβ
  unfold primeSourceCoordinate
  push_cast at this ⊢
  nlinarith

end Zeta23.CCM

#print axioms Zeta23.CCM.productionArithmeticRealValue_eq_poleArch_sub_primes
#print axioms Zeta23.CCM.contactPrimeWeight_nonneg
#print axioms Zeta23.CCM.primeSourceCoordinate_mem_of_mem_Icc
#print axioms Zeta23.CCM.productionContactIndexEnergy_le_of_norm_eq_one
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.stationaryResponseCost_nonneg
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.poleArch_sub_primeSamples_eq
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.olderPrimeBudget
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.olderPrimeBudget_finite
