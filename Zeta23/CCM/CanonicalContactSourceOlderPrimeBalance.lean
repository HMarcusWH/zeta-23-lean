import Zeta23.CCM.CanonicalSecularResolvent
import Zeta23.CCM.CanonicalQuadraticNormalSourceKernel
import Zeta23.CCM.CanonicalContactOlderPrimeBudget

noncomputable section

namespace Zeta23.CCM

open Matrix Finset
open scoped BigOperators ComplexConjugate ArithmeticFunction

/-!
# POST285 M59/M61: exact source-moment older-prime balance at a contact (Steps 98, 99)

At an even contact of the canonical family (`L > 0`, `K ≥ 2`, odd Rayleigh bottom
`λ_odd > 0`, `A_L z = 0`, `z ≠ 0`), write `M = M₄(z)`, `γ = γ_L > 0`,
`h_z(ω) = quadraticNormalSourceAtom K z ω` (the mixed quadratic-normal atom, not
the energy `e_{Dz}` of M45–M50), `p_z(ω) = Re(conj(M) h_z(ω))`,
`β_q = Λ(q)/√q` and `ω_q = 1 - log q / L`.  Let

`I = Re(conj(M) (∫₀ᴸ h_z(1 - t/L) (e^{-t/2} + e^{t/2}) - ∫₀ᴸ h_z(1 - t/L) ρ(t)))`.

* **(98B), `contactSourcePairing_balance`.**  `I - ∑_q β_q p_z(ω_q) = |M|²/γ`.
  This is the real form of the proved source-kernel representation
  (`explicitCanonicalSourceMoment_eq_sourceKernelRHS`) paired with the M74 phase
  lock (`canonical_contact_phase`).  No F04 is used.
* **(99B), `contactSourcePairing_nearOld_balance`.**  For every split `θ`, with
  `N = ∑_{ω_q ≤ θ} β_q (-p_z(ω_q))` and `O = ∑_{ω_q > θ} β_q p_z(ω_q)`,
  `I - O + N = |M|²/γ`, so `O = I + N - |M|²/γ`.
* **Gap.**  `γ ≤ ‖g‖²/λ_odd`, so `|M|²/γ ≥ λ_odd |M|²/‖g‖² > 0` and
  `O ≤ I + N - λ_odd |M|²/‖g‖² < I + N`.
* **Endpoints.**  Every active sample has `0 ≤ ω_q ≤ 1`, and `p_z(0) = 0`, so a
  seam sample `q = e^L` contributes `0`.

The sign of `N` is not used: no near-edge sign of `p_z` is proved here.  These
are exact identities and a necessary condition at every contact.  The opposite
side `O ≥ I + N` (plan (99C)) is OPEN; it is never assumed, and the identities
exclude nothing.
-/

/-- `p_z(ω) = Re(conj(M₄ z) h_z(ω))`. -/
def contactSourcePairing (K : ℕ) (z : euclideanEvenBoundaryFlatSubspace K) (ω : ℝ) : ℝ :=
  (conj (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K z)) *
    quadraticNormalSourceAtom K z ω).re

/-- The pole-minus-archimedean part `I` of the real source pairing. -/
def contactSourcePoleArch (L : ℝ) (K : ℕ) (z : euclideanEvenBoundaryFlatSubspace K) : ℝ :=
  (conj (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K z)) *
    ((∫ x in (0 : ℝ)..L,
        quadraticNormalSourceAtom K z (1 - x / L) * (completeSourcePoleWeight x : ℂ)) -
      ∫ x in (0 : ℝ)..L,
        quadraticNormalSourceAtom K z (1 - x / L) * (archDensity x : ℂ))).re

/-- The source pairing vanishes at the seam coordinate `ω = 0`. -/
theorem contactSourcePairing_zero (K : ℕ) (z : euclideanEvenBoundaryFlatSubspace K) :
    contactSourcePairing K z 0 = 0 := by
  simp [contactSourcePairing, quadraticNormalSourceAtom_zero]

/-- **(98B)** At an even contact, `I - ∑_q β_q p_z(ω_q) = |M₄ z|²/γ_L`. -/
theorem contactSourcePairing_balance {L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 2 ≤ K)
    (hpos : 0 < parityRayleighBottom .odd L K)
    {z : euclideanEvenBoundaryFlatSubspace K}
    (hz : evenCompressedCanonical L K z = 0) (hz0 : z ≠ 0) :
    contactSourcePoleArch L K z -
        ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
          Λ q / Real.sqrt q * contactSourcePairing K z (primeSourceCoordinate q L) =
      Complex.normSq (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K z)) /
        canonicalResolventGamma L K hpos := by
  have h := (canonical_contact_phase hL hK hpos hz hz0).2.2
  rw [explicitCanonicalSourceMoment_eq_sourceKernelRHS hL K (by omega) z] at h
  unfold quadraticNormalSourceKernelRHS at h
  rw [← h, mul_sub, Complex.sub_re, Finset.mul_sum, Complex.re_sum]
  unfold contactSourcePoleArch
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold contactSourcePairing primeSourceWeight
  rw [mul_left_comm, Complex.re_ofReal_mul]

/-- **(99B)** For every split `θ`, `I - O + N = |M₄ z|²/γ_L`, with older part
`O = ∑_{ω_q > θ} β_q p_z(ω_q)` and near part `N = ∑_{ω_q ≤ θ} β_q (-p_z(ω_q))`. -/
theorem contactSourcePairing_nearOld_balance {L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 2 ≤ K)
    (hpos : 0 < parityRayleighBottom .odd L K)
    {z : euclideanEvenBoundaryFlatSubspace K}
    (hz : evenCompressedCanonical L K z = 0) (hz0 : z ≠ 0) (θ : ℝ) :
    contactSourcePoleArch L K z -
        ∑ q ∈ (Finset.Icc 2 ⌊Real.exp L⌋₊).filter (fun q => ¬ primeSourceCoordinate q L ≤ θ),
          Λ q / Real.sqrt q * contactSourcePairing K z (primeSourceCoordinate q L) +
        ∑ q ∈ (Finset.Icc 2 ⌊Real.exp L⌋₊).filter (fun q => primeSourceCoordinate q L ≤ θ),
          Λ q / Real.sqrt q * (-contactSourcePairing K z (primeSourceCoordinate q L)) =
      Complex.normSq (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K z)) /
        canonicalResolventGamma L K hpos := by
  have h := contactSourcePairing_balance hL hK hpos hz hz0
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 2 ⌊Real.exp L⌋₊)
    (fun q => primeSourceCoordinate q L ≤ θ)] at h
  have hneg : ∑ q ∈ (Finset.Icc 2 ⌊Real.exp L⌋₊).filter (fun q => primeSourceCoordinate q L ≤ θ),
      Λ q / Real.sqrt q * (-contactSourcePairing K z (primeSourceCoordinate q L)) =
      -∑ q ∈ (Finset.Icc 2 ⌊Real.exp L⌋₊).filter (fun q => primeSourceCoordinate q L ≤ θ),
        Λ q / Real.sqrt q * contactSourcePairing K z (primeSourceCoordinate q L) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [hneg]
  linarith

/-- `γ_L ≤ ‖g‖² / λ_odd`. -/
theorem canonicalResolventGamma_le {L : ℝ} {K : ℕ}
    (hpos : 0 < parityRayleighBottom .odd L K) :
    canonicalResolventGamma L K hpos ≤
      ‖oddCubicCompressionVector K‖ ^ 2 / parityRayleighBottom .odd L K := by
  set δ := parityRayleighBottom .odd L K
  set r := canonicalResolventVector L K hpos
  set g := oddCubicCompressionVector K
  have hr : δ * ‖r‖ ≤ ‖g‖ := canonical_resolventVector_norm_le hpos
  have hγ : canonicalResolventGamma L K hpos ≤ ‖g‖ * ‖r‖ := by
    have h := canonicalResolventGamma_ofReal (L := L) (K := K) hpos
    calc canonicalResolventGamma L K hpos
        = ((canonicalResolventGamma L K hpos : ℝ) : ℂ).re := by rw [Complex.ofReal_re]
      _ ≤ ‖((canonicalResolventGamma L K hpos : ℝ) : ℂ)‖ := Complex.re_le_norm _
      _ = ‖inner ℂ g r‖ := by rw [h]
      _ ≤ ‖g‖ * ‖r‖ := norm_inner_le_norm g r
  rw [le_div_iff₀ hpos]
  have hg0 := norm_nonneg g
  have hr' : ‖r‖ ≤ ‖g‖ / δ := by rw [le_div_iff₀ hpos]; linarith
  calc canonicalResolventGamma L K hpos * δ ≤ ‖g‖ * ‖r‖ * δ :=
        mul_le_mul_of_nonneg_right hγ hpos.le
    _ = ‖g‖ * (δ * ‖r‖) := by ring
    _ ≤ ‖g‖ * ‖g‖ := mul_le_mul_of_nonneg_left hr hg0
    _ = ‖g‖ ^ 2 := by ring

/-- **Quantitative gap.**  At an even contact the margin `|M₄ z|²/γ_L` is at
least `λ_odd |M₄ z|² / ‖g‖² > 0`. -/
theorem contactSourceMargin_ge {L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 2 ≤ K)
    (hpos : 0 < parityRayleighBottom .odd L K)
    {z : euclideanEvenBoundaryFlatSubspace K}
    (hz : evenCompressedCanonical L K z = 0) (hz0 : z ≠ 0) :
    0 < parityRayleighBottom .odd L K *
          Complex.normSq (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K z)) /
        ‖oddCubicCompressionVector K‖ ^ 2 ∧
      parityRayleighBottom .odd L K *
          Complex.normSq (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K z)) /
        ‖oddCubicCompressionVector K‖ ^ 2 ≤
      Complex.normSq (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K z)) /
        canonicalResolventGamma L K hpos := by
  set M := centeredMoment K 4 (evenBoundaryFlatRawCoefficients K z)
  set γ := canonicalResolventGamma L K hpos
  set δ := parityRayleighBottom .odd L K
  set g := oddCubicCompressionVector K
  have hγ : 0 < γ := canonicalResolventGamma_pos hK hpos
  have hg : 0 < ‖g‖ := norm_pos_iff.mpr (oddCubicCompressionVector_ne_zero K hK)
  -- `M ≠ 0` from the phase lock: `Re(conj M S) = |M|²/γ` and `Re(conj S M) > 0`
  have hph := canonical_contact_phase hL hK hpos hz hz0
  have hM : M ≠ 0 := by
    intro h0
    have h2 := hph.2.1
    change 0 < (conj (explicitCanonicalSourceMoment L K z) * M).re at h2
    rw [h0, mul_zero, Complex.zero_re] at h2
    exact lt_irrefl _ h2
  have hMpos : 0 < Complex.normSq M := Complex.normSq_pos.mpr hM
  have hγle : γ ≤ ‖g‖ ^ 2 / δ := canonicalResolventGamma_le hpos
  refine ⟨by positivity, ?_⟩
  rw [div_le_div_iff₀ (by positivity) hγ]
  have : γ * δ ≤ ‖g‖ ^ 2 := by rwa [le_div_iff₀ hpos] at hγle
  nlinarith

/-- **(99B) with the gap.**  At an even contact and for every split `θ`,
`O ≤ I + N - λ_odd |M₄ z|²/‖g‖²`; in particular `O < I + N`.  A necessary
condition, not an exclusion: the opposite side `O ≥ I + N` is OPEN. -/
theorem contactSourcePairing_older_le {L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 2 ≤ K)
    (hpos : 0 < parityRayleighBottom .odd L K)
    {z : euclideanEvenBoundaryFlatSubspace K}
    (hz : evenCompressedCanonical L K z = 0) (hz0 : z ≠ 0) (θ : ℝ) :
    ∑ q ∈ (Finset.Icc 2 ⌊Real.exp L⌋₊).filter (fun q => ¬ primeSourceCoordinate q L ≤ θ),
        Λ q / Real.sqrt q * contactSourcePairing K z (primeSourceCoordinate q L) ≤
      contactSourcePoleArch L K z +
        ∑ q ∈ (Finset.Icc 2 ⌊Real.exp L⌋₊).filter (fun q => primeSourceCoordinate q L ≤ θ),
          Λ q / Real.sqrt q * (-contactSourcePairing K z (primeSourceCoordinate q L)) -
        parityRayleighBottom .odd L K *
            Complex.normSq (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K z)) /
          ‖oddCubicCompressionVector K‖ ^ 2 := by
  have h := contactSourcePairing_nearOld_balance hL hK hpos hz hz0 θ
  have hm := (contactSourceMargin_ge hL hK hpos hz hz0).2
  linarith

end Zeta23.CCM

#print axioms Zeta23.CCM.contactSourcePairing_zero
#print axioms Zeta23.CCM.contactSourcePairing_balance
#print axioms Zeta23.CCM.contactSourcePairing_nearOld_balance
#print axioms Zeta23.CCM.canonicalResolventGamma_le
#print axioms Zeta23.CCM.contactSourceMargin_ge
#print axioms Zeta23.CCM.contactSourcePairing_older_le
