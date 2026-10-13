import Zeta23.CCM.CanonicalPoleNeutralGeometry
import Zeta23.CCM.SourceSignCountermodels
import Zeta23.CCM.CanonicalCenteredIndexPoincare

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators ComplexConjugate

/-!
Actual native pole functionals are nonzero on the legal parity carriers once
`K ≥ 2`. The witness is the unchanged existing five-point even source stencil,
with centered zero extension. Its elementary-source sign is not used here.

The rank-nullity calculation concerns the native kernels in the existing legal
coefficient spaces. It supplies neither a canonical spectral sign nor a ground
state. The dimension at `K = 2` is zero; nonzero neutral vectors require `K ≥ 3`.
-/

/-- The unchanged native even profile pairing respects centered zero extension. -/
theorem poleEvenProfile_dot_centeredZeroExtend (L : ℝ)
    {N M : ℕ} (hNM : N ≤ M) (u : Fin (2 * N + 1) → ℂ) :
    poleEvenProfile L M ⬝ᵥ centeredZeroExtend hNM u = poleEvenProfile L N ⬝ᵥ u := by
  unfold dotProduct
  rw [Fintype.sum_of_injective
    (centeredEmbedding N M hNM)
    (centeredEmbedding N M hNM).injective
    (fun i : Fin (2 * N + 1) => poleEvenProfile L N i * u i)
    (fun j : Fin (2 * M + 1) =>
      poleEvenProfile L M j * centeredZeroExtend hNM u j)]
  · intro j hj
    rw [centeredZeroExtend_apply_of_not_mem_range hNM u j]
    · simp
    · simpa using hj
  · intro i
    simp [poleEvenProfile]

/-- Exact native even pole pairing of the existing legal five-point stencil. -/
theorem poleEvenProfile_dot_positiveEvenSourceWitness {L : ℝ} (hL : 0 < L) :
    poleEvenProfile L 2 ⬝ᵥ positiveEvenSourceWitness =
      ((6144 * Real.pi ^ 4 /
        (L * (L ^ 2 + 16 * Real.pi ^ 2) * (L ^ 2 + 64 * Real.pi ^ 2)) : ℝ) : ℂ) := by
  have hL0 : L ≠ 0 := hL.ne'
  have h16 : L ^ 2 + 16 * Real.pi ^ 2 ≠ 0 := by positivity
  have h64 : L ^ 2 + 64 * Real.pi ^ 2 ≠ 0 := by positivity
  have hr :
      2 * (L / (L ^ 2 + 64 * Real.pi ^ 2)) -
        8 * (L / (L ^ 2 + 16 * Real.pi ^ 2)) + 6 * (L / L ^ 2) =
      6144 * Real.pi ^ 4 /
        (L * (L ^ 2 + 16 * Real.pi ^ 2) * (L ^ 2 + 64 * Real.pi ^ 2)) := by
    field_simp [hL0, h16, h64]
    ring
  have h2 : poleProfileDenominator (-2) L = L ^ 2 + 64 * Real.pi ^ 2 := by
    unfold poleProfileDenominator
    norm_num
    ring
  have h1 : poleProfileDenominator (-1) L = L ^ 2 + 16 * Real.pi ^ 2 := by
    simp [poleProfileDenominator]
  have h0 : poleProfileDenominator 0 L = L ^ 2 := by
    simp [poleProfileDenominator]
  have hp1 : poleProfileDenominator 1 L = L ^ 2 + 16 * Real.pi ^ 2 := by
    simp [poleProfileDenominator]
  have hp2 : poleProfileDenominator 2 L = L ^ 2 + 64 * Real.pi ^ 2 := by
    unfold poleProfileDenominator
    norm_num
    ring
  have he : poleEvenProfile L 2 ⬝ᵥ positiveEvenSourceWitness =
      ((2 * (L / (L ^ 2 + 64 * Real.pi ^ 2)) -
        8 * (L / (L ^ 2 + 16 * Real.pi ^ 2)) + 6 * (L / L ^ 2) : ℝ) : ℂ) := by
    simp [dotProduct, Fin.sum_univ_succ, positiveEvenSourceWitness,
      poleEvenProfile, poleEvenProfileReal, centeredIndex, h2, h1, h0, hp1, hp2]
    push_cast
    ring
  rw [he, hr]

/-- Positive real native pairing; no source-matrix sign is inferred. -/
theorem poleEvenProfile_dot_positiveEvenSourceWitness_re_pos {L : ℝ} (hL : 0 < L) :
    0 < (poleEvenProfile L 2 ⬝ᵥ positiveEvenSourceWitness).re := by
  rw [poleEvenProfile_dot_positiveEvenSourceWitness hL]
  simp only [Complex.ofReal_re]
  positivity

/-- The actual legal even witness at every `K ≥ 2`. -/
def canonicalPoleEvenNonzeroWitness (K : ℕ) (hK : 2 ≤ K) :
    euclideanEvenBoundaryFlatSubspace K :=
  ⟨WithLp.toLp 2 (centeredZeroExtend hK positiveEvenSourceWitness), by
    rw [mem_euclideanEvenBoundaryFlatSubspace_iff]
    change centeredZeroExtend hK positiveEvenSourceWitness ∈ evenBoundaryFlatSubspace K
    exact centeredZeroExtend_mem_evenBoundaryFlatSubspace hK positiveEvenSourceWitness_mem⟩

theorem canonicalPoleEvenFunctional_nonzeroWitness {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) :
    canonicalPoleEvenFunctional L K (canonicalPoleEvenNonzeroWitness K hK) ≠ 0 := by
  have he : canonicalPoleEvenFunctional L K (canonicalPoleEvenNonzeroWitness K hK) =
      poleEvenProfile L 2 ⬝ᵥ positiveEvenSourceWitness := by
    change poleEvenProfile L K ⬝ᵥ centeredZeroExtend hK positiveEvenSourceWitness = _
    exact poleEvenProfile_dot_centeredZeroExtend L hK positiveEvenSourceWitness
  rw [he]
  intro hz
  have hp := poleEvenProfile_dot_positiveEvenSourceWitness_re_pos hL
  rw [hz, Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

/-- The actual legal odd witness is the centered-index image of the even one. -/
def canonicalPoleOddNonzeroWitness (K : ℕ) (hK : 2 ≤ K) :
    euclideanOddBoundaryFlatSubspace K :=
  euclideanEvenToOddIndexLinearMap K (canonicalPoleEvenNonzeroWitness K hK)

theorem canonicalPoleOddFunctional_nonzeroWitness {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) :
    canonicalPoleOddFunctional L K (canonicalPoleOddNonzeroWitness K hK) ≠ 0 := by
  rw [canonicalPoleOddNonzeroWitness, canonicalPoleOddFunctional_evenIndex hL]
  apply mul_ne_zero
  · exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
      (div_ne_zero hL.ne' (by positivity)))
  · exact canonicalPoleEvenFunctional_nonzeroWitness hL K hK

/-- Restricted native even functional, with its precise legal ambient space. -/
def legalCanonicalPoleEvenFunctional (L : ℝ) (K : ℕ) :
    euclideanEvenBoundaryFlatSubspace K →ₗ[ℂ] ℂ :=
  (canonicalPoleEvenFunctional L K).comp (euclideanEvenBoundaryFlatSubspace K).subtype

/-- Restricted native odd functional. -/
def legalCanonicalPoleOddFunctional (L : ℝ) (K : ℕ) :
    euclideanOddBoundaryFlatSubspace K →ₗ[ℂ] ℂ :=
  (canonicalPoleOddFunctional L K).comp (euclideanOddBoundaryFlatSubspace K).subtype

theorem legalCanonicalPoleEvenFunctional_ne_zero {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) : legalCanonicalPoleEvenFunctional L K ≠ 0 := by
  intro hf
  have hw := congrArg
    (fun f : euclideanEvenBoundaryFlatSubspace K →ₗ[ℂ] ℂ =>
      f (canonicalPoleEvenNonzeroWitness K hK)) hf
  exact canonicalPoleEvenFunctional_nonzeroWitness hL K hK
    (by simpa [legalCanonicalPoleEvenFunctional] using hw)

theorem legalCanonicalPoleOddFunctional_ne_zero {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) : legalCanonicalPoleOddFunctional L K ≠ 0 := by
  intro hf
  have hw := congrArg
    (fun f : euclideanOddBoundaryFlatSubspace K →ₗ[ℂ] ℂ =>
      f (canonicalPoleOddNonzeroWitness K hK)) hf
  exact canonicalPoleOddFunctional_nonzeroWitness hL K hK
    (by simpa [legalCanonicalPoleOddFunctional] using hw)

theorem legalCanonicalPoleEvenFunctional_surjective {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) :
    Function.Surjective (legalCanonicalPoleEvenFunctional L K) := by
  let u := canonicalPoleEvenNonzeroWitness K hK
  have hu : legalCanonicalPoleEvenFunctional L K u ≠ 0 :=
    canonicalPoleEvenFunctional_nonzeroWitness hL K hK
  intro c
  refine ⟨(c / legalCanonicalPoleEvenFunctional L K u) • u, ?_⟩
  rw [map_smul, smul_eq_mul]
  exact div_mul_cancel₀ c hu

theorem legalCanonicalPoleOddFunctional_surjective {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) :
    Function.Surjective (legalCanonicalPoleOddFunctional L K) := by
  let u := canonicalPoleOddNonzeroWitness K hK
  have hu : legalCanonicalPoleOddFunctional L K u ≠ 0 :=
    canonicalPoleOddFunctional_nonzeroWitness hL K hK
  intro c
  refine ⟨(c / legalCanonicalPoleOddFunctional L K u) • u, ?_⟩
  rw [map_smul, smul_eq_mul]
  exact div_mul_cancel₀ c hu

/-- Native even pole-neutral dimension, including the trivial `K = 2` carrier. -/
theorem finrank_poleNeutralEvenSubspace {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) :
    Module.finrank ℂ (poleNeutralEvenSubspace L K) = K - 2 := by
  have hdim := (legalCanonicalPoleEvenFunctional L K).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (legalCanonicalPoleEvenFunctional_surjective hL K hK),
    Submodule.finrank_top, Module.finrank_self,
    finrank_euclideanEvenBoundaryFlatSubspace K (by omega)] at hdim
  change 1 + Module.finrank ℂ (poleNeutralEvenSubspace L K) = K - 1 at hdim
  omega

/-- Native odd pole-neutral dimension on the same exact domain. -/
theorem finrank_poleNeutralOddSubspace {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) :
    Module.finrank ℂ (poleNeutralOddSubspace L K) = K - 2 := by
  have hdim := (legalCanonicalPoleOddFunctional L K).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (legalCanonicalPoleOddFunctional_surjective hL K hK),
    Submodule.finrank_top, Module.finrank_self,
    finrank_euclideanOddBoundaryFlatSubspace K (by omega)] at hdim
  change 1 + Module.finrank ℂ (poleNeutralOddSubspace L K) = K - 1 at hdim
  omega

/-- Restrict the proved coefficient Poincaré bound to the exact native kernel.
The algebraic index equivalence is not asserted to preserve the norm. -/
theorem poleNeutralIndex_norm_lower {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) :
    ‖u‖ ^ 2 ≤ 4 * ‖poleNeutralIndexLinearMap hL K u‖ ^ 2 := by
  have hflat := evenBoundaryFlatRawCoefficients_boundaryFlat K u.val
  have hc := norm_sq_le_four_mul_norm_index_sq K
    (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))) hflat.1
  exact hc

end Zeta23.CCM

#print axioms Zeta23.CCM.poleEvenProfile_dot_positiveEvenSourceWitness
#print axioms Zeta23.CCM.canonicalPoleEvenFunctional_nonzeroWitness
#print axioms Zeta23.CCM.canonicalPoleOddFunctional_nonzeroWitness
#print axioms Zeta23.CCM.legalCanonicalPoleEvenFunctional_ne_zero
#print axioms Zeta23.CCM.legalCanonicalPoleOddFunctional_ne_zero
#print axioms Zeta23.CCM.legalCanonicalPoleEvenFunctional_surjective
#print axioms Zeta23.CCM.legalCanonicalPoleOddFunctional_surjective
#print axioms Zeta23.CCM.finrank_poleNeutralEvenSubspace
#print axioms Zeta23.CCM.finrank_poleNeutralOddSubspace
#print axioms Zeta23.CCM.poleNeutralIndex_norm_lower
