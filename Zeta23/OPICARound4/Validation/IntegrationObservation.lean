import Zeta23.OPICARound4.NativeObservation

noncomputable section

namespace Zeta23.OPICARound4.Validation

open CCM OPICARound3
open scoped BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

theorem finite_observation_energy_consumer (T : E →ₗ[ℂ] E) (O : E →ₗ[ℂ] F)
    (d : ℕ) (x : E) :
    (inner ℂ x (finiteObservationGram T O d x)).re =
      ∑ j ∈ Finset.range d, ‖O ((T ^ j) x)‖ ^ 2 :=
  finiteObservationGram_energy T O d x

theorem finite_observation_kernel_consumer (T : E →ₗ[ℂ] E) (O : E →ₗ[ℂ] F)
    (d : ℕ) (x : E) :
    finiteObservationGram T O d x = 0 ↔ ∀ j < d, O ((T ^ j) x) = 0 :=
  finiteObservationGram_kernel_iff T O d x

theorem invisible_eigenmode_all_prefixes_consumer
    (T : E →ₗ[ℂ] E) (O : E →ₗ[ℂ] F) (x : E) (lam : ℂ)
    (hx : T x = lam • x) (ho : O x = 0) (d : ℕ) :
    finiteObservationGram T O d x = 0 :=
  blind_vector_in_every_finite_gram_kernel T O x
    (eigenmode_invisible_at_all_powers T O x lam hx ho) d

theorem declared_input_reachability_consumer {ι : Type*}
    (T : E →ₗ[ℂ] E) (O : E →ₗ[ℂ] F) (g : ι → E) (d : ℕ)
    (h : ∀ j < d, ∀ i, O ((T ^ j) (g i)) = 0) :
    finiteInputReachableSubspace T g d ≤ LinearMap.ker O :=
  reachable_subspace_in_output_kernel T O g d h

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

theorem native_even_invisible_observation_consumer {L : ℝ} (K : ℕ)
    (u : poleNeutralEvenSubspace L K) (lam : ℂ)
    (hu : poleNeutralEvenCompressedCanonical L K u = lam • u)
    (hf : poleNeutralCorrectedCubicSource L K u = 0) (d : ℕ) :
    finiteObservationGram (poleNeutralEvenCompressedCanonical L K)
      (nativeEvenObservation L K) d u = 0 :=
  native_even_invisible_gram K u lam hu hf d

theorem native_odd_invisible_observation_consumer {L : ℝ} (K : ℕ)
    (u : poleNeutralOddSubspace L K) (lam : ℂ)
    (hu : poleNeutralOddCompressedCanonical L K u = lam • u)
    (hf : poleNeutralCubicPairingFunctional L K u = 0) (d : ℕ) :
    finiteObservationGram (poleNeutralOddCompressedCanonical L K)
      (nativeOddObservation L K) d u = 0 :=
  native_odd_invisible_gram K u lam hu hf d

theorem positive_native_observation_bound_consumer {L : ℝ} {K : ℕ} {c : ℝ}
    (hc : 0 < c)
    (he : ∀ (u : poleNeutralEvenSubspace L K) (lam : ℝ), lam < 0 →
      poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u →
        c * ‖u‖ ≤ ‖nativeEvenObservation L K u‖)
    (ho : ∀ (u : poleNeutralOddSubspace L K) (lam : ℝ), lam < 0 →
      poleNeutralOddCompressedCanonical L K u = (lam : ℂ) • u →
        c * ‖u‖ ≤ ‖nativeOddObservation L K u‖)
    (u : poleNeutralEvenSubspace L K) (hu : u ≠ 0) (lam : ℝ) (hlam : lam < 0)
    (heigen : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :
    nativeEvenObservation L K u ≠ 0 :=
  native_observation_bound_excludes_invisible_even ⟨hc, he, ho⟩ u hu lam hlam heigen

end Zeta23.OPICARound4.Validation

#print axioms Zeta23.OPICARound4.Validation.finite_observation_energy_consumer
#print axioms Zeta23.OPICARound4.Validation.finite_observation_kernel_consumer
#print axioms Zeta23.OPICARound4.Validation.invisible_eigenmode_all_prefixes_consumer
#print axioms Zeta23.OPICARound4.Validation.declared_input_reachability_consumer
#print axioms Zeta23.OPICARound4.Validation.native_even_invisible_observation_consumer
#print axioms Zeta23.OPICARound4.Validation.native_odd_invisible_observation_consumer
#print axioms Zeta23.OPICARound4.Validation.positive_native_observation_bound_consumer
