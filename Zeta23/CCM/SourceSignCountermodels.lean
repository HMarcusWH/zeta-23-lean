import Zeta23.CCM.SourceLatticeCoordinates

noncomputable section

namespace Zeta23.CCM

open Matrix Finset
open scoped BigOperators ComplexConjugate

/-!
# POST284-M04/M15/M18: exact elementary source sign countermodels

Exact integer witnesses for the elementary `sourceMatrix`:

* `K = 3` even `(1,-4,7,-8,7,-4,1)`: boundary flat, `M_0 = ⋯ = M_3 = 0`,
  `M_4 = 48`, and source energy `-4` at `ω = 1/2`.  This falsifies universal
  elementary-source positivity on the even boundary-flat carrier.
* `K = 2` even `(1,-4,6,-4,1)`: `M_4 = 24`, energy `+6` at `ω = 1/2`.
* `K = 2` odd `(-1,2,0,-2,1)`: `M_3 = 12`, energy `-6` at `ω = 1/2`.
* `K = 3` even `(1,-6,15,-20,15,-6,1)`: `M_0 = ⋯ = M_5 = 0`, `M_6 = 720`.
* `K = 3` odd `(-1,4,-5,0,5,-4,1)`: `M_0 = ⋯ = M_4 = 0`, `M_5 = 240`.

Fourth-moment firewall: for every `K ≥ 3` the even boundary-flat carrier
contains vectors with `M_4 ≠ 0` of both strict half-aperture source signs, so
`M_4 ≠ 0` alone cannot select an elementary source sign.

Scope: elementary `sourceMatrix` only.  None of these vectors is claimed to be
a canonical contact eigenvector.
-/

/-- `K = 3` even negative source witness `(1,-4,7,-8,7,-4,1)`. -/
def negativeEvenSourceWitness : Fin (2 * 3 + 1) → ℂ := ![1, -4, 7, -8, 7, -4, 1]

/-- `K = 2` even positive source witness `(1,-4,6,-4,1)`. -/
def positiveEvenSourceWitness : Fin (2 * 2 + 1) → ℂ := ![1, -4, 6, -4, 1]

/-- `K = 2` odd source witness `(-1,2,0,-2,1)`. -/
def oddSourceWitnessK2 : Fin (2 * 2 + 1) → ℂ := ![-1, 2, 0, -2, 1]

/-- `K = 3` even sixth-moment witness `(1,-6,15,-20,15,-6,1)`. -/
def evenSixthMomentWitness : Fin (2 * 3 + 1) → ℂ := ![1, -6, 15, -20, 15, -6, 1]

/-- `K = 3` odd fifth-moment witness `(-1,4,-5,0,5,-4,1)`. -/
def oddFifthMomentWitness : Fin (2 * 3 + 1) → ℂ := ![-1, 4, -5, 0, 5, -4, 1]

section Computations

private theorem latticeSign_values :
    latticeSign (-3) = -1 ∧ latticeSign (-2) = 1 ∧ latticeSign (-1) = -1 ∧
      latticeSign 0 = 1 ∧ latticeSign 1 = -1 ∧ latticeSign 2 = 1 ∧ latticeSign 3 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [latticeSign] <;> decide

theorem negativeEvenSourceWitness_moments :
    centeredMoment 3 0 negativeEvenSourceWitness = 0 ∧
      centeredMoment 3 1 negativeEvenSourceWitness = 0 ∧
      centeredMoment 3 2 negativeEvenSourceWitness = 0 ∧
      centeredMoment 3 3 negativeEvenSourceWitness = 0 ∧
      centeredMoment 3 4 negativeEvenSourceWitness = 48 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (norm_num [centeredMoment, Fin.sum_univ_succ, negativeEvenSourceWitness, centeredIndex])

theorem positiveEvenSourceWitness_moments :
    centeredMoment 2 0 positiveEvenSourceWitness = 0 ∧
      centeredMoment 2 1 positiveEvenSourceWitness = 0 ∧
      centeredMoment 2 2 positiveEvenSourceWitness = 0 ∧
      centeredMoment 2 3 positiveEvenSourceWitness = 0 ∧
      centeredMoment 2 4 positiveEvenSourceWitness = 24 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (norm_num [centeredMoment, Fin.sum_univ_succ, positiveEvenSourceWitness, centeredIndex])

theorem oddSourceWitnessK2_moments :
    centeredMoment 2 0 oddSourceWitnessK2 = 0 ∧
      centeredMoment 2 1 oddSourceWitnessK2 = 0 ∧
      centeredMoment 2 2 oddSourceWitnessK2 = 0 ∧
      centeredMoment 2 3 oddSourceWitnessK2 = 12 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (norm_num [centeredMoment, Fin.sum_univ_succ, oddSourceWitnessK2, centeredIndex])

theorem evenSixthMomentWitness_moments :
    centeredMoment 3 0 evenSixthMomentWitness = 0 ∧
      centeredMoment 3 1 evenSixthMomentWitness = 0 ∧
      centeredMoment 3 2 evenSixthMomentWitness = 0 ∧
      centeredMoment 3 3 evenSixthMomentWitness = 0 ∧
      centeredMoment 3 4 evenSixthMomentWitness = 0 ∧
      centeredMoment 3 5 evenSixthMomentWitness = 0 ∧
      centeredMoment 3 6 evenSixthMomentWitness = 720 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (norm_num [centeredMoment, Fin.sum_univ_succ, evenSixthMomentWitness, centeredIndex])

theorem oddFifthMomentWitness_moments :
    centeredMoment 3 0 oddFifthMomentWitness = 0 ∧
      centeredMoment 3 1 oddFifthMomentWitness = 0 ∧
      centeredMoment 3 2 oddFifthMomentWitness = 0 ∧
      centeredMoment 3 3 oddFifthMomentWitness = 0 ∧
      centeredMoment 3 4 oddFifthMomentWitness = 0 ∧
      centeredMoment 3 5 oddFifthMomentWitness = 240 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (norm_num [centeredMoment, Fin.sum_univ_succ, oddFifthMomentWitness, centeredIndex])

/-- Exact half-aperture source energy of the `K = 3` negative witness. -/
theorem negativeEvenSourceWitness_half_energy :
    quadraticForm (sourceMatrix (1 / 2) 3) negativeEvenSourceWitness = -4 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := latticeSign_values
  rw [quadraticForm_sourceMatrix_half]
  simp [Fin.sum_univ_succ, negativeEvenSourceWitness, centeredIndex,
    h1, h2, h3, h4, h5, h6, h7, Complex.conj_ofNat]
  norm_num

/-- Exact half-aperture source energy of the `K = 2` positive witness. -/
theorem positiveEvenSourceWitness_half_energy :
    quadraticForm (sourceMatrix (1 / 2) 2) positiveEvenSourceWitness = 6 := by
  obtain ⟨-, h2, h3, h4, h5, h6, -⟩ := latticeSign_values
  rw [quadraticForm_sourceMatrix_half]
  simp [Fin.sum_univ_succ, positiveEvenSourceWitness, centeredIndex,
    h2, h3, h4, h5, h6, Complex.conj_ofNat]
  norm_num

/-- Exact half-aperture source energy of the `K = 2` odd witness. -/
theorem oddSourceWitnessK2_half_energy :
    quadraticForm (sourceMatrix (1 / 2) 2) oddSourceWitnessK2 = -6 := by
  obtain ⟨-, h2, h3, h4, h5, h6, -⟩ := latticeSign_values
  rw [quadraticForm_sourceMatrix_half]
  simp [Fin.sum_univ_succ, oddSourceWitnessK2, centeredIndex,
    h2, h3, h4, h5, h6, Complex.conj_ofNat]
  norm_num

theorem negativeEvenSourceWitness_even :
    negativeEvenSourceWitness ∈ evenCoefficientSubspace 3 := by
  rw [mem_evenCoefficientSubspace_iff]
  funext i
  fin_cases i <;> rfl

theorem positiveEvenSourceWitness_even :
    positiveEvenSourceWitness ∈ evenCoefficientSubspace 2 := by
  rw [mem_evenCoefficientSubspace_iff]
  funext i
  fin_cases i <;> rfl

theorem oddSourceWitnessK2_odd :
    oddSourceWitnessK2 ∈ oddCoefficientSubspace 2 := by
  rw [mem_oddCoefficientSubspace_iff]
  funext i
  fin_cases i <;> simp [reverseCoefficients, oddSourceWitnessK2]

end Computations

theorem negativeEvenSourceWitness_mem :
    negativeEvenSourceWitness ∈ evenBoundaryFlatSubspace 3 := by
  obtain ⟨h0, h1, h2, -, -⟩ := negativeEvenSourceWitness_moments
  exact ⟨(mem_boundaryFlatSubspace_iff 3 _).mpr ⟨h0, h1, h2⟩,
    negativeEvenSourceWitness_even⟩

theorem positiveEvenSourceWitness_mem :
    positiveEvenSourceWitness ∈ evenBoundaryFlatSubspace 2 := by
  obtain ⟨h0, h1, h2, -, -⟩ := positiveEvenSourceWitness_moments
  exact ⟨(mem_boundaryFlatSubspace_iff 2 _).mpr ⟨h0, h1, h2⟩,
    positiveEvenSourceWitness_even⟩

theorem oddSourceWitnessK2_mem :
    oddSourceWitnessK2 ∈ oddBoundaryFlatSubspace 2 := by
  obtain ⟨h0, h1, h2, -⟩ := oddSourceWitnessK2_moments
  exact ⟨(mem_boundaryFlatSubspace_iff 2 _).mpr ⟨h0, h1, h2⟩, oddSourceWitnessK2_odd⟩

/-- **Exact negative elementary source control (M04).**  The even
boundary-flat `K = 3` vector `(1,-4,7,-8,7,-4,1)` has `M_0 = ⋯ = M_3 = 0`,
`M_4 = 48` and half-aperture source energy `-4`. -/
theorem negativeEvenSourceWitness_control :
    negativeEvenSourceWitness ∈ evenBoundaryFlatSubspace 3 ∧
      centeredMoment 3 3 negativeEvenSourceWitness = 0 ∧
      centeredMoment 3 4 negativeEvenSourceWitness = 48 ∧
      quadraticForm (sourceMatrix (1 / 2) 3) negativeEvenSourceWitness = -4 :=
  ⟨negativeEvenSourceWitness_mem, negativeEvenSourceWitness_moments.2.2.2.1,
    negativeEvenSourceWitness_moments.2.2.2.2, negativeEvenSourceWitness_half_energy⟩

/-- **Fourth-moment firewall (M18).**  For every `K ≥ 3` the even
boundary-flat carrier contains vectors with nonzero fourth moment and both
strict half-aperture elementary source signs. -/
theorem fourthMoment_firewall_even (K : ℕ) (hK : 3 ≤ K) :
    ∃ u v : Fin (2 * K + 1) → ℂ,
      u ∈ evenBoundaryFlatSubspace K ∧ v ∈ evenBoundaryFlatSubspace K ∧
      centeredMoment K 4 u = 24 ∧ centeredMoment K 4 v = 48 ∧
      quadraticForm (sourceMatrix (1 / 2) K) u = 6 ∧
      quadraticForm (sourceMatrix (1 / 2) K) v = -4 := by
  refine ⟨centeredZeroExtend (show 2 ≤ K by omega) positiveEvenSourceWitness,
    centeredZeroExtend hK negativeEvenSourceWitness,
    centeredZeroExtend_mem_evenBoundaryFlatSubspace (by omega) positiveEvenSourceWitness_mem,
    centeredZeroExtend_mem_evenBoundaryFlatSubspace hK negativeEvenSourceWitness_mem,
    ?_, ?_, ?_, ?_⟩
  · rw [centeredMoment_centeredZeroExtend (by omega)]
    exact positiveEvenSourceWitness_moments.2.2.2.2
  · rw [centeredMoment_centeredZeroExtend hK]
    exact negativeEvenSourceWitness_moments.2.2.2.2
  · rw [quadraticForm_sourceMatrix_centeredZeroExtend (by omega)]
    exact positiveEvenSourceWitness_half_energy
  · rw [quadraticForm_sourceMatrix_centeredZeroExtend hK]
    exact negativeEvenSourceWitness_half_energy

/-- Odd half-aperture negative control at every `K ≥ 2`. -/
theorem oddSource_half_negative_control (K : ℕ) (hK : 2 ≤ K) :
    ∃ u : Fin (2 * K + 1) → ℂ,
      u ∈ oddBoundaryFlatSubspace K ∧ centeredMoment K 3 u = 12 ∧
      quadraticForm (sourceMatrix (1 / 2) K) u = -6 := by
  refine ⟨centeredZeroExtend hK oddSourceWitnessK2,
    centeredZeroExtend_mem_oddBoundaryFlatSubspace hK oddSourceWitnessK2_mem, ?_, ?_⟩
  · rw [centeredMoment_centeredZeroExtend hK]
    exact oddSourceWitnessK2_moments.2.2.2
  · rw [quadraticForm_sourceMatrix_centeredZeroExtend hK]
    exact oddSourceWitnessK2_half_energy

end Zeta23.CCM

#print axioms Zeta23.CCM.negativeEvenSourceWitness_control
#print axioms Zeta23.CCM.positiveEvenSourceWitness_moments
#print axioms Zeta23.CCM.oddSourceWitnessK2_moments
#print axioms Zeta23.CCM.evenSixthMomentWitness_moments
#print axioms Zeta23.CCM.oddFifthMomentWitness_moments
#print axioms Zeta23.CCM.fourthMoment_firewall_even
#print axioms Zeta23.CCM.oddSource_half_negative_control
