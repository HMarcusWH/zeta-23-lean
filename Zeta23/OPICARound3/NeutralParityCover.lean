import Zeta23.OPICARound2.FiniteNeutralApproximation
import Zeta23.CCM.DetectorRetainedSchurState

noncomputable section

namespace Zeta23.OPICARound3

open Matrix Set
open CCM
open scoped BigOperators ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-! Actual complete-form neutral negativity. The predicates deliberately
carry no cutoff hypothesis, so that the zero-dimensional K=2 predecessor
remains available to first-cutoff consumers. -/

def EvenNeutralNegative (L : ℝ) (K : ℕ) : Prop :=
  ∃ u : poleNeutralEvenSubspace L K,
    (inner ℂ (poleNeutralEvenCompressedCanonical L K u) u).re < 0

def OddNeutralNegative (L : ℝ) (K : ℕ) : Prop :=
  ∃ u : poleNeutralOddSubspace L K,
    (inner ℂ (poleNeutralOddCompressedCanonical L K u) u).re < 0

def PoleNeutralParityNegative (p : ReversalParity) (L : ℝ) (K : ℕ) : Prop :=
  match p with
  | .even => EvenNeutralNegative L K
  | .odd => OddNeutralNegative L K

def BothNeutralNegative (L : ℝ) (K : ℕ) : Prop :=
  EvenNeutralNegative L K ∧ OddNeutralNegative L K

def fullCanonicalEnergy (L : ℝ) (K : ℕ)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) : ℝ :=
  (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin u) u).re

def parityPoleFunctional (p : ReversalParity) (L : ℝ) (K : ℕ) :
    EuclideanSpace ℂ (Fin (2 * K + 1)) →ₗ[ℂ] ℂ :=
  match p with
  | .even => canonicalPoleEvenFunctional L K
  | .odd => canonicalPoleOddFunctional L K

@[simp] theorem fullCanonicalEnergy_zero (L : ℝ) (K : ℕ) :
    fullCanonicalEnergy L K 0 = 0 := by
  simp [fullCanonicalEnergy]

theorem evenNeutralNegative_iff_ambient (L : ℝ) (K : ℕ) :
    EvenNeutralNegative L K ↔
      ∃ u : EuclideanSpace ℂ (Fin (2 * K + 1)),
        u ∈ euclideanEvenBoundaryFlatSubspace K ∧
        canonicalPoleEvenFunctional L K u = 0 ∧ fullCanonicalEnergy L K u < 0 := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u.val, u.val.property, (mem_poleNeutralEvenSubspace L K u.val).mp u.property, ?_⟩
    unfold fullCanonicalEnergy
    rw [← inner_poleNeutralEvenCompressedCanonical_self]
    exact hu
  · rintro ⟨u, hlegal, hpole, hneg⟩
    let v : poleNeutralEvenSubspace L K :=
      ⟨⟨u, hlegal⟩, (mem_poleNeutralEvenSubspace L K _).mpr hpole⟩
    refine ⟨v, ?_⟩
    rw [inner_poleNeutralEvenCompressedCanonical_self]
    exact hneg

theorem oddNeutralNegative_iff_ambient (L : ℝ) (K : ℕ) :
    OddNeutralNegative L K ↔
      ∃ u : EuclideanSpace ℂ (Fin (2 * K + 1)),
        u ∈ euclideanOddBoundaryFlatSubspace K ∧
        canonicalPoleOddFunctional L K u = 0 ∧ fullCanonicalEnergy L K u < 0 := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u.val, u.val.property, (mem_poleNeutralOddSubspace L K u.val).mp u.property, ?_⟩
    unfold fullCanonicalEnergy
    rw [← inner_poleNeutralOddCompressedCanonical_self]
    exact hu
  · rintro ⟨u, hlegal, hpole, hneg⟩
    let v : poleNeutralOddSubspace L K :=
      ⟨⟨u, hlegal⟩, (mem_poleNeutralOddSubspace L K _).mpr hpole⟩
    refine ⟨v, ?_⟩
    rw [inner_poleNeutralOddCompressedCanonical_self]
    exact hneg

theorem poleNeutralParityNegative_iff_ambient (p : ReversalParity) (L : ℝ) (K : ℕ) :
    PoleNeutralParityNegative p L K ↔
      ∃ u : EuclideanSpace ℂ (Fin (2 * K + 1)),
        u ∈ euclideanParityBoundaryFlatSubspace p K ∧
        parityPoleFunctional p L K u = 0 ∧ fullCanonicalEnergy L K u < 0 := by
  cases p
  · exact evenNeutralNegative_iff_ambient L K
  · exact oddNeutralNegative_iff_ambient L K

theorem negative_fullCanonicalEnergy_ne_zero {L : ℝ} {K : ℕ}
    {u : EuclideanSpace ℂ (Fin (2 * K + 1))} (hu : fullCanonicalEnergy L K u < 0) : u ≠ 0 := by
  intro hz
  rw [hz, fullCanonicalEnergy_zero] at hu
  exact (lt_irrefl 0) hu

theorem native_neutral_parity_negative_iff (p : ReversalParity) (L : ℝ) (K : ℕ) :
    PoleNeutralParityNegative p L K ↔
      ∃ u : nativePoleNeutralParitySpace p L K,
        (inner ℂ (nativePoleNeutralParityCanonical p L K u) u).re < 0 := by
  cases p <;> rfl

/-- Both physical pole equations survive the actual parity projections.
This constructs the native carriers rather than postulating neutrality of
a component selected only by its sign. -/
theorem native_neutral_negative_parity_split {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) (hlegal : BoundaryFlatCoefficients K u)
    (hp : canonicalPoleExponentialMoment 1 L K u = 0)
    (hm : canonicalPoleExponentialMoment (-1) L K u = 0)
    (hneg : (quadraticForm (canonicalSourceMatrix L K) u).re < 0) :
    EvenNeutralNegative L K ∨ OddNeutralNegative L K := by
  have hraw := (mem_boundaryFlatSubspace_iff K u).mpr hlegal
  obtain ⟨hepole, hopole⟩ := (canonicalPoleExponentialMoments_iff_profiles hL K u).mp ⟨hp, hm⟩
  let elegal : euclideanEvenBoundaryFlatSubspace K :=
    ⟨WithLp.toLp 2 (evenPart K u), (mem_euclideanEvenBoundaryFlatSubspace_iff K _).mpr
      (evenPart_mem_evenBoundaryFlatSubspace hraw)⟩
  let olegal : euclideanOddBoundaryFlatSubspace K :=
    ⟨WithLp.toLp 2 (oddPart K u), (mem_euclideanOddBoundaryFlatSubspace_iff K _).mpr
      (oddPart_mem_oddBoundaryFlatSubspace hraw)⟩
  have hEvenOdd : poleEvenProfile L K ⬝ᵥ oddPart K u = 0 := by
    rw [dotProduct_comm]
    exact dotProduct_eq_zero_of_reverse_odd_even K _ _
      (reverseCoefficients_oddPart K u) (reverseCoefficients_poleEvenProfile L K)
  have hOddEven : poleOddProfile L K ⬝ᵥ evenPart K u = 0 :=
    poleOddProfile_dot_evenBoundaryFlat_eq_zero L K elegal
  have hezero : canonicalPoleEvenFunctional L K elegal = 0 := by
    have hs := congrArg (fun v => poleEvenProfile L K ⬝ᵥ v) (evenPart_add_oddPart K u)
    rw [dotProduct_add, hEvenOdd, add_zero] at hs
    exact hs.trans hepole
  have hozero : canonicalPoleOddFunctional L K olegal = 0 := by
    have hs := congrArg (fun v => poleOddProfile L K ⬝ᵥ v) (evenPart_add_oddPart K u)
    rw [dotProduct_add, hOddEven, zero_add] at hs
    exact hs.trans hopole
  rcases OPICARound2.neutral_negative_parity_split L K u hneg with he | ho
  · left
    apply (evenNeutralNegative_iff_ambient L K).mpr
    refine ⟨elegal, elegal.property, hezero, ?_⟩
    unfold fullCanonicalEnergy
    rw [← quadraticForm_re_eq_re_inner_apply_self]
    exact he
  · right
    apply (oddNeutralNegative_iff_ambient L K).mpr
    refine ⟨olegal, olegal.property, hozero, ?_⟩
    unfold fullCanonicalEnergy
    rw [← quadraticForm_re_eq_re_inner_apply_self]
    exact ho

/-- R3-D01: one actual off-line zero gives a native even-or-odd neutral
negative witness at every sufficiently large aperture. -/
theorem neutral_parity_cover_of_off_line_zero
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ < L →
      ∃ K : ℕ, 3 ≤ K ∧ (EvenNeutralNegative L K ∨ OddNeutralNegative L K) := by
  obtain ⟨L₀, hL₀, hcover⟩ := OPICARound2.eventually_finite_neutral_negative_of_off_line_zero ρ hoff
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL
  obtain ⟨K, hK, u, _, hlegal, hp, hm, hneg, _⟩ := hcover L hL
  exact ⟨K, hK, native_neutral_negative_parity_split (hL₀.trans hL) K u hlegal hp hm hneg⟩

end Zeta23.OPICARound3

#print axioms Zeta23.OPICARound3.native_neutral_negative_parity_split
#print axioms Zeta23.OPICARound3.neutral_parity_cover_of_off_line_zero
