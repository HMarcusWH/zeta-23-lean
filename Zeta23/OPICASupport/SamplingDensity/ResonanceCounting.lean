import Zeta23.Defs.Counting
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A linear bound for exponential resonances

The exceptional set is the full exponential-zero lattice.  The counting argument
uses distinct complex points and does not require that the zero configuration
lie on the critical line.
-/

noncomputable section

namespace Zeta23.OPICARound20

open scoped BigOperators

def resonancePoint (L : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) * (2 * Real.pi * Complex.I) / (L : ℂ) + 1 / 2

def resonanceGrid (L U : ℝ) : Finset ℂ :=
  (Finset.range (Nat.ceil (U * L / (2 * Real.pi)) + 1)).image (resonancePoint L)

theorem gammaOf_injective : Function.Injective gammaOf := by
  intro ρ σ h
  simpa only [gammaOf, div_left_inj' Complex.I_ne_zero, sub_left_inj] using h

theorem exponential_gamma_argument (L : ℝ) (ρ : ℂ) :
    Complex.I * gammaOf ρ * (L : ℂ) = (ρ - 1 / 2) * (L : ℂ) := by
  unfold gammaOf
  calc
    Complex.I * ((ρ - 1 / 2) / Complex.I) * (L : ℂ) =
        (((ρ - 1 / 2) / Complex.I) * Complex.I) * (L : ℂ) := by ring
    _ = (ρ - 1 / 2) * (L : ℂ) := by rw [div_mul_cancel₀ _ Complex.I_ne_zero]

theorem resonance_mem_grid_of_ordinate_bounds
    {L U : ℝ} (hL : 0 < L) (ρ : ℂ) (hρ0 : 0 ≤ ρ.im) (hρU : ρ.im ≤ U)
    (hexp : Complex.exp (Complex.I * gammaOf ρ * (L : ℂ)) = 1) :
    ρ ∈ resonanceGrid L U := by
  have harg := exponential_gamma_argument L ρ
  have him : 0 ≤ (Complex.I * gammaOf ρ * (L : ℂ)).im := by
    rw [harg]
    simpa using mul_nonneg hρ0 hL.le
  obtain ⟨n, hn⟩ := (Complex.exp_eq_one_iff_of_im_nonneg him).mp hexp
  rw [harg] at hn
  have hnreal : (n : ℝ) * (2 * Real.pi) = ρ.im * L := by
    have hi := congrArg Complex.im hn
    simpa using hi.symm
  have hnle : (n : ℝ) ≤ U * L / (2 * Real.pi) := by
    apply (le_div_iff₀ Real.two_pi_pos).mpr
    rw [hnreal]
    exact mul_le_mul_of_nonneg_right hρU hL.le
  have hnceil : n ≤ Nat.ceil (U * L / (2 * Real.pi)) := by
    exact_mod_cast hnle.trans (Nat.le_ceil (U * L / (2 * Real.pi)))
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hpoint : ρ = resonancePoint L n := by
    have heq : ρ - 1 / 2 = (n : ℂ) * (2 * Real.pi * Complex.I) / (L : ℂ) :=
      (eq_div_iff hLc).mpr hn
    exact sub_eq_iff_eq_add.mp heq
  exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hnceil), hpoint.symm⟩

theorem resonanceGrid_card_lt_linear {L U : ℝ} (hL : 0 < L) (hU : 0 ≤ U) :
    ((resonanceGrid L U).card : ℝ) < U * L / (2 * Real.pi) + 2 := by
  have hc : (resonanceGrid L U).card ≤ Nat.ceil (U * L / (2 * Real.pi)) + 1 := by
    exact (Finset.card_image_le).trans_eq (Finset.card_range _)
  have hc' : ((resonanceGrid L U).card : ℝ) ≤
      (Nat.ceil (U * L / (2 * Real.pi)) : ℝ) + 1 := by exact_mod_cast hc
  have hx : 0 ≤ U * L / (2 * Real.pi) :=
    div_nonneg (mul_nonneg hU hL.le) Real.two_pi_pos.le
  have hceil := Nat.ceil_lt_add_one hx
  linarith

/-- A precise minimal counting supplier: distinct dyadic window counts exceed
every linear function at some positive height.  Multiplicity counts do not suffice. -/
def DistinctWindowSuperlinear (Z : ZeroConfig) : Prop :=
  ∀ c b : ℝ, ∃ T : ℝ, 0 < T ∧ c * T + b < (Z.Nd T (2 * T) : ℝ)

def nonresonantZeroSet (Z : ZeroConfig) (L : ℝ) : Set ℂ :=
  {ρ | ρ ∈ Z.carrier ∧ Complex.exp (Complex.I * gammaOf ρ * (L : ℂ)) ≠ 1}

/-- Superlinear distinct-zero growth supplies infinitely many points outside
the complete exponential-zero lattice, for each fixed positive aperture. -/
theorem nonresonantZeroSet_infinite_of_distinct_growth
    (Z : ZeroConfig) (hgrowth : DistinctWindowSuperlinear Z) {L : ℝ} (hL : 0 < L) :
    (nonresonantZeroSet Z L).Infinite := by
  classical
  intro hs
  let s := hs.toFinset
  obtain ⟨T, hT, hcount⟩ := hgrowth (L / Real.pi) ((s.card : ℝ) + 2)
  let A := (Z.finite_window T (2 * T)).toFinset
  have hsubset : A ⊆ s ∪ resonanceGrid L (2 * T) := by
    intro ρ hρ
    have hwindow : ρ ∈ Z.window T (2 * T) := by
      simpa only [A, Set.Finite.mem_toFinset, ZeroConfig.window] using hρ
    by_cases hexp : Complex.exp (Complex.I * gammaOf ρ * (L : ℂ)) = 1
    · apply Finset.mem_union.mpr
      right
      apply resonance_mem_grid_of_ordinate_bounds hL ρ _ hwindow.2.2 hexp
      linarith [hwindow.2.1]
    · apply Finset.mem_union.mpr
      left
      simpa only [s, Set.Finite.mem_toFinset, nonresonantZeroSet, Set.mem_ofPred_eq]
        using (show ρ ∈ Z.carrier ∧
          Complex.exp (Complex.I * gammaOf ρ * (L : ℂ)) ≠ 1 from ⟨hwindow.1, hexp⟩)
  have hcard : Z.Nd T (2 * T) ≤ s.card + (resonanceGrid L (2 * T)).card := by
    calc
      Z.Nd T (2 * T) = A.card :=
        Set.ncard_eq_toFinset_card _ (Z.finite_window T (2 * T))
      _ ≤ (s ∪ resonanceGrid L (2 * T)).card := Finset.card_le_card hsubset
      _ ≤ s.card + (resonanceGrid L (2 * T)).card := Finset.card_union_le _ _
  have hcard' : (Z.Nd T (2 * T) : ℝ) ≤
      (s.card : ℝ) + ((resonanceGrid L (2 * T)).card : ℝ) := by exact_mod_cast hcard
  have hgrid := resonanceGrid_card_lt_linear hL (show 0 ≤ 2 * T by positivity)
  have hlin : (2 * T) * L / (2 * Real.pi) = (L / Real.pi) * T := by ring
  rw [hlin] at hgrid
  linarith

/-- Any desired finite number of distinct actual configuration points can then
be chosen, with their `gammaOf` coordinates also distinct. -/
theorem exists_nonresonant_zero_samples_of_distinct_growth
    (Z : ZeroConfig) (hgrowth : DistinctWindowSuperlinear Z) {L : ℝ} (hL : 0 < L)
    (n : ℕ) :
    ∃ ρ : Fin n → Z.carrier, Function.Injective (fun j => gammaOf (ρ j)) ∧
      ∀ j, Complex.exp (Complex.I * gammaOf (ρ j) * (L : ℂ)) ≠ 1 := by
  let e := Set.Infinite.natEmbedding (nonresonantZeroSet Z L)
    (nonresonantZeroSet_infinite_of_distinct_growth Z hgrowth hL)
  let ρ : Fin n → Z.carrier := fun j => ⟨(e j).val, (e j).property.1⟩
  refine ⟨ρ, ?_, ?_⟩
  · intro i j hij
    apply Fin.val_injective
    apply e.injective
    apply Subtype.ext
    exact gammaOf_injective hij
  · exact fun j => (e j).property.2

end Zeta23.OPICARound20
