import Zeta23.OPICARound6.NextSearch.SourceEnergies
import Mathlib.Tactic.Ring

/-!
# Same-source bipolar transfer and conditional cofinal equivalences

All cells, cutoffs, labels, weights, centres, targets and spent partners
are the literal native ones. Nothing is asserted about their asymptotic
bounds. The common error tail is an explicit additional hypothesis.
-/

noncomputable section
namespace Zeta23.OPICARound6.NextSearch

open Zeta23.OPICARound6.PrimeFactorPaths
open Zeta23.OPICARound6.PrimeFactorPaths.NativeCells

def survivorPositiveEnergy (X : ℕ) (r : Removal) : ℝ :=
  ∑ j ∈ wholeCoarseKeys X, weight j * (max (survivorCharge X j r) 0)^2

def survivorNegativeEnergy (X : ℕ) (r : Removal) : ℝ :=
  ∑ j ∈ wholeCoarseKeys X, weight j * (max (-survivorCharge X j r) 0)^2

def reverseOpposedSurvivorEnergy (X : ℕ) (r : Removal) : ℝ :=
  ∑ j ∈ wholeCoarseKeys X,
    weight j * (4 * max (oddDeviation X j r) 0 * max (-evenDeviation X j r) 0)

def rawSquareEnergy (X : ℕ) : ℝ :=
  ∑ j ∈ wholeCoarseKeys X,
    weight j * (RoughNodeCharges.charge (roughCutoff X) (rawLabels X j))^2

def survivorSquareEnergy (X : ℕ) (r : Removal) : ℝ :=
  ∑ j ∈ wholeCoarseKeys X, weight j * (survivorCharge X j r)^2

def pairedOpposedSurvivorEnergy (X : ℕ) (r : Removal) : ℝ :=
  opposedSurvivorEnergy X r + reverseOpposedSurvivorEnergy X r

private theorem survivor_abs_le_raw_card (X : ℕ) (j : Key) (r : Removal) :
    |survivorCharge X j r| ≤ ((rawLabels X j).card : ℝ) := by
  unfold survivorCharge survivingLabels
  have hcard : (rawLabels X j \ r.all).card ≤ (rawLabels X j).card :=
    Finset.card_le_card Finset.sdiff_subset
  exact (RoughNodeCharges.abs_charge_le_card (roughCutoff X) _).trans
    (by exact_mod_cast hcard)

private theorem raw_sub_survivor (X : ℕ) (j : Key) (r : Removal) :
    RoughNodeCharges.charge (roughCutoff X) (rawLabels X j) -
        survivorCharge X j r =
      RoughNodeCharges.charge (roughCutoff X) (removedLabels X j r) :=
  RoughNodeCharges.charge_sub_survivors (roughCutoff X) (rawLabels X j) r.all

/-- Both polarities use the identical removal loss, with no symmetry hypothesis
on the arithmetic source. This is a finite same-cell inequality. -/
theorem raw_survivor_polarity_difference (X : ℕ) (r : Removal)
    (pol : ℝ) (hpol : |pol| = 1) :
    |(∑ j ∈ wholeCoarseKeys X,
        weight j * (max (pol * RoughNodeCharges.charge (roughCutoff X) (rawLabels X j)) 0)^2) -
      (∑ j ∈ wholeCoarseKeys X,
        weight j * (max (pol * survivorCharge X j r) 0)^2)| ≤
        completeRemovalCost X r := by
  have h := FiniteSelectorEnergy.weighted_energy_comparison
    (wholeCoarseKeys X) weight
    (fun j => RoughNodeCharges.charge (roughCutoff X) (rawLabels X j))
    (fun j => survivorCharge X j r)
    (fun j => ((rawLabels X j).card : ℝ))
    pol hpol (fun j _ => weight_nonneg j)
    (fun j _ => RoughNodeCharges.abs_charge_le_card (roughCutoff X) (rawLabels X j))
    (fun j _ => survivor_abs_le_raw_card X j r)
  unfold completeRemovalCost
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro j _
  rw [raw_sub_survivor X j r]

theorem reverseOpposedSurvivorEnergy_bracket (X : ℕ) (r : Removal) :
    reverseOpposedSurvivorEnergy X r ≤ survivorNegativeEnergy X r ∧
    survivorNegativeEnergy X r ≤ reverseOpposedSurvivorEnergy X r + unsignedErrorEnergy X := by
  constructor
  · unfold reverseOpposedSurvivorEnergy survivorNegativeEnergy
    apply Finset.sum_le_sum
    intro j _
    rw [NativeStoppingCost.native_opposed_cost_reverse]
    exact mul_le_mul_of_nonneg_left
      (max_le (sub_le_self _ (sq_nonneg _)) (sq_nonneg _)) (weight_nonneg j)
  · unfold reverseOpposedSurvivorEnergy survivorNegativeEnergy unsignedErrorEnergy
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    rw [← mul_add, NativeStoppingCost.native_opposed_cost_reverse]
    apply mul_le_mul_of_nonneg_left _ (weight_nonneg j)
    linarith [le_max_left
      ((max (-survivorCharge X j r) 0)^2 - (unsignedDiscrepancy X j)^2) 0]

/-- The missing finite negative analogue, with both directions of the bracket. -/
theorem rawNegativeEnergy_bracket (X : ℕ) (r : Removal) :
    reverseOpposedSurvivorEnergy X r ≤ rawNegativeEnergy X + completeRemovalCost X r ∧
    rawNegativeEnergy X ≤ reverseOpposedSurvivorEnergy X r +
      unsignedErrorEnergy X + completeRemovalCost X r := by
  have h : |rawNegativeEnergy X - survivorNegativeEnergy X r| ≤ completeRemovalCost X r := by
    simpa only [rawNegativeEnergy, survivorNegativeEnergy, neg_one_mul] using
      raw_survivor_polarity_difference X r (-1) (by norm_num)
  obtain ⟨hl,hu⟩ := abs_le.mp h
  obtain ⟨hp,hq⟩ := reverseOpposedSurvivorEnergy_bracket X r
  constructor <;> linarith

theorem rawNegativeEnergy_le_full_components (X : ℕ) (r : Removal) :
    rawNegativeEnergy X ≤ reverseOpposedSurvivorEnergy X r +
      unsignedErrorEnergy X + completeRemovalCost X r :=
  (rawNegativeEnergy_bracket X r).2

/-- Strengthen the existing positive upper bound by retaining the lower bound. -/
theorem rawPositiveEnergy_bracket (X : ℕ) (r : Removal) :
    opposedSurvivorEnergy X r ≤ rawPositiveEnergy X + completeRemovalCost X r ∧
    rawPositiveEnergy X ≤ opposedSurvivorEnergy X r +
      unsignedErrorEnergy X + completeRemovalCost X r := by
  have h : |rawPositiveEnergy X - survivorPositiveEnergy X r| ≤ completeRemovalCost X r := by
    simpa only [rawPositiveEnergy, survivorPositiveEnergy, one_mul] using
      raw_survivor_polarity_difference X r 1 (by norm_num)
  have hs : opposedSurvivorEnergy X r ≤ survivorPositiveEnergy X r ∧
      survivorPositiveEnergy X r ≤ opposedSurvivorEnergy X r + unsignedErrorEnergy X := by
    simpa only [opposedSurvivorEnergy, survivorPositiveEnergy, unsignedErrorEnergy] using
      native_energy_bracket X r (wholeCoarseKeys X)
  obtain ⟨hl,hu⟩ := abs_le.mp h
  obtain ⟨hp,hq⟩ := hs
  constructor <;> linarith

private theorem square_eq_polarities (a : ℝ) :
    a^2 = (max a 0)^2 + (max (-a) 0)^2 := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha, max_eq_right (neg_nonpos.mpr ha)]
    ring
  · have ha' : a ≤ 0 := le_of_lt (lt_of_not_ge ha)
    rw [max_eq_right ha', max_eq_left (neg_nonneg.mpr ha')]
    ring

theorem rawSquareEnergy_eq_polarities (X : ℕ) :
    rawSquareEnergy X = rawPositiveEnergy X + rawNegativeEnergy X := by
  unfold rawSquareEnergy rawPositiveEnergy rawNegativeEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_add]
  exact congrArg (fun t : ℝ => weight j * t) (square_eq_polarities _)

private theorem abs_square_sub_le (a b H : ℝ) (ha : |a| ≤ H) (hb : |b| ≤ H) :
    |a^2-b^2| ≤ 2*H*|a-b| := by
  have hf : a^2-b^2 = (a+b)*(a-b) := by ring
  rw [hf,abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc
    |a+b| ≤ |a|+|b| := abs_add_le a b
    _ ≤ 2*H := by linarith

/-- The combined square loss is at most one complete removal cost,
not the sum of two separately bounded polarity losses. -/
theorem rawSquareEnergy_removal_bound (X : ℕ) (r : Removal) :
    |rawSquareEnergy X - survivorSquareEnergy X r| ≤ completeRemovalCost X r := by
  unfold rawSquareEnergy survivorSquareEnergy completeRemovalCost
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro j _
  rw [← mul_sub, abs_mul, abs_of_nonneg (weight_nonneg j)]
  apply mul_le_mul_of_nonneg_left _ (weight_nonneg j)
  rw [← raw_sub_survivor X j r]
  exact abs_square_sub_le _ _ _
    (RoughNodeCharges.abs_charge_le_card (roughCutoff X) (rawLabels X j))
    (survivor_abs_le_raw_card X j r)

private theorem max_difference_pair (s d : ℝ) :
    max ((max s 0)^2-d^2) 0 + max ((max (-s) 0)^2-d^2) 0 =
      max (s^2-d^2) 0 := by
  have hz : (0:ℝ)^2-d^2 ≤ 0 := by nlinarith [sq_nonneg d]
  by_cases hs : 0 ≤ s
  · simp only [max_eq_left hs, max_eq_right (neg_nonpos.mpr hs),
      max_eq_right hz, add_zero]
  · have hs' : s ≤ 0 := le_of_lt (lt_of_not_ge hs)
    have hn : (-s)^2 = s^2 := by ring
    simp only [max_eq_right hs', max_eq_left (neg_nonneg.mpr hs'),
      max_eq_right hz, zero_add, hn]

/-- Exact combined cell identity: the two sign contributions never charge the
unsigned error twice in one cell. -/
theorem pairedOpposedSurvivorEnergy_eq (X : ℕ) (r : Removal) :
    pairedOpposedSurvivorEnergy X r =
      ∑ j ∈ wholeCoarseKeys X, weight j *
        max ((survivorCharge X j r)^2-(unsignedDiscrepancy X j)^2) 0 := by
  unfold pairedOpposedSurvivorEnergy opposedSurvivorEnergy reverseOpposedSurvivorEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_add, NativeStoppingCost.native_opposed_cost,
    NativeStoppingCost.native_opposed_cost_reverse]
  exact congrArg (fun t : ℝ => weight j * t) (max_difference_pair _ _)

theorem pairedOpposedSurvivorEnergy_bracket (X : ℕ) (r : Removal) :
    pairedOpposedSurvivorEnergy X r ≤ survivorSquareEnergy X r ∧
    survivorSquareEnergy X r ≤ pairedOpposedSurvivorEnergy X r + unsignedErrorEnergy X := by
  constructor
  · rw [pairedOpposedSurvivorEnergy_eq]
    unfold survivorSquareEnergy
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left
      (max_le (sub_le_self _ (sq_nonneg _)) (sq_nonneg _)) (weight_nonneg j)
  · rw [pairedOpposedSurvivorEnergy_eq]
    unfold survivorSquareEnergy unsignedErrorEnergy
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (weight_nonneg j)
    linarith [le_max_left ((survivorCharge X j r)^2-(unsignedDiscrepancy X j)^2) 0]

/-- A single copy of U and R bounds the total two-sided raw energy.
This is strictly sharper than adding the two separate upper bounds. -/
theorem rawBipolarEnergy_bracket (X : ℕ) (r : Removal) :
    pairedOpposedSurvivorEnergy X r ≤
      rawPositiveEnergy X + rawNegativeEnergy X + completeRemovalCost X r ∧
    rawPositiveEnergy X + rawNegativeEnergy X ≤
      pairedOpposedSurvivorEnergy X r + unsignedErrorEnergy X + completeRemovalCost X r := by
  have h := rawSquareEnergy_removal_bound X r
  rw [rawSquareEnergy_eq_polarities] at h
  obtain ⟨hl,hu⟩ := abs_le.mp h
  obtain ⟨hp,hq⟩ := pairedOpposedSurvivorEnergy_bracket X r
  constructor <;> linarith

theorem unsignedErrorEnergy_nonnegative (X : ℕ) : 0 ≤ unsignedErrorEnergy X := by
  unfold unsignedErrorEnergy
  exact Finset.sum_nonneg fun j _ => mul_nonneg (weight_nonneg j) (sq_nonneg _)

/-- Cofinal means one admissible X beyond every horizon, not a full tail. -/
def CofinalSubpower (f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X₀ : ℕ,
    ∃ X : ℕ, max X₀ 64 ≤ X ∧ f X ≤ C * (X : ℝ)^ε

/-- Uniform tail control is stronger; this is an OPEN arithmetic hypothesis
when applied to the actual unsigned and removal errors. -/
def TailSubpower (f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∃ Y : ℕ,
    ∀ X : ℕ, max Y 64 ≤ X → f X ≤ C * (X : ℝ)^ε

/-- A cofinal estimate may be transported through an eventual error bound.
Two unrelated cofinal witnesses are NOT sufficient. -/
theorem cofinalSubpower_of_tail_error (f g err : ℕ → ℝ)
    (h : ∀ X, f X ≤ g X + err X)
    (hg : CofinalSubpower g) (he : TailSubpower err) : CofinalSubpower f := by
  intro ε hε
  obtain ⟨C,hC,hg'⟩ := hg ε hε
  obtain ⟨D,hD,Y,hY⟩ := he ε hε
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro X₀
  obtain ⟨X,hX,hgX⟩ := hg' (max X₀ Y)
  have hXY : max X₀ Y ≤ X := (le_max_left _ _).trans hX
  have h64 : 64 ≤ X := (le_max_right _ _).trans hX
  refine ⟨X,max_le ((le_max_left _ _).trans hXY) h64,?_⟩
  have hYX : max Y 64 ≤ X := max_le ((le_max_right _ _).trans hXY) h64
  calc
    f X ≤ g X + err X := h X
    _ ≤ C*(X:ℝ)^ε + D*(X:ℝ)^ε := add_le_add hgX (hY X hYX)
    _ = (C+D)*(X:ℝ)^ε := by ring

theorem cofinalSubpower_iff_of_tail_error (f g err : ℕ → ℝ)
    (hfg : ∀ X, f X ≤ g X + err X)
    (hgf : ∀ X, g X ≤ f X + err X)
    (he : TailSubpower err) : CofinalSubpower f ↔ CofinalSubpower g :=
  ⟨fun hf => cofinalSubpower_of_tail_error g f err hgf hf he,
   fun hg => cofinalSubpower_of_tail_error f g err hfg hg he⟩

/-- For a FIXED removal policy, under an explicit uniform remainder budget,
the positive cofinal source estimate is equivalent to its survivor estimate. -/
theorem positiveRawSubpower_iff_opposed_of_tail_error (r : ℕ → Removal)
    (he : TailSubpower (fun X => unsignedErrorEnergy X + completeRemovalCost X (r X))) :
    PositiveRawSubpower ↔ CofinalSubpower (fun X => opposedSurvivorEnergy X (r X)) := by
  change CofinalSubpower rawPositiveEnergy ↔ _
  refine cofinalSubpower_iff_of_tail_error _ _ _ ?_ ?_ he
  · intro X
    linarith [(rawPositiveEnergy_bracket X (r X)).2]
  · intro X
    linarith [(rawPositiveEnergy_bracket X (r X)).1, unsignedErrorEnergy_nonnegative X]

/-- Identical conditional reduction for the negative polarity. -/
theorem negativeRawSubpower_iff_opposed_of_tail_error (r : ℕ → Removal)
    (he : TailSubpower (fun X => unsignedErrorEnergy X + completeRemovalCost X (r X))) :
    NegativeRawSubpower ↔ CofinalSubpower (fun X => reverseOpposedSurvivorEnergy X (r X)) := by
  change CofinalSubpower rawNegativeEnergy ↔ _
  refine cofinalSubpower_iff_of_tail_error _ _ _ ?_ ?_ he
  · intro X
    linarith [(rawNegativeEnergy_bracket X (r X)).2]
  · intro X
    linarith [(rawNegativeEnergy_bracket X (r X)).1, unsignedErrorEnergy_nonnegative X]

/-- Polarity selection remains OUTSIDE the epsilon and horizon quantifiers.
This is conditional on the same fixed removal policy's tail remainder. -/
theorem onePolarityRawSubpower_iff_opposed_of_tail_error (r : ℕ → Removal)
    (he : TailSubpower (fun X => unsignedErrorEnergy X + completeRemovalCost X (r X))) :
    OnePolarityRawSubpower ↔
      (CofinalSubpower (fun X => opposedSurvivorEnergy X (r X)) ∨
       CofinalSubpower (fun X => reverseOpposedSurvivorEnergy X (r X))) := by
  unfold OnePolarityRawSubpower
  exact or_congr (positiveRawSubpower_iff_opposed_of_tail_error r he)
    (negativeRawSubpower_iff_opposed_of_tail_error r he)

end Zeta23.OPICARound6.NextSearch
