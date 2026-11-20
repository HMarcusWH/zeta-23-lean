import Zeta23.OPICARound6.PrimeFactorPaths.ParityDeficitProduct
import Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The occupied native grid and its unsigned parity discrepancy on a fixed integer horizon.
The upper endpoint is included, the lower terminal inequality is strict, and the full cell
width used in the center is the underlying dyadic width. The complete-shell restriction
is available separately. No assertion about the size of the unsigned discrepancy or the
quality of a matching is needed for the finite statements.
-/

noncomputable section
open scoped Classical ArithmeticFunction.Moebius
namespace Zeta23.OPICARound6.PrimeFactorPaths.NativeCells
open Zeta23.OPICARound6.PrimeFactorPaths

def roughCutoff (X : ℕ) : ℕ :=
  (if X ≤ 1 then 0 else (X-1).log2+1)^2

def baseShift (X : ℕ) : ℕ :=
  let j := X.log2
  let t := j.sqrt
  if t*t < j then t+1 else t

structure Key where
  shell : ℕ
  depth : ℕ
  index : ℕ
  deriving DecidableEq

def width (X : ℕ) (j k : ℕ) : ℕ := 2^(j-baseShift X-k)

def keyOf (X n k : ℕ) : Key :=
  ⟨n.log2, k, n / width X n.log2 k⟩

def levels (X n : ℕ) : Finset ℕ :=
  Finset.range (n.log2 + 1 - baseShift X)

def terminalLabels (X : ℕ) : Finset ℕ :=
  (Finset.range (X+1)).filter fun n =>
    X^99 < n^100 ∧ Squarefree n ∧ ∀ p ∈ n.primeFactors, roughCutoff X < p

def rawLabels (X : ℕ) (j : Key) : Finset ℕ :=
  (terminalLabels X).filter fun n => j.depth ∈ levels X n ∧ keyOf X n j.depth = j

def occupiedKeys (X : ℕ) : Finset Key :=
  (terminalLabels X).biUnion fun n => (levels X n).image (keyOf X n)

def coarse (X : ℕ) (j : Key) : Prop := 2*j.depth < j.shell-baseShift X

/-- Every integer of the half-open shell [2^j,2^(j+1)) passes the actual terminal gates. -/
def completeShell (X j : ℕ) : Prop := X^99 < (2^j)^100 ∧ 2^(j+1) ≤ X+1

def wholeCoarseKeys (X : ℕ) : Finset Key :=
  (occupiedKeys X).filter fun j => coarse X j ∧ completeShell X j.shell

def weight (j : Key) : ℝ := 1 / (2:ℝ)^(j.shell+j.depth)

theorem mem_terminalLabels (X n : ℕ) :
    n ∈ terminalLabels X ↔ n ≤ X ∧ X^99 < n^100 ∧ Squarefree n ∧
      ∀ p ∈ n.primeFactors, roughCutoff X < p := by
  simp [terminalLabels]

theorem mem_rawLabels (X : ℕ) (j : Key) (n : ℕ) :
    n ∈ rawLabels X j ↔ n ∈ terminalLabels X ∧ j.depth+baseShift X ≤ n.log2 ∧
      keyOf X n j.depth = j := by
  simp only [rawLabels, Finset.mem_filter, levels, Finset.mem_range,
    Nat.lt_sub_iff_add_lt, Nat.lt_succ_iff]

theorem mem_occupiedKeys (X : ℕ) (j : Key) :
    j ∈ occupiedKeys X ↔ (rawLabels X j).Nonempty := by
  constructor
  · intro h
    obtain ⟨n, hn, himage⟩ := Finset.mem_biUnion.mp h
    obtain ⟨k, hlevel, hj⟩ := Finset.mem_image.mp himage
    subst j
    exact ⟨n, Finset.mem_filter.mpr ⟨hn, hlevel, rfl⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨hn, hk, hj⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_biUnion.mpr ⟨n, hn, Finset.mem_image.mpr ⟨j.depth, hk, hj⟩⟩

theorem weight_nonneg (j : Key) : 0 ≤ weight j := by unfold weight; positivity

theorem aligned_index_iff (X n j k i : ℕ) :
    n / width X j k = i ↔ i * width X j k ≤ n ∧ n < (i+1) * width X j k := by
  have hpos : 0 < width X j k := by unfold width; positivity
  rw [Nat.div_eq_iff hpos, Nat.add_one_mul]
  omega

structure Removal where
  targets : Finset ℕ
  spentPartners : Finset ℕ

def Removal.all (r : Removal) : Finset ℕ := r.targets ∪ r.spentPartners

def removedLabels (X : ℕ) (j : Key) (r : Removal) := rawLabels X j ∩ r.all
def survivingLabels (X : ℕ) (j : Key) (r : Removal) := rawLabels X j \ r.all

def coneTargets (X cap : ℕ) : Finset ℕ :=
  (terminalLabels X).filter fun n => n / max 1 (n.primeFactors.sup id) ≤ cap

def evenPopulation (X : ℕ) (j : Key) (r : Removal) : ℕ :=
  ((survivingLabels X j r).filter fun n => Even n.primeFactors.card).card
def oddPopulation (X : ℕ) (j : Key) (r : Removal) : ℕ :=
  ((survivingLabels X j r).filter fun n => ¬Even n.primeFactors.card).card

/-- Real reciprocal of the absolutely convergent zeta(2) series times the finite prime product. -/
def density (X : ℕ) : ℝ :=
  (∑' n : ℕ, 1/((n:ℝ)+1)^2)⁻¹ *
    ∏ p ∈ Nat.primesLE (roughCutoff X), (p:ℝ) / (p+1)

def center (X : ℕ) (j : Key) (r : Removal) : ℝ :=
  ((width X j.shell j.depth : ℝ)*density X - (removedLabels X j r).card)/2
def evenDeviation (X : ℕ) (j : Key) (r : Removal) : ℝ := evenPopulation X j r - center X j r
def oddDeviation (X : ℕ) (j : Key) (r : Removal) : ℝ := oddPopulation X j r - center X j r
def unsignedDiscrepancy (X : ℕ) (j : Key) : ℝ :=
  (rawLabels X j).card - (width X j.shell j.depth : ℝ)*density X
def survivorCharge (X : ℕ) (j : Key) (r : Removal) : ℝ :=
  RoughNodeCharges.charge (roughCutoff X) (survivingLabels X j r)

theorem survivor_sign (X : ℕ) (j : Key) (r : Removal) {n : ℕ}
    (hn : n ∈ survivingLabels X j r) :
    RoughNodeCharges.roughSign (roughCutoff X) n =
      if Even n.primeFactors.card then (1:ℝ) else -1 := by
  have hraw : n ∈ rawLabels X j := (Finset.mem_sdiff.mp hn).1
  have ht := (mem_terminalLabels X n).mp ((mem_rawLabels X j n).mp hraw).1
  have hcard : ArithmeticFunction.cardFactors n = n.primeFactors.card := by
    rw [← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree ht.2.2.1.ne_zero).mpr ht.2.2.1,
      ArithmeticFunction.cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]
  rw [RoughNodeCharges.roughSign, if_pos ht.2.2.2,
    ArithmeticFunction.moebius_apply_of_squarefree ht.2.2.1, Int.cast_pow, Int.cast_neg,
    Int.cast_one, hcard, neg_one_pow_eq_ite]

theorem survivorCharge_eq_counts (X : ℕ) (j : Key) (r : Removal) :
    survivorCharge X j r = (evenPopulation X j r : ℝ) - oddPopulation X j r := by
  unfold survivorCharge RoughNodeCharges.charge evenPopulation oddPopulation
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [survivor_sign X j r hn]
  by_cases he : Even n.primeFactors.card <;> simp [he]

theorem count_conservation (X : ℕ) (j : Key) (r : Removal) :
    evenPopulation X j r + oddPopulation X j r + (removedLabels X j r).card =
      (rawLabels X j).card := by
  unfold evenPopulation oddPopulation
  rw [Finset.card_filter_add_card_filter_not]
  exact Finset.card_sdiff_add_card_inter _ _

theorem deviation_difference (X : ℕ) (j : Key) (r : Removal) :
    evenDeviation X j r - oddDeviation X j r = survivorCharge X j r := by
  rw [survivorCharge_eq_counts]
  unfold evenDeviation oddDeviation
  ring

theorem deviation_sum (X : ℕ) (j : Key) (r : Removal) :
    evenDeviation X j r + oddDeviation X j r = unsignedDiscrepancy X j := by
  have h : (evenPopulation X j r : ℝ) + oddPopulation X j r + (removedLabels X j r).card =
      (rawLabels X j).card := by exact_mod_cast count_conservation X j r
  unfold evenDeviation oddDeviation center unsignedDiscrepancy
  linarith

theorem weighted_deficit_transfer (X : ℕ) (r : Removal) (nodes : Finset Key) :
    (∑ j ∈ nodes, weight j * |(max (survivorCharge X j r) 0)^2 -
       4 * max (evenDeviation X j r) 0 * max (-oddDeviation X j r) 0|) ≤
      ∑ j ∈ nodes, weight j * (unsignedDiscrepancy X j)^2 := by
  have h := ParityDeficitProduct.weighted_absolute_remainder nodes
    (fun j => evenDeviation X j r) (fun j => oddDeviation X j r) weight
    (fun j _ => weight_nonneg j)
  simpa only [deviation_difference, deviation_sum] using h

/-- The actual occupied coarse nodes of complete shells use exactly the generator weights. -/
theorem whole_coarse_deficit_transfer (X : ℕ) (r : Removal) :
    (∑ j ∈ wholeCoarseKeys X, weight j * |(max (survivorCharge X j r) 0)^2 -
       4 * max (evenDeviation X j r) 0 * max (-oddDeviation X j r) 0|) ≤
      ∑ j ∈ wholeCoarseKeys X, weight j * (unsignedDiscrepancy X j)^2 :=
  weighted_deficit_transfer X r _

/-- Lower and upper controls on the actual one-sided energy over the same finite cells. -/
theorem native_energy_bracket (X : ℕ) (r : Removal) (nodes : Finset Key) :
    let P := ∑ j ∈ nodes, weight j *
      (4 * max (evenDeviation X j r) 0 * max (-oddDeviation X j r) 0)
    let E := ∑ j ∈ nodes, weight j * (max (survivorCharge X j r) 0)^2
    let U := ∑ j ∈ nodes, weight j * (unsignedDiscrepancy X j)^2
    P ≤ E ∧ E ≤ P + U := by
  dsimp only
  constructor
  · apply Finset.sum_le_sum
    intro j _
    obtain ⟨hl, _⟩ := ParityDeficitProduct.quadrant_remainder (evenDeviation X j r) (oddDeviation X j r)
    rw [deviation_difference] at hl
    exact mul_le_mul_of_nonneg_left (sub_nonneg.mp hl) (weight_nonneg j)
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    obtain ⟨_, hu⟩ := ParityDeficitProduct.quadrant_remainder (evenDeviation X j r) (oddDeviation X j r)
    rw [deviation_difference, deviation_sum] at hu
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith) (weight_nonneg j)

end Zeta23.OPICARound6.PrimeFactorPaths.NativeCells
