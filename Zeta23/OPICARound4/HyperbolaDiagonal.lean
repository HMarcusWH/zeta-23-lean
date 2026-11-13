import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
open Finset

namespace Zeta23.OPICARound4

def aliasDiagonal (R : ℝ → ℝ) (x : ℝ) (Y : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 Y, (ArithmeticFunction.moebius a : ℝ) ^ 2 * R (x / (a : ℝ) ^ 2)

theorem abs_aliasDiagonal_le_count
    (R : ℝ → ℝ) (x M : ℝ) (Y : ℕ) (hM : 0 ≤ M)
    (hR : ∀ a ∈ Icc 1 Y, |R (x / (a : ℝ) ^ 2)| ≤ M) :
    |aliasDiagonal R x Y| ≤ M * Y := by
  unfold aliasDiagonal
  calc
    |∑ a ∈ Icc 1 Y, (ArithmeticFunction.moebius a : ℝ) ^ 2 * R (x / (a : ℝ) ^ 2)|
      ≤ ∑ a ∈ Icc 1 Y, |(ArithmeticFunction.moebius a : ℝ) ^ 2 * R (x / (a : ℝ) ^ 2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Icc 1 Y, M := by
      apply Finset.sum_le_sum
      intro a ha
      have hmu : |(ArithmeticFunction.moebius a : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a)
      have hmusq : (ArithmeticFunction.moebius a : ℝ) ^ 2 ≤ 1 := by
        have hbounds := abs_le.mp hmu
        nlinarith [sq_nonneg (ArithmeticFunction.moebius a : ℝ)]
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      calc
        (ArithmeticFunction.moebius a : ℝ) ^ 2 * |R (x / (a : ℝ) ^ 2)|
          ≤ 1 * |R (x / (a : ℝ) ^ 2)| :=
            mul_le_mul_of_nonneg_right hmusq (abs_nonneg _)
        _ ≤ M := by simpa using hR a ha
    _ = M * Y := by simp [mul_comm]

theorem abs_aliasDiagonal_le_sqrt
    (R : ℝ → ℝ) {T x M : ℝ} (hT : 0 < T) (hx : 0 < x) (hM : 0 ≤ M)
    (hR : ∀ y : ℝ, 1 / T ≤ y → |R y| ≤ M) :
    |aliasDiagonal R x ⌊Real.sqrt (T * x)⌋₊| ≤ (M * Real.sqrt T) * Real.sqrt x := by
  let Y : ℕ := ⌊Real.sqrt (T * x)⌋₊
  have hY : (Y : ℝ) ≤ Real.sqrt (T * x) := Nat.floor_le (Real.sqrt_nonneg _)
  have hYnonneg : 0 ≤ (Y : ℝ) := Nat.cast_nonneg _
  have hYsq : (Y : ℝ) ^ 2 ≤ T * x := by
    nlinarith [Real.sq_sqrt (mul_nonneg hT.le hx.le), Real.sqrt_nonneg (T * x)]
  have hlocal : ∀ a ∈ Icc 1 Y, |R (x / (a : ℝ) ^ 2)| ≤ M := by
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have haY : a ≤ Y := (Finset.mem_Icc.mp ha).2
    have haPos : (0 : ℝ) < a := by exact_mod_cast (Nat.zero_lt_of_lt ha1)
    have haYreal : (a : ℝ) ≤ Y := by exact_mod_cast haY
    apply hR
    apply (div_le_div_iff₀ hT (sq_pos_of_pos haPos)).mpr
    nlinarith
  calc
    |aliasDiagonal R x Y| ≤ M * Y := abs_aliasDiagonal_le_count R x M Y hM hlocal
    _ ≤ M * Real.sqrt (T * x) := mul_le_mul_of_nonneg_left hY hM
    _ = (M * Real.sqrt T) * Real.sqrt x := by rw [Real.sqrt_mul hT.le]; ring

theorem lower_bound_remove_bounded_diagonal
    {total combined diagonal scale C D : ℝ}
    (hidentity : total = combined + diagonal)
    (hdiag : |diagonal| ≤ D * scale)
    (htotal : -(C * scale) ≤ total) :
    -((C + D) * scale) ≤ combined := by
  have hd := (abs_le.mp hdiag).2
  nlinarith

theorem lower_bound_restore_bounded_diagonal
    {total combined diagonal scale C D : ℝ}
    (hidentity : total = combined + diagonal)
    (hdiag : |diagonal| ≤ D * scale)
    (hcombined : -(C * scale) ≤ combined) :
    -((C + D) * scale) ≤ total := by
  have hd := (abs_le.mp hdiag).1
  nlinarith


/-- The actual Mobius-weighted Poisson remainder, with every ordered pair retained. -/
def mobiusPoissonRemainder (R : ℝ → ℝ) (x : ℝ) (Y : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 Y, ∑ b ∈ Icc 1 Y,
    (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
      R (x / ((a : ℝ) * (b : ℝ)))

/-- Only the diagonal is removed; no coprimality or sign simplification is made. -/
def mobiusPoissonOffDiagonal (R : ℝ → ℝ) (x : ℝ) (Y : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 Y, ∑ b ∈ (Icc 1 Y).erase a,
    (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
      R (x / ((a : ℝ) * (b : ℝ)))

def mobiusReciprocalSum (Y : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 Y, (ArithmeticFunction.moebius a : ℝ) / (a : ℝ)

/-- The helpful continuum rank-one term is retained in the remaining target. -/
def mobiusPoissonRankOne (I x : ℝ) (Y : ℕ) : ℝ :=
  I * x * mobiusReciprocalSum Y ^ 2

def mobiusPoissonQuadratic (P : ℝ → ℝ) (x : ℝ) (Y : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 Y, ∑ b ∈ Icc 1 Y,
    (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
      P (x / ((a : ℝ) * (b : ℝ)))

theorem mobiusPoissonRemainder_eq_diagonal_add_offDiagonal
    (R : ℝ → ℝ) (x : ℝ) (Y : ℕ) :
    mobiusPoissonRemainder R x Y =
      aliasDiagonal R x Y + mobiusPoissonOffDiagonal R x Y := by
  unfold mobiusPoissonRemainder aliasDiagonal mobiusPoissonOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have he := (Finset.add_sum_erase (Icc 1 Y)
    (fun b => (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
      R (x / ((a : ℝ) * (b : ℝ)))) ha).symm
  simpa only [pow_two] using he

theorem mobiusPoissonRankOne_nonneg {I x : ℝ} (hI : 0 ≤ I) (hx : 0 ≤ x) (Y : ℕ) :
    0 ≤ mobiusPoissonRankOne I x Y := by
  exact mul_nonneg (mul_nonneg hI hx) (sq_nonneg _)

theorem mobiusPoissonQuadratic_eq_rankOne_add_remainder
    (P R : ℝ → ℝ) (I x : ℝ) (Y : ℕ)
    (hP : ∀ y : ℝ, P y = I * y + R y) :
    mobiusPoissonQuadratic P x Y =
      mobiusPoissonRankOne I x Y + mobiusPoissonRemainder R x Y := by
  unfold mobiusPoissonQuadratic mobiusPoissonRemainder mobiusPoissonRankOne mobiusReciprocalSum
  simp_rw [hP, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [pow_two, Finset.sum_mul_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem mobiusPoissonQuadratic_eq_rankOne_offDiagonal_add_diagonal
    (P R : ℝ → ℝ) (I x : ℝ) (Y : ℕ)
    (hP : ∀ y : ℝ, P y = I * y + R y) :
    mobiusPoissonQuadratic P x Y =
      (mobiusPoissonRankOne I x Y + mobiusPoissonOffDiagonal R x Y) +
        aliasDiagonal R x Y := by
  rw [mobiusPoissonQuadratic_eq_rankOne_add_remainder P R I x Y hP,
    mobiusPoissonRemainder_eq_diagonal_add_offDiagonal]
  ring

/-- Constants and the threshold are chosen before the real observation scale. -/
def HasEventualSqrtLower (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ X0 : ℝ, 0 < X0 ∧
    ∀ x : ℝ, X0 ≤ x → -(C * Real.sqrt x) ≤ f x

/-- An exact equivalence of the two OPEN lower-bound targets. It proves neither target.
The bounded-remainder premise must be established for the literal analytic remainder. -/
theorem eventual_sqrt_lower_poisson_iff_rankOne_offDiagonal
    (P R : ℝ → ℝ) (I : ℝ) {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M)
    (hP : ∀ y : ℝ, P y = I * y + R y)
    (hR : ∀ y : ℝ, 1 / T ≤ y → |R y| ≤ M) :
    HasEventualSqrtLower (fun x => mobiusPoissonQuadratic P x ⌊Real.sqrt (T*x)⌋₊) ↔
      HasEventualSqrtLower (fun x =>
        mobiusPoissonRankOne I x ⌊Real.sqrt (T*x)⌋₊ +
          mobiusPoissonOffDiagonal R x ⌊Real.sqrt (T*x)⌋₊) := by
  constructor
  · rintro ⟨C,hC,X0,hX0,hbound⟩
    refine ⟨C + M * Real.sqrt T, by positivity, X0, hX0, ?_⟩
    intro x hx
    exact lower_bound_remove_bounded_diagonal
      (mobiusPoissonQuadratic_eq_rankOne_offDiagonal_add_diagonal P R I x _ hP)
      (abs_aliasDiagonal_le_sqrt R hT (hX0.trans_le hx) hM hR) (hbound x hx)
  · rintro ⟨C,hC,X0,hX0,hbound⟩
    refine ⟨C + M * Real.sqrt T, by positivity, X0, hX0, ?_⟩
    intro x hx
    exact lower_bound_restore_bounded_diagonal
      (mobiusPoissonQuadratic_eq_rankOne_offDiagonal_add_diagonal P R I x _ hP)
      (abs_aliasDiagonal_le_sqrt R hT (hX0.trans_le hx) hM hR) (hbound x hx)

end Zeta23.OPICARound4

