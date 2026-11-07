import Zeta23.CCM.CanonicalApertureComplexSource
import Mathlib.Analysis.Meromorphic.Basic

noncomputable section
namespace Zeta23.OPICARound4.PrimeSourceLaurent
open CCM Complex Matrix
open scoped BigOperators

/-- The phase of the actual integer q. Primality and prime-power relations are
retained by later evaluation; no independent phase is assigned here. -/
def integerPhase (q : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * (Real.log q : ℂ) * Complex.I / z)

theorem integerPhase_ne_zero (q : ℕ) (z : ℂ) : integerPhase q z ≠ 0 :=
  Complex.exp_ne_zero _

theorem exp_source_angle (q : ℕ) (z : ℂ) (n : ℤ) :
    Complex.exp ((2 * (Real.pi : ℂ) * (n : ℂ) *
      complexPrimeSourceCoordinate q z) * Complex.I) = integerPhase q z ^ (-n) := by
  have harg : (2 * (Real.pi : ℂ) * (n : ℂ) *
      complexPrimeSourceCoordinate q z) * Complex.I =
      (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
        ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * (Real.log q : ℂ) * Complex.I / z) := by
    simp only [complexPrimeSourceCoordinate, Int.cast_neg]
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    Complex.exp_int_mul, one_mul]
  rfl

theorem exp_neg_source_angle (q : ℕ) (z : ℂ) (n : ℤ) :
    Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) *
      complexPrimeSourceCoordinate q z) * Complex.I) = integerPhase q z ^ n := by
  simpa only [Int.cast_neg, mul_neg, neg_mul, neg_neg] using exp_source_angle q z (-n)

/-- Exact potential, with its orientation inherited from omega = 1-log(q)/z. -/
theorem potential_laurent (q : ℕ) (z : ℂ) (n : ℤ) :
    complexSourcePotential (complexPrimeSourceCoordinate q z) n =
      (integerPhase q z ^ n - integerPhase q z ^ (-n)) * Complex.I /
        (2 * (Real.pi : ℂ)) := by
  unfold complexSourcePotential Complex.sin
  rw [exp_neg_source_angle, exp_source_angle]
  ring

/-- The z-dependent diagonal coefficient is retained in full. -/
theorem diagonal_laurent (q : ℕ) (z : ℂ) (n : ℤ) :
    complexSourceDiagonal (complexPrimeSourceCoordinate q z) n =
      (1 - (Real.log q : ℂ) / z) *
        (integerPhase q z ^ (-n) + integerPhase q z ^ n) := by
  unfold complexSourceDiagonal Complex.cos
  rw [exp_source_angle, exp_neg_source_angle]
  unfold complexPrimeSourceCoordinate
  ring

def formalPrimePotential (X : ℂ) (n : ℤ) : ℂ :=
  (X ^ n - X ^ (-n)) * Complex.I / (2 * (Real.pi : ℂ))

def formalPrimeDiagonal (q : ℕ) (z X : ℂ) (n : ℤ) : ℂ :=
  (1 - (Real.log q : ℂ) / z) * (X ^ (-n) + X ^ n)

def formalPrimeMatrix (q : ℕ) (z X : ℂ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  dividedDifferenceMatrix (formalPrimePotential X) (formalPrimeDiagonal q z X) K

theorem formalPrimeMatrix_actual (q : ℕ) (z : ℂ) (K : ℕ) :
    formalPrimeMatrix q z (integerPhase q z) K =
      complexSourceMatrix (complexPrimeSourceCoordinate q z) K := by
  have hp : formalPrimePotential (integerPhase q z) =
      complexSourcePotential (complexPrimeSourceCoordinate q z) := by
    funext n
    exact (potential_laurent q z n).symm
  have hd : formalPrimeDiagonal q z (integerPhase q z) =
      complexSourceDiagonal (complexPrimeSourceCoordinate q z) := by
    funext n
    exact (diagonal_laurent q z n).symm
  simp only [formalPrimeMatrix, hp, hd, complexSourceMatrix]

theorem formalPrimeMatrix_one (q : ℕ) (z : ℂ) (K : ℕ) :
    formalPrimeMatrix q z 1 K =
      (2 * (1 - (Real.log q : ℂ) / z)) • (1 : Matrix _ _ ℂ) := by
  ext i j
  simp only [formalPrimeMatrix, dividedDifferenceMatrix, dividedDifferenceEntry,
    formalPrimePotential, formalPrimeDiagonal, _root_.one_zpow, sub_self, zero_mul,
    zero_div, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j
  · subst j
    simp
    ring
  · have hc : centeredIndex K i ≠ centeredIndex K j := by
      exact fun e => h (centeredIndex_injective K e)
    simp [h, hc]

theorem frozenPrimeMatrix_laurent (Q K : ℕ) (z : ℂ) :
    complexFrozenCanonicalPrimeMatrix Q z K =
      ∑ q ∈ Finset.Icc 2 Q,
        primeSourceWeight q • formalPrimeMatrix q z (integerPhase q z) K := by
  simp only [formalPrimeMatrix_actual, complexFrozenCanonicalPrimeMatrix]

/-- Polynomial continuation of z times the exactly scalar-subtracted prime
atom. This is defined at zero, where the original phase is only a formal input. -/
def scaledPrimeMatrix (q : ℕ) (z X : ℂ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  dividedDifferenceMatrix (fun n => z * formalPrimePotential X n)
    (fun n => (z - (Real.log q : ℂ)) * (X ^ (-n) + X ^ n - 2)) K

theorem scaledPrimeMatrix_eq (q : ℕ) {z : ℂ} (hz : z ≠ 0) (X : ℂ) (K : ℕ) :
    scaledPrimeMatrix q z X K = z • (formalPrimeMatrix q z X K -
      (2 * (1 - (Real.log q : ℂ) / z)) • (1 : Matrix _ _ ℂ)) := by
  ext i j
  simp only [scaledPrimeMatrix, formalPrimeMatrix, dividedDifferenceMatrix,
    dividedDifferenceEntry, formalPrimeDiagonal, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j
  · subst j
    simp only [ite_true, mul_one]
    field_simp [hz]
  · have hc : centeredIndex K i ≠ centeredIndex K j :=
      fun e => h (centeredIndex_injective K e)
    simp only [if_neg hc, if_neg h, mul_zero, sub_zero]
    ring

theorem scaledPrimeMatrix_zero (q : ℕ) (X : ℂ) (K : ℕ) :
    scaledPrimeMatrix q 0 X K = Matrix.diagonal (fun i =>
      -(Real.log q : ℂ) * (X ^ (-centeredIndex K i) + X ^ centeredIndex K i - 2)) := by
  ext i j
  simp only [scaledPrimeMatrix, dividedDifferenceMatrix, dividedDifferenceEntry,
    zero_mul, sub_self, zero_div, zero_sub, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst j
    simp
  · have hc : centeredIndex K i ≠ centeredIndex K j :=
      fun e => h (centeredIndex_injective K e)
    simp [h, hc]

theorem analyticAt_scaledPrimeMatrix (q : ℕ) (X : ℂ) (K : ℕ)
    (i j : Fin (2 * K + 1)) (z : ℂ) :
    AnalyticAt ℂ (fun w => scaledPrimeMatrix q w X K i j) z := by
  unfold scaledPrimeMatrix dividedDifferenceMatrix dividedDifferenceEntry
  split_ifs
  · fun_prop
  · fun_prop

theorem tendsto_scaledPrimeMatrix (q : ℕ) (X : ℂ) (K : ℕ)
    (i j : Fin (2 * K + 1)) :
    Filter.Tendsto (fun z => scaledPrimeMatrix q z X K i j) (nhds 0)
      (nhds (Matrix.diagonal (fun i => -(Real.log q : ℂ) *
        (X ^ (-centeredIndex K i) + X ^ centeredIndex K i - 2)) i j)) := by
  simpa only [scaledPrimeMatrix_zero] using
    (analyticAt_scaledPrimeMatrix q X K i j 0).continuousAt.tendsto

theorem meromorphicAt_formalPrimeMatrix (q : ℕ) (X : ℂ) (K : ℕ)
    (i j : Fin (2 * K + 1)) (z : ℂ) :
    MeromorphicAt (fun w => formalPrimeMatrix q w X K i j) z := by
  unfold formalPrimeMatrix dividedDifferenceMatrix dividedDifferenceEntry
  split_ifs
  · unfold formalPrimeDiagonal
    exact ((MeromorphicAt.const 1 z).sub
      ((MeromorphicAt.const (Real.log q : ℂ) z).div (MeromorphicAt.id z))).mul
      (MeromorphicAt.const _ z)
  · exact MeromorphicAt.const _ z

def formalFrozenPrimeMatrix (Q : ℕ) (z : ℂ) (X : ℕ → ℂ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  ∑ q ∈ Finset.Icc 2 Q, primeSourceWeight q • formalPrimeMatrix q z (X q) K

def primeCommonScalar (Q : ℕ) (z : ℂ) : ℂ :=
  ∑ q ∈ Finset.Icc 2 Q, primeSourceWeight q * (2 * (1 - (Real.log q : ℂ) / z))

def scaledFrozenPrimeMatrix (Q : ℕ) (z : ℂ) (X : ℕ → ℂ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  ∑ q ∈ Finset.Icc 2 Q, primeSourceWeight q • scaledPrimeMatrix q z (X q) K

theorem formalFrozenPrimeMatrix_actual (Q : ℕ) (z : ℂ) (K : ℕ) :
    formalFrozenPrimeMatrix Q z (fun q => integerPhase q z) K =
      complexFrozenCanonicalPrimeMatrix Q z K := by
  exact (frozenPrimeMatrix_laurent Q K z).symm

theorem scaledFrozenPrimeMatrix_eq (Q : ℕ) {z : ℂ} (hz : z ≠ 0)
    (X : ℕ → ℂ) (K : ℕ) :
    scaledFrozenPrimeMatrix Q z X K =
      z • (formalFrozenPrimeMatrix Q z X K - primeCommonScalar Q z • 1) := by
  simp only [scaledFrozenPrimeMatrix, formalFrozenPrimeMatrix, primeCommonScalar,
    scaledPrimeMatrix_eq _ hz, Finset.sum_smul, Finset.smul_sum, smul_sub,
    Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro q hq
    exact smul_comm _ _ _
  · apply Finset.sum_congr rfl
    intro q hq
    simp only [smul_smul]
    congr 1
    ring

theorem analyticAt_scaledFrozenPrimeMatrix (Q : ℕ) (X : ℕ → ℂ) (K : ℕ)
    (i j : Fin (2 * K + 1)) (z : ℂ) :
    AnalyticAt ℂ (fun w => scaledFrozenPrimeMatrix Q w X K i j) z := by
  simp only [scaledFrozenPrimeMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.analyticAt_fun_sum
  intro q hq
  exact analyticAt_const.mul (analyticAt_scaledPrimeMatrix q (X q) K i j z)

end Zeta23.OPICARound4.PrimeSourceLaurent
