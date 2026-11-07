import Zeta23.OPICARound4.RegularCells.PrimeSourceLaurent
import Zeta23.OPICARound4.RegularCells.FinitePrimeLaurentAlgebra
import Zeta23.CCM.CanonicalApertureSourceHolomorphy

noncomputable section
namespace Zeta23.OPICARound4.PrimeSourceLaurent
open CCM RegularCells Complex Matrix
open scoped BigOperators

def boundedPrimeSet (Q : ℕ) : Finset ℕ :=
  (Finset.range (Q + 1)).filter Nat.Prime

theorem boundedPrimeSet_prime (Q : ℕ) : ∀ p ∈ boundedPrimeSet Q, Nat.Prime p := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2

theorem primeFactors_subset_boundedPrimeSet (Q q : ℕ) (hq : q ≤ Q) :
    q.primeFactors ⊆ boundedPrimeSet Q := by
  intro p hp
  obtain ⟨hpp, hpd, hq0⟩ := Nat.mem_primeFactors.mp hp
  have hle : p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hpd
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpp⟩

def integerFormalExponent (Q q : ℕ) (p : boundedPrimeSet Q) : ℤ :=
  q.factorization (p : ℕ)

def integerFormalPhase (Q q : ℕ) (X : boundedPrimeSet Q → ℂˣ) : ℂ :=
  formalPrimeMonomial (boundedPrimeSet Q) (integerFormalExponent Q q) X

theorem integerPhase_eq_primePhase (q : ℕ) (z : ℂ) :
    integerPhase q z = primePhase q z := by
  unfold integerPhase primePhase
  push_cast
  rfl

theorem integerFormalPhase_actual (Q q : ℕ) (hq : q ≤ Q) (z : ℂ) :
    integerFormalPhase Q q (primePhaseUnits (boundedPrimeSet Q) z) = integerPhase q z := by
  rw [integerPhase_eq_primePhase,
    primePhase_eq_factorization_monomial (boundedPrimeSet Q) q
      (primeFactors_subset_boundedPrimeSet Q q hq)]
  rfl

theorem formalPrimeMonomial_zpow (s : Finset ℕ) (k : s → ℤ) (n : ℤ)
    (X : s → ℂˣ) :
    formalPrimeMonomial s k X ^ n =
      formalPrimeMonomial s (fun p => k p * n) X := by
  simp only [formalPrimeMonomial, _root_.zpow_mul]
  exact (Finset.prod_zpow _ _ _).symm

theorem integerFormalPhase_zpow_expansion (Q q : ℕ) (n : ℤ) :
    HasPrimeLaurentExpansion (boundedPrimeSet Q)
      (fun _ X => integerFormalPhase Q q X ^ n) := by
  apply (HasPrimeLaurentExpansion.monomial (boundedPrimeSet Q)
    (fun p => integerFormalExponent Q q p * n)).congr
  intro z X
  exact (formalPrimeMonomial_zpow _ _ n X).symm

theorem formalPrimePotential_expansion (Q q : ℕ) (n : ℤ) :
    HasPrimeLaurentExpansion (boundedPrimeSet Q)
      (fun _ X => formalPrimePotential (integerFormalPhase Q q X) n) := by
  have h := (integerFormalPhase_zpow_expansion Q q n).sub
    (integerFormalPhase_zpow_expansion Q q (-n))
  have hc := HasPrimeLaurentExpansion.constant (s := boundedPrimeSet Q)
    (fun _ => Complex.I / (2 * (Real.pi : ℂ))) (by fun_prop)
  apply (h.mul hc).congr
  intro z X
  simp only [formalPrimePotential, mul_div_assoc]

theorem formalPrimeDiagonal_expansion (Q q : ℕ) (n : ℤ) :
    HasPrimeLaurentExpansion (boundedPrimeSet Q)
      (fun z X => formalPrimeDiagonal q z (integerFormalPhase Q q X) n) := by
  have hc := HasPrimeLaurentExpansion.constant (s := boundedPrimeSet Q)
    (fun z : ℂ => 1 - (Real.log q : ℂ) / z)
    ((MeromorphicAt.const 1 0).sub
      ((MeromorphicAt.const (Real.log q : ℂ) 0).div (MeromorphicAt.id 0)))
  exact hc.mul ((integerFormalPhase_zpow_expansion Q q (-n)).add
    (integerFormalPhase_zpow_expansion Q q n))

theorem formalPrimeMatrix_expansion (Q q K : ℕ) (i j : Fin (2 * K + 1)) :
    HasPrimeLaurentExpansion (boundedPrimeSet Q)
      (fun z X => formalPrimeMatrix q z (integerFormalPhase Q q X) K i j) := by
  unfold formalPrimeMatrix dividedDifferenceMatrix dividedDifferenceEntry
  split_ifs
  · exact formalPrimeDiagonal_expansion Q q _
  · have h := (formalPrimePotential_expansion Q q (centeredIndex K i)).sub
      (formalPrimePotential_expansion Q q (centeredIndex K j))
    exact h.mul (HasPrimeLaurentExpansion.constant
      (fun _ => ((((centeredIndex K i - centeredIndex K j : ℤ) : ℂ)))⁻¹)
      (by fun_prop))

def factoredFrozenPrimeMatrix (Q : ℕ) (z : ℂ)
    (X : boundedPrimeSet Q → ℂˣ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  formalFrozenPrimeMatrix Q z (fun q => integerFormalPhase Q q X) K

theorem factoredFrozenPrimeMatrix_actual (Q K : ℕ) (z : ℂ) :
    factoredFrozenPrimeMatrix Q z (primePhaseUnits (boundedPrimeSet Q) z) K =
      complexFrozenCanonicalPrimeMatrix Q z K := by
  rw [← formalFrozenPrimeMatrix_actual]
  unfold factoredFrozenPrimeMatrix formalFrozenPrimeMatrix
  apply Finset.sum_congr rfl
  intro q hq
  dsimp only
  rw [integerFormalPhase_actual Q q (Finset.mem_Icc.mp hq).2]

theorem factoredFrozenPrimeMatrix_expansion (Q K : ℕ) (i j : Fin (2 * K + 1)) :
    HasPrimeLaurentExpansion (boundedPrimeSet Q)
      (fun z X => factoredFrozenPrimeMatrix Q z X K i j) := by
  unfold factoredFrozenPrimeMatrix formalFrozenPrimeMatrix
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact HasPrimeLaurentExpansion.sum (Finset.Icc 2 Q) _ (fun q _ =>
    (HasPrimeLaurentExpansion.constant (fun _ => primeSourceWeight q) (by fun_prop)).mul
      (formalPrimeMatrix_expansion Q q K i j))

def formalWFreeSourceMatrix (Q : ℕ) (z : ℂ)
    (X : boundedPrimeSet Q → ℂˣ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  -complexCanonicalArchWithoutWMatrix z K - factoredFrozenPrimeMatrix Q z X K

theorem formalWFreeSourceMatrix_actual (Q K : ℕ) (z : ℂ) :
    formalWFreeSourceMatrix Q z (primePhaseUnits (boundedPrimeSet Q) z) K =
      -complexCanonicalArchWithoutWMatrix z K - complexFrozenCanonicalPrimeMatrix Q z K := by
  rw [formalWFreeSourceMatrix, factoredFrozenPrimeMatrix_actual]

theorem formalWFreeSourceMatrix_expansion (Q K : ℕ) (i j : Fin (2 * K + 1)) :
    HasPrimeLaurentExpansion (boundedPrimeSet Q)
      (fun z X => formalWFreeSourceMatrix Q z X K i j) := by
  have ha : MeromorphicAt (fun z => complexCanonicalArchWithoutWMatrix z K i j) 0 :=
    (analyticOnNhd_complexCanonicalArchWithoutWMatrix_apply_strip K i j 0
      (by simp)).meromorphicAt
  exact ((HasPrimeLaurentExpansion.constant _ ha).neg).sub
    (factoredFrozenPrimeMatrix_expansion Q K i j)



theorem scaledPrimeMatrix_expansion (Q q K : ℕ) (i j : Fin (2 * K + 1)) :
    HasPrimeLaurentExpansion (boundedPrimeSet Q)
      (fun z X => scaledPrimeMatrix q z (integerFormalPhase Q q X) K i j) := by
  have hp (n : ℤ) := (HasPrimeLaurentExpansion.constant (s := boundedPrimeSet Q)
    (fun z : ℂ => z) (MeromorphicAt.id 0)).mul (formalPrimePotential_expansion Q q n)
  unfold scaledPrimeMatrix dividedDifferenceMatrix dividedDifferenceEntry
  split_ifs
  · exact (HasPrimeLaurentExpansion.constant
      (fun z : ℂ => z - (Real.log q : ℂ)) (by fun_prop)).mul
      (((integerFormalPhase_zpow_expansion Q q _).add
        (integerFormalPhase_zpow_expansion Q q _)).sub
          (HasPrimeLaurentExpansion.constant (fun _ => 2) (by fun_prop)))
  · exact ((hp (centeredIndex K i)).sub (hp (centeredIndex K j))).mul
      (HasPrimeLaurentExpansion.constant
        (fun _ => ((((centeredIndex K i - centeredIndex K j : ℤ) : ℂ)))⁻¹) (by fun_prop))

def factoredScaledPrimeMatrix (Q : ℕ) (z : ℂ)
    (X : boundedPrimeSet Q → ℂˣ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  scaledFrozenPrimeMatrix Q z (fun q => integerFormalPhase Q q X) K

theorem factoredScaledPrimeMatrix_expansion (Q K : ℕ) (i j : Fin (2 * K + 1)) :
    HasPrimeLaurentExpansion (boundedPrimeSet Q)
      (fun z X => factoredScaledPrimeMatrix Q z X K i j) := by
  unfold factoredScaledPrimeMatrix scaledFrozenPrimeMatrix
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact HasPrimeLaurentExpansion.sum (Finset.Icc 2 Q) _ (fun q _ =>
    (HasPrimeLaurentExpansion.constant (fun _ => primeSourceWeight q) (by fun_prop)).mul
      (scaledPrimeMatrix_expansion Q q K i j))

theorem factoredScaledPrimeMatrix_actual (Q K : ℕ) (z : ℂ) :
    factoredScaledPrimeMatrix Q z (primePhaseUnits (boundedPrimeSet Q) z) K =
      scaledFrozenPrimeMatrix Q z (fun q => integerPhase q z) K := by
  unfold factoredScaledPrimeMatrix scaledFrozenPrimeMatrix
  apply Finset.sum_congr rfl
  intro q hq
  dsimp only
  rw [integerFormalPhase_actual Q q (Finset.mem_Icc.mp hq).2]

/-- Scaled, exactly common-scalar-subtracted source; defined at zero by the
literal polynomial prime continuation, not by assigning z*(1/z)=1 there. -/
def formalScaledSourceMatrix (Q : ℕ) (z : ℂ)
    (X : boundedPrimeSet Q → ℂˣ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  (-z) • complexCanonicalArchWithoutWMatrix z K - factoredScaledPrimeMatrix Q z X K

theorem formalScaledSourceMatrix_eq (Q K : ℕ) {z : ℂ} (hz : z ≠ 0)
    (X : boundedPrimeSet Q → ℂˣ) :
    formalScaledSourceMatrix Q z X K = z •
      (formalWFreeSourceMatrix Q z X K + primeCommonScalar Q z • 1) := by
  unfold formalScaledSourceMatrix factoredScaledPrimeMatrix formalWFreeSourceMatrix
    factoredFrozenPrimeMatrix
  rw [scaledFrozenPrimeMatrix_eq Q hz]
  module

theorem formalScaledSourceMatrix_actual (Q K : ℕ) (z : ℂ) :
    formalScaledSourceMatrix Q z (primePhaseUnits (boundedPrimeSet Q) z) K =
      (-z) • complexCanonicalArchWithoutWMatrix z K -
        scaledFrozenPrimeMatrix Q z (fun q => integerPhase q z) K := by
  rw [formalScaledSourceMatrix, factoredScaledPrimeMatrix_actual]

theorem formalScaledSourceMatrix_expansion (Q K : ℕ) (i j : Fin (2 * K + 1)) :
    HasPrimeLaurentExpansion (boundedPrimeSet Q)
      (fun z X => formalScaledSourceMatrix Q z X K i j) := by
  have ha : MeromorphicAt (fun z => complexCanonicalArchWithoutWMatrix z K i j) 0 :=
    (analyticOnNhd_complexCanonicalArchWithoutWMatrix_apply_strip K i j 0
      (by simp)).meromorphicAt
  exact ((HasPrimeLaurentExpansion.constant (fun z : ℂ => -z) (by fun_prop)).mul
    (HasPrimeLaurentExpansion.constant _ ha)).sub
      (factoredScaledPrimeMatrix_expansion Q K i j)

private theorem matrix_mul_expansion {s : Finset ℕ} {m n k : Type*} [Fintype n]
    (A : ℂ → (s → ℂˣ) → Matrix m n ℂ)
    (B : ℂ → (s → ℂˣ) → Matrix n k ℂ)
    (hA : ∀ i j, HasPrimeLaurentExpansion s (fun z X => A z X i j))
    (hB : ∀ i j, HasPrimeLaurentExpansion s (fun z X => B z X i j)) :
    ∀ i j, HasPrimeLaurentExpansion s (fun z X => (A z X * B z X) i j) := by
  intro i j
  exact HasPrimeLaurentExpansion.sum Finset.univ _ (fun l _ => (hA i l).mul (hB l j))

/-- Literal raw physical diagonal; no aperture-dependent conjugation or inverse Gram. -/
def rawPhysicalDiagonal (K : ℕ) (z : ℂ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  Matrix.diagonal (fun i => (z / (4 * (Real.pi : ℂ))) ^ 2 + (centeredIndex K i : ℂ) ^ 2)

theorem rawPhysicalDiagonal_expansion (Q K : ℕ) (i j : Fin (2 * K + 1)) :
    HasPrimeLaurentExpansion (boundedPrimeSet Q)
      (fun z _ => rawPhysicalDiagonal K z i j) := by
  apply HasPrimeLaurentExpansion.constant
  simp only [rawPhysicalDiagonal, Matrix.diagonal_apply]
  split_ifs <;> fun_prop

def formalRawFrameEnergy {ι : Type*} (Q K : ℕ)
    (C : Matrix (Fin (2 * K + 1)) ι ℂ) (z : ℂ) (X : boundedPrimeSet Q → ℂˣ) :
    Matrix ι ι ℂ :=
  C.conjTranspose * rawPhysicalDiagonal K z * formalScaledSourceMatrix Q z X K *
    rawPhysicalDiagonal K z * C

def formalRawFrameGram {ι : Type*} (K : ℕ)
    (C : Matrix (Fin (2 * K + 1)) ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  C.conjTranspose * rawPhysicalDiagonal K z * rawPhysicalDiagonal K z * C

theorem formalRawFrameEnergy_expansion {ι : Type*} (Q K : ℕ)
    (C : Matrix (Fin (2 * K + 1)) ι ℂ) :
    ∀ i j, HasPrimeLaurentExpansion (boundedPrimeSet Q)
      (fun z X => formalRawFrameEnergy Q K C z X i j) := by
  have hc : ∀ i j, HasPrimeLaurentExpansion (boundedPrimeSet Q)
      (fun (_ : ℂ) (_ : boundedPrimeSet Q → ℂˣ) => C i j) :=
    fun i j => HasPrimeLaurentExpansion.constant _ (by fun_prop)
  have hct : ∀ i j, HasPrimeLaurentExpansion (boundedPrimeSet Q)
      (fun (_ : ℂ) (_ : boundedPrimeSet Q → ℂˣ) => C.conjTranspose i j) :=
    fun i j => HasPrimeLaurentExpansion.constant _ (by fun_prop)
  exact matrix_mul_expansion _ _
    (matrix_mul_expansion _ _
      (matrix_mul_expansion _ _
        (matrix_mul_expansion _ _ hct (rawPhysicalDiagonal_expansion Q K))
        (formalScaledSourceMatrix_expansion Q K))
      (rawPhysicalDiagonal_expansion Q K)) hc

theorem formalRawFrameGram_expansion {ι : Type*} (Q K : ℕ)
    (C : Matrix (Fin (2 * K + 1)) ι ℂ) :
    ∀ i j, HasPrimeLaurentExpansion (boundedPrimeSet Q)
      (fun z _ => formalRawFrameGram K C z i j) := by
  have hc : ∀ i j, HasPrimeLaurentExpansion (boundedPrimeSet Q)
      (fun (_ : ℂ) (_ : boundedPrimeSet Q → ℂˣ) => C i j) :=
    fun i j => HasPrimeLaurentExpansion.constant _ (by fun_prop)
  have hct : ∀ i j, HasPrimeLaurentExpansion (boundedPrimeSet Q)
      (fun (_ : ℂ) (_ : boundedPrimeSet Q → ℂˣ) => C.conjTranspose i j) :=
    fun i j => HasPrimeLaurentExpansion.constant _ (by fun_prop)
  exact matrix_mul_expansion _ _
    (matrix_mul_expansion _ _
      (matrix_mul_expansion _ _ hct (rawPhysicalDiagonal_expansion Q K))
      (rawPhysicalDiagonal_expansion Q K)) hc

theorem formalRawFrameEnergy_actual {ι : Type*} (Q K : ℕ)
    (C : Matrix (Fin (2 * K + 1)) ι ℂ) (z : ℂ) :
    formalRawFrameEnergy Q K C z (primePhaseUnits (boundedPrimeSet Q) z) =
      C.conjTranspose * rawPhysicalDiagonal K z *
        ((-z) • complexCanonicalArchWithoutWMatrix z K -
          scaledFrozenPrimeMatrix Q z (fun q => integerPhase q z) K) *
        rawPhysicalDiagonal K z * C := by
  rw [formalRawFrameEnergy, formalScaledSourceMatrix_actual]

/-- Exact coefficient matrix of X ↦ Ho*X*Ge-Go*X*He on the complete rectangular
matrix space, with both full Grams retained. -/
def formalRawFrameSylvester {ι κ : Type*} (Q K : ℕ)
    (Ce : Matrix (Fin (2 * K + 1)) ι ℂ)
    (Co : Matrix (Fin (2 * K + 1)) κ ℂ) (z : ℂ) (X : boundedPrimeSet Q → ℂˣ) :
    Matrix (κ × ι) (κ × ι) ℂ :=
  fun ij kl => formalRawFrameEnergy Q K Co z X ij.1 kl.1 * formalRawFrameGram K Ce z kl.2 ij.2 -
    formalRawFrameGram K Co z ij.1 kl.1 * formalRawFrameEnergy Q K Ce z X kl.2 ij.2

theorem formalRawFrameSylvester_expansion {ι κ : Type*} (Q K : ℕ)
    (Ce : Matrix (Fin (2 * K + 1)) ι ℂ)
    (Co : Matrix (Fin (2 * K + 1)) κ ℂ) (i j : κ × ι) :
    HasPrimeLaurentExpansion (boundedPrimeSet Q)
      (fun z X => formalRawFrameSylvester Q K Ce Co z X i j) := by
  exact ((formalRawFrameEnergy_expansion Q K Co i.1 j.1).mul
    (formalRawFrameGram_expansion Q K Ce j.2 i.2)).sub
    ((formalRawFrameGram_expansion Q K Co i.1 j.1).mul
      (formalRawFrameEnergy_expansion Q K Ce j.2 i.2))

theorem formalRawFrameSylvester_det_expansion {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (Q K : ℕ)
    (Ce : Matrix (Fin (2 * K + 1)) ι ℂ)
    (Co : Matrix (Fin (2 * K + 1)) κ ℂ) :
    HasPrimeLaurentExpansion (boundedPrimeSet Q)
      (fun z X => (formalRawFrameSylvester Q K Ce Co z X).det) :=
  HasPrimeLaurentExpansion.det _ (formalRawFrameSylvester_expansion Q K Ce Co)


theorem formalRawFrameSylvester_mulVec {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q K : ℕ) (Ce : Matrix (Fin (2 * K + 1)) ι ℂ)
    (Co : Matrix (Fin (2 * K + 1)) κ ℂ) (z : ℂ) (X : boundedPrimeSet Q → ℂˣ)
    (V : Matrix κ ι ℂ) (i : κ) (j : ι) :
    (formalRawFrameSylvester Q K Ce Co z X *ᵥ (fun ij => V ij.1 ij.2)) (i,j) =
      (formalRawFrameEnergy Q K Co z X * V * formalRawFrameGram K Ce z -
        formalRawFrameGram K Co z * V * formalRawFrameEnergy Q K Ce z X) i j := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    formalRawFrameSylvester, sub_mul, Finset.sum_sub_distrib,
    Matrix.sub_apply, Matrix.mul_apply, Finset.sum_mul]
  congr 1 <;> rw [Finset.sum_comm] <;> apply Finset.sum_congr rfl <;> intro a ha <;>
    apply Finset.sum_congr rfl <;> intro b hb <;> ring

end Zeta23.OPICARound4.PrimeSourceLaurent
