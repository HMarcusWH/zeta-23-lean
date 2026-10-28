import Zeta23.OPICARound4.RegularCells.FixedSeed
import Mathlib.Analysis.Calculus.Deriv.Star

noncomputable section

namespace Zeta23.OPICARound4

open scoped BigOperators ComplexConjugate
set_option backward.isDefEq.respectTransparency false

variable {ι κ : Type*} [Fintype ι]

/-- Energy in a possibly moving, nonorthonormal frame. -/
def frameEnergyEntry (A : ℝ → ι → ι → ℂ) (V : ℝ → ι → κ → ℂ)
    (t : ℝ) (i j : κ) : ℂ :=
  ∑ m, ∑ n, star (V t m i) * A t m n * V t n j

def frameGramEntry (V : ℝ → ι → κ → ℂ) (t : ℝ) (i j : κ) : ℂ :=
  ∑ m, star (V t m i) * V t m j

/-- Includes both moving-frame terms, in addition to the source derivative. -/
def frameEnergyDerivative (A A' : ι → ι → ℂ) (V V' : ι → κ → ℂ)
    (i j : κ) : ℂ :=
  ∑ m, ∑ n, (star (V' m i) * A m n * V n j +
    star (V m i) * A' m n * V n j + star (V m i) * A m n * V' n j)

def frameGramDerivative (V V' : ι → κ → ℂ) (i j : κ) : ℂ :=
  ∑ m, (star (V' m i) * V m j + star (V m i) * V' m j)

theorem frameEnergyEntry_hasDerivAt
    (A : ℝ → ι → ι → ℂ) (V : ℝ → ι → κ → ℂ)
    (A' : ι → ι → ℂ) (V' : ι → κ → ℂ) (t : ℝ)
    (hA : ∀ m n, HasDerivAt (fun s => A s m n) (A' m n) t)
    (hV : ∀ m i, HasDerivAt (fun s => V s m i) (V' m i) t)
    (i j : κ) :
    HasDerivAt (fun s => frameEnergyEntry A V s i j)
      (frameEnergyDerivative (A t) A' (V t) V' i j) t := by
  unfold frameEnergyEntry frameEnergyDerivative
  apply HasDerivAt.fun_sum
  intro m _
  apply HasDerivAt.fun_sum
  intro n _
  have hh : HasDerivAt
      (fun s => star (V s m i) * A s m n * V s n j)
      ((star (V' m i) * A t m n + star (V t m i) * A' m n) * V t n j +
        star (V t m i) * A t m n * V' n j) t := by
    simpa only [Pi.mul_apply] using! (((hV m i).star.mul (hA m n)).mul (hV n j))
  convert! hh using 1 <;> ring

theorem frameGramEntry_hasDerivAt (V : ℝ → ι → κ → ℂ)
    (V' : ι → κ → ℂ) (t : ℝ)
    (hV : ∀ m i, HasDerivAt (fun s => V s m i) (V' m i) t)
    (i j : κ) :
    HasDerivAt (fun s => frameGramEntry V s i j)
      (frameGramDerivative (V t) V' i j) t := by
  unfold frameGramEntry frameGramDerivative
  apply HasDerivAt.fun_sum
  intro m _
  exact (hV m i).star.mul (hV m j)

/-- At a fixed contact value λ the derivative is H'−λG', with the actual
Gram derivative. There is no sign assertion about this contact matrix. -/
theorem neutral_contact_pencil_hasDerivAt
    (A : ℝ → ι → ι → ℂ) (V : ℝ → ι → κ → ℂ)
    (A' : ι → ι → ℂ) (V' : ι → κ → ℂ) (t lam : ℝ)
    (hA : ∀ m n, HasDerivAt (fun s => A s m n) (A' m n) t)
    (hV : ∀ m i, HasDerivAt (fun s => V s m i) (V' m i) t)
    (i j : κ) :
    HasDerivAt (fun s => frameEnergyEntry A V s i j -
      (lam : ℂ) * frameGramEntry V s i j)
      (frameEnergyDerivative (A t) A' (V t) V' i j -
        (lam : ℂ) * frameGramDerivative (V t) V' i j) t :=
  (frameEnergyEntry_hasDerivAt A V A' V' t hA hV i j).sub
    ((frameGramEntry_hasDerivAt V V' t hV i j).const_mul (lam : ℂ))

/-- If λ moves, its derivative contributes the additional −λ'G term. -/
theorem moving_neutral_contact_pencil_hasDerivAt
    (A : ℝ → ι → ι → ℂ) (V : ℝ → ι → κ → ℂ)
    (A' : ι → ι → ℂ) (V' : ι → κ → ℂ)
    (lam : ℝ → ℂ) (lam' : ℂ) (t : ℝ)
    (hA : ∀ m n, HasDerivAt (fun s => A s m n) (A' m n) t)
    (hV : ∀ m i, HasDerivAt (fun s => V s m i) (V' m i) t)
    (hlam : HasDerivAt lam lam' t) (i j : κ) :
    HasDerivAt (fun s => frameEnergyEntry A V s i j -
      lam s * frameGramEntry V s i j)
      (frameEnergyDerivative (A t) A' (V t) V' i j -
        (lam' * frameGramEntry V t i j +
          lam t * frameGramDerivative (V t) V' i j)) t :=
  (frameEnergyEntry_hasDerivAt A V A' V' t hA hV i j).sub
    (hlam.mul (frameGramEntry_hasDerivAt V V' t hV i j))

/-- The actual G01 diagonal applied to any fixed seed frame. -/
def fixedSeedFrame (K : ℕ) (U : Fin (2 * K + 1) → κ → ℂ)
    (t : ℝ) (m : Fin (2 * K + 1)) (i : κ) : ℂ :=
  (RegularCells.fixedSeedDiagonalEntry t K m : ℂ) * U m i

def fixedSeedFrameDerivative (K : ℕ) (U : Fin (2 * K + 1) → κ → ℂ)
    (t : ℝ) (m : Fin (2 * K + 1)) (i : κ) : ℂ :=
  ((2 * (t / (4 * Real.pi)) * (1 / (4 * Real.pi)) : ℝ) : ℂ) * U m i

theorem fixedSeedFrame_hasDerivAt (K : ℕ) (U : Fin (2 * K + 1) → κ → ℂ)
    (t : ℝ) (m : Fin (2 * K + 1)) (i : κ) :
    HasDerivAt (fun s => fixedSeedFrame K U s m i)
      (fixedSeedFrameDerivative K U t m i) t := by
  have hd := ((((hasDerivAt_id t).div_const (4 * Real.pi)).pow 2).add_const
    ((CCM.centeredIndex K m : ℝ) ^ 2)).ofReal_comp
  simpa [fixedSeedFrame, fixedSeedFrameDerivative, RegularCells.fixedSeedDiagonalEntry,
    RegularCells.fixedSeedParameter] using hd.mul_const (U m i)

/-- Native source specialization retains the source derivative as an explicit
local differentiability premise. It proves no arithmetic sign or regularity
outside the domain where that premise has independently been established. -/
theorem native_fixedSeed_contact_pencil_hasDerivAt
    (K : ℕ) (U : Fin (2 * K + 1) → κ → ℂ)
    (A' : Fin (2 * K + 1) → Fin (2 * K + 1) → ℂ) (t lam : ℝ)
    (hA : ∀ m n, HasDerivAt (fun s => CCM.canonicalSourceMatrix s K m n) (A' m n) t)
    (i j : κ) :
    HasDerivAt (fun s => frameEnergyEntry (fun s => CCM.canonicalSourceMatrix s K)
      (fixedSeedFrame K U) s i j - (lam : ℂ) * frameGramEntry (fixedSeedFrame K U) s i j)
      (frameEnergyDerivative (CCM.canonicalSourceMatrix t K) A'
        (fixedSeedFrame K U t) (fixedSeedFrameDerivative K U t) i j -
      (lam : ℂ) * frameGramDerivative (fixedSeedFrame K U t)
        (fixedSeedFrameDerivative K U t) i j) t :=
  neutral_contact_pencil_hasDerivAt _ _ _ _ t lam hA (fixedSeedFrame_hasDerivAt K U t) i j

end Zeta23.OPICARound4
