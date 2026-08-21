import Zeta23.CCM.Kernel
import Zeta23.ExplicitFormula
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

noncomputable section

namespace Zeta23.CCM

open MeasureTheory
open scoped Interval ArithmeticFunction

/-- Classical archimedean density used by the finite CCM construction. -/
def archDensity (x : ℝ) : ℝ :=
  Real.exp (x / 2) / (Real.exp x - Real.exp (-x))

/-- Pointwise-regularized integrand for the index-independent diagonal correction. -/
def cCorrectionIntegrand (x : ℝ) : ℝ :=
  if x = 0 then 1 / 4 else
    (1 - Real.exp (-x / 2)) / (Real.exp x - Real.exp (-x))

/-- R004's index-independent `c_correction(L)`. -/
def cCorrection (L : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..L, cCorrectionIntegrand x

/-- R004's second index-independent diagonal normalization. -/
def wCorrection (L : ℝ) : ℝ :=
  (1 / 2) * (Real.eulerMascheroniConstant + Real.log (4 * Real.pi))
    - (1 / 2) * Real.log ((Real.exp L + 1) / (Real.exp L - 1))

/-- Off-diagonal archimedean primitive `alpha_L(n)`. -/
def alphaL (n : ℤ) (L : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ x in (0 : ℝ)..L,
    (if x = 0 then
      if n = 0 then 0 else Real.pi * (n : ℝ) / L
    else
      Real.sin (2 * Real.pi * (n : ℝ) * x / L) * archDensity x)

/-- Diagonal finite-part term `beta_L(n)`. -/
def betaL (n : ℤ) (L : ℝ) : ℝ :=
  (1 / L) * ∫ x in (0 : ℝ)..L,
    (if x = 0 then 1 / 2
    else x * Real.cos (2 * Real.pi * (n : ℝ) * x / L) * archDensity x)

/-- Diagonal regularized term `gamma_L(n)`. -/
def gammaL (n : ℤ) (L : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..L,
    (if x = 0 then 1 / 4
    else (Real.cos (2 * Real.pi * (n : ℝ) * x / L) - Real.exp (-x / 2))
      * archDensity x))
  + cCorrection L + wCorrection L

/-- Pole channel of the finite CCM matrix. -/
def poleComponent (n m : ℤ) (L : ℝ) : ℝ :=
  let κ : ℝ := 16 * Real.pi ^ 2
  let C : ℝ := 32 * L * Real.sinh (L / 4) ^ 2
  C * (L ^ 2 - κ * ((m * n : ℤ) : ℝ)) /
    ((L ^ 2 + κ * (m : ℝ) ^ 2) * (L ^ 2 + κ * (n : ℝ) ^ 2))

/-- Archimedean channel of the finite CCM matrix. -/
def archComponent (n m : ℤ) (L : ℝ) : ℝ :=
  if n = m then
    2 * gammaL n L - 2 * betaL n L
  else
    (alphaL m L - alphaL n L) / ((n - m : ℤ) : ℝ)

/-- Finite von-Mangoldt prime-power channel. -/
def primeComponent (n m : ℤ) (L : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
    (Λ k / Real.sqrt k : ℝ) * qBasis n m (Real.log k) L

/-- Exact scalar entry of the R004 finite CCM matrix. -/
def entry (n m : ℤ) (L : ℝ) : ℝ :=
  poleComponent n m L - archComponent n m L - primeComponent n m L

end Zeta23.CCM
