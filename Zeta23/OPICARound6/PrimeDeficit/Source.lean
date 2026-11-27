import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Positivity

/-!
# Independent scalar prime-deficit source (R11) — OPEN main upper

Fixed native source, not a modeled prime process: the dyadic base is the
power of two below N, the small-prime center is (p+1)/(2p), the large-prime
set includes all p with z(N)<p<=N, and all N in the complete integer window
including its final full cell. No signed asymptotic bound is proved here.

The analytic link to the independently supplied Deduction.G remains a
separate, explicitly OPEN source-binding/bridge obligation.
-/
noncomputable section
namespace Zeta23.OPICARound6.PrimeDeficit

/-- The unique dyadic block base for N>=1 (no statement for N=0). -/
def dyadicBase (N : ℕ) : ℕ := 2 ^ N.log2

/-- The exact z(N)=U(N)^(2/3), fixed over each dyadic block. -/
def smallPrimeCutoff (N : ℕ) : ℝ :=
  (dyadicBase N : ℝ) ^ ((2:ℝ)/3)

/-- Exact discrete period mean m_p=(p+1)/(2p), not 1/2. -/
def discretePrimeMean (p : ℕ) : ℝ :=
  ((p:ℝ)+1)/(2*(p:ℝ))

/-- Exact prime mean C_z, retaining p<=floor z. -/
def smallPrimeCenter (N : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊smallPrimeCutoff N⌋₊,
    Real.log (p:ℝ) * discretePrimeMean p

/-- N/p - floor(N/p), using exact natural integer division for N,p. -/
def primeFractionalPart (N p : ℕ) : ℝ :=
  (N:ℝ)/(p:ℝ) - ((N/p:ℕ):ℝ)

/-- Exactly the strict lower and inclusive upper prime endpoints z(N)<p<=N. -/
def activeLargePrimes (N : ℕ) : Finset ℕ :=
  (Nat.primesLE N).filter fun p => smallPrimeCutoff N < (p:ℝ)

/-- The literal centered large-prime deficit D_large(N), with C_z intact. -/
def largePrimeDeficit (N : ℕ) : ℝ :=
  Real.eulerMascheroniConstant * (N:ℝ) -
  smallPrimeCenter N -
  ∑ p ∈ activeLargePrimes N,
    Real.log (p:ℝ) * (1-primeFractionalPart N p)

/-- Full weighted integer energy, including K and floor(K^(3/2)). -/
def positiveDeficitEnergy (K : ℕ) : ℝ :=
  ∑ N ∈ Finset.Icc K ⌊(K:ℝ)^((3:ℝ)/2)⌋₊,
    (max (largePrimeDeficit N) 0)^2 / ((N:ℝ)*((N:ℝ)+1))

/-- OPEN. The source-specific cofinal subpower estimate of Round11 equation (OPEN).
There is no theorem proving this definition. -/
def LargePrimeDeficitSubpower : Prop :=
  ∀ η : ℝ, 0 < η → ∀ K₀ : ℕ,
    ∃ K : ℕ, max K₀ 64 ≤ K ∧ positiveDeficitEnergy K ≤ (K:ℝ)^η

/-- Direct discrete von Mangoldt G formula from the paper; equality with the
separately checked external Deduction.G remains to be compiled/proved. -/
def literalG (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    ArithmeticFunction.vonMangoldt n * (x/(n:ℝ)-1)) -
  x * Real.log x + (1+Real.eulerMascheroniConstant)*x

/-- Complete real window at fixed delta=1/2. OPEN source-binding transfer. -/
def literalGEnergy (Y : ℝ) : ℝ :=
  ∫ x in Y..Y^((3:ℝ)/2), (max (literalG x) 0)^2/x^2

/-- The required full arithmetic-to-analytic adapter is itself an OPEN target.
Its presence in source does not assert the implication is proved. -/
def MissingPrimeDeficitToLiteralGBridge : Prop :=
  LargePrimeDeficitSubpower →
    ∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ,
      ∃ Y : ℝ, max Y₀ 2 ≤ Y ∧ literalGEnergy Y ≤ Y^η

/-- A small supporting fact, not an upper bound. -/
theorem positiveDeficitEnergy_nonneg (K : ℕ) :
    0 ≤ positiveDeficitEnergy K := by
  unfold positiveDeficitEnergy
  apply Finset.sum_nonneg
  intro N hN
  positivity

end Zeta23.OPICARound6.PrimeDeficit
