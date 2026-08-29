import Zeta23.CCM.DictionaryTentMollifierLimit
import Zeta23.CCM.DictionaryTentMollifierSupport
import Zeta23.CCM.DictionaryDeterministicRHS

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter
open scoped BigOperators ArithmeticFunction

/-!
# Route-M M4--M5: pole and prime limit passages

M4 uses only the fixed-complex-frequency transform convergence proved in
`DictionaryTentMollifierLimit`.

M5 follows the project's truncate-first firewall.  Every mollified tent is
supported in the one common envelope `[-(L+1), L+1]`, so the raw prime
`tsum` is replaced by one finite set independent of the mollifier index
before any limit is taken.  The cutoff is therefore `exp (L+1)`, not
`exp L`.
-/

/-- Topological-support form of the common M3 support envelope. -/
theorem dictionaryTentMollified_tsupport_subset_Icc_add_one
    {L : ℝ} (hL : 0 < L) (n : ℕ) :
    tsupport (dictionaryTentMollified L n) ⊆
      Icc (-(L + 1)) (L + 1) := by
  exact closure_minimal
    (dictionaryTentMollified_support_subset_Icc hL n) isClosed_Icc

/-- The literal tent is also supported in the larger common M5 envelope. -/
theorem dictionaryTent_tsupport_subset_Icc_add_one
    {L : ℝ} (hL : 0 < L) :
    tsupport (dictionaryTent L) ⊆
      Icc (-(L + 1)) (L + 1) := by
  refine closure_minimal ?_ isClosed_Icc
  intro x hx
  have hIcc : x ∈ Icc (-L) L :=
    dictionaryTent_support_subset_Icc hL hx
  constructor <;> linarith [hIcc.1, hIcc.2]

/-- M4: the pole channel converges by evaluating the fixed-frequency transform
limit at the two literature pole frequencies `±I/2`. -/
theorem dictionaryPoleRHS_dictionaryTentMollified_tendsto
    {L : ℝ} (hL : 0 < L) :
    Tendsto
      (fun n : ℕ =>
        dictionaryPoleRHS (dictionaryTentMollified L n))
      atTop
      (𝓝 (dictionaryPoleRHS (dictionaryTent L))) := by
  unfold dictionaryPoleRHS
  exact
    (paperFT_dictionaryTentMollified_tendsto
      hL (Complex.I / 2)).add
    (paperFT_dictionaryTentMollified_tendsto
      hL (-Complex.I / 2))

/-- One fixed prime summand converges by M3 physical-space pointwise
convergence. -/
private theorem dictionaryPrimeSummand_mollified_tendsto
    (L : ℝ) (q : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((Λ q / Real.sqrt q : ℝ) : ℂ) *
          (dictionaryTentMollified L n (Real.log q) +
            dictionaryTentMollified L n (-Real.log q)))
      atTop
      (𝓝 (
        ((Λ q / Real.sqrt q : ℝ) : ℂ) *
          (dictionaryTent L (Real.log q) +
            dictionaryTent L (-Real.log q)))) := by
  have hpair :
      Tendsto
        (fun n : ℕ =>
          dictionaryTentMollified L n (Real.log q) +
            dictionaryTentMollified L n (-Real.log q))
        atTop
        (𝓝 (
          dictionaryTent L (Real.log q) +
            dictionaryTent L (-Real.log q))) :=
    (dictionaryTentMollified_tendsto L (Real.log q)).add
      (dictionaryTentMollified_tendsto L (-Real.log q))
  exact tendsto_const_nhds.mul hpair

/-- M5: truncate the prime channel to one common finite support before passing
to the limit. -/
theorem dictionaryPrimeRHS_dictionaryTentMollified_tendsto
    {L : ℝ} (hL : 0 < L) :
    Tendsto
      (fun n : ℕ =>
        dictionaryPrimeRHS (dictionaryTentMollified L n))
      atTop
      (𝓝 (dictionaryPrimeRHS (dictionaryTent L))) := by
  let R : ℝ := L + 1
  let S : Finset ℕ := Finset.Icc 2 ⌊Real.exp R⌋₊

  have hmoll (n : ℕ) :
      dictionaryPrimeRHS (dictionaryTentMollified L n) =
        -(∑ q ∈ S,
          ((Λ q / Real.sqrt q : ℝ) : ℂ) *
            (dictionaryTentMollified L n (Real.log q) +
              dictionaryTentMollified L n (-Real.log q))) := by
    simpa only [R, S] using
      dictionaryPrimeRHS_eq_finset
        (dictionaryTentMollified_tsupport_subset_Icc_add_one hL n)

  have htent :
      dictionaryPrimeRHS (dictionaryTent L) =
        -(∑ q ∈ S,
          ((Λ q / Real.sqrt q : ℝ) : ℂ) *
            (dictionaryTent L (Real.log q) +
              dictionaryTent L (-Real.log q))) := by
    simpa only [R, S] using
      dictionaryPrimeRHS_eq_finset
        (dictionaryTent_tsupport_subset_Icc_add_one hL)

  have hsum :
      Tendsto
        (fun n : ℕ =>
          ∑ q ∈ S,
            ((Λ q / Real.sqrt q : ℝ) : ℂ) *
              (dictionaryTentMollified L n (Real.log q) +
                dictionaryTentMollified L n (-Real.log q)))
        atTop
        (𝓝 (
          ∑ q ∈ S,
            ((Λ q / Real.sqrt q : ℝ) : ℂ) *
              (dictionaryTent L (Real.log q) +
                dictionaryTent L (-Real.log q)))) := by
    refine tendsto_finsetSum S ?_
    intro q hq
    exact dictionaryPrimeSummand_mollified_tendsto L q

  have hseq :
      (fun n : ℕ =>
        dictionaryPrimeRHS (dictionaryTentMollified L n)) =
      fun n =>
        -(∑ q ∈ S,
          ((Λ q / Real.sqrt q : ℝ) : ℂ) *
            (dictionaryTentMollified L n (Real.log q) +
              dictionaryTentMollified L n (-Real.log q))) := by
    funext n
    exact hmoll n

  rw [hseq, htent]
  exact hsum.neg

/-- Compiler-facing M4--M5 package. -/
theorem dictionaryTent_pole_prime_limit_package
    {L : ℝ} (hL : 0 < L) :
    Tendsto
      (fun n : ℕ =>
        dictionaryPoleRHS (dictionaryTentMollified L n))
      atTop
      (𝓝 (dictionaryPoleRHS (dictionaryTent L))) ∧
    Tendsto
      (fun n : ℕ =>
        dictionaryPrimeRHS (dictionaryTentMollified L n))
      atTop
      (𝓝 (dictionaryPrimeRHS (dictionaryTent L))) := by
  exact ⟨
    dictionaryPoleRHS_dictionaryTentMollified_tendsto hL,
    dictionaryPrimeRHS_dictionaryTentMollified_tendsto hL
  ⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.dictionaryPoleRHS_dictionaryTentMollified_tendsto
#print axioms Zeta23.CCM.dictionaryPrimeRHS_dictionaryTentMollified_tendsto
#print axioms Zeta23.CCM.dictionaryTent_pole_prime_limit_package
