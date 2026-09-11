import Zeta23.CCM.CanonicalApertureParameterHolomorphy
import Zeta23.CCM.FrozenCanonicalSourceComplex
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set Filter
open scoped BigOperators ComplexConjugate ArithmeticFunction

/-!
# FIRST-BAD-RIGIDITY-E4-A4R1d: assembled source holomorphy

PR #148 proved genuine parameter holomorphy of the three fixed-unit
archimedean cores on `complexArchSafeStrip`.  This module begins assembling
those pointwise core theorems into the actual frozen source continuation.

The natural common source domain removes the explicit prime/pole singularity at
zero from the archimedean safe strip.  The scalar principal-log branch is still
handled separately; merely defining this punctured strip does not assert that
the full source is analytic there.

No determinant density, positivity, negative-root exclusion, or RH theorem is
claimed here.
-/

/-- Common punctured strip for the frozen source channels before the scalar-log
branch condition is discharged. -/
def complexFrozenSourceDomain : Set ℂ :=
  complexArchSafeStrip \ {0}

/-- The punctured source strip is open. -/
theorem isOpen_complexFrozenSourceDomain : IsOpen complexFrozenSourceDomain := by
  exact isOpen_complexArchSafeStrip.sdiff isClosed_singleton

/-- Every nonzero real aperture lies in the punctured source strip. -/
@[simp] theorem ofReal_mem_complexFrozenSourceDomain_iff (L : ℝ) :
    (L : ℂ) ∈ complexFrozenSourceDomain ↔ L ≠ 0 := by
  simp [complexFrozenSourceDomain, ofReal_mem_complexArchSafeStrip]

/-- The exact `wCorrection`-free archimedean source entry is analytic throughout
#148's common strip. -/
theorem analyticOnNhd_complexCanonicalArchWithoutWComponent_strip
    (n m : ℤ) :
    AnalyticOnNhd ℂ
      (complexCanonicalArchWithoutWComponent n m)
      complexArchSafeStrip := by
  by_cases hnm : n = m
  · subst m
    have hg :=
      (analyticOnNhd_complexGammaCore_strip n).const_smul (c := (2 : ℂ))
    have hb :=
      (analyticOnNhd_complexBetaCore_strip n).const_smul (c := (2 : ℂ))
    simpa [complexCanonicalArchWithoutWComponent, smul_eq_mul] using hg.sub hb
  · have ha :=
      (analyticOnNhd_complexAlphaCore_strip m).sub
        (analyticOnNhd_complexAlphaCore_strip n)
    simpa [complexCanonicalArchWithoutWComponent, hnm] using
      ha.div_const (c := (((n - m : ℤ) : ℂ)))

/-- Matrix packaging of the exact archimedean remainder holomorphy. -/
theorem analyticOnNhd_complexCanonicalArchWithoutWMatrix_strip
    (K : ℕ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => complexCanonicalArchWithoutWMatrix z K)
      complexArchSafeStrip := by
  rw [analyticOnNhd_pi_iff]
  intro i
  rw [analyticOnNhd_pi_iff]
  intro j
  simpa [complexCanonicalArchWithoutWMatrix] using
    analyticOnNhd_complexCanonicalArchWithoutWComponent_strip
      (centeredIndex K i) (centeredIndex K j)

/-- The only singularity of one frozen prime coordinate on the selected source
domain has already been removed by definition. -/
theorem analyticOnNhd_complexPrimeSourceCoordinate_sourceDomain
    (q : ℕ) :
    AnalyticOnNhd ℂ
      (complexPrimeSourceCoordinate q)
      complexFrozenSourceDomain := by
  intro z hz
  have hz0 : z ≠ 0 := by
    have hnot : z ∉ ({0} : Set ℂ) := hz.2
    simpa using hnot
  have hquot : AnalyticAt ℂ (fun w : ℂ => (Real.log q : ℂ) / w) z :=
    analyticAt_const.div analyticAt_id hz0
  simpa [complexPrimeSourceCoordinate] using analyticAt_const.sub hquot

private theorem analyticOnNhd_complexSourcePotential_comp
    {s : Set ℂ} {ω : ℂ → ℂ}
    (hω : AnalyticOnNhd ℂ ω s) (n : ℤ) :
    AnalyticOnNhd ℂ (fun z : ℂ => complexSourcePotential (ω z) n) s := by
  intro z hz
  have hw := hω z hz
  let a : ℂ := 2 * (Real.pi : ℂ) * (n : ℂ)
  have harg : AnalyticAt ℂ (fun u : ℂ => a * ω u) z :=
    analyticAt_const.mul hw
  have hsin : AnalyticAt ℂ (fun u : ℂ => Complex.sin (a * ω u)) z := by
    simpa [Function.comp_def] using Complex.analyticAt_sin.comp harg
  simpa [complexSourcePotential, a, mul_assoc] using
    hsin.div_const (c := (Real.pi : ℂ))

private theorem analyticOnNhd_complexSourceDiagonal_comp
    {s : Set ℂ} {ω : ℂ → ℂ}
    (hω : AnalyticOnNhd ℂ ω s) (n : ℤ) :
    AnalyticOnNhd ℂ (fun z : ℂ => complexSourceDiagonal (ω z) n) s := by
  intro z hz
  have hw := hω z hz
  let a : ℂ := 2 * (Real.pi : ℂ) * (n : ℂ)
  have harg : AnalyticAt ℂ (fun u : ℂ => a * ω u) z :=
    analyticAt_const.mul hw
  have hcos : AnalyticAt ℂ (fun u : ℂ => Complex.cos (a * ω u)) z := by
    simpa [Function.comp_def] using Complex.analyticAt_cos.comp harg
  have hprod : AnalyticAt ℂ
      (fun u : ℂ => (2 : ℂ) * (ω u * Complex.cos (a * ω u))) z :=
    analyticAt_const.mul (hw.mul hcos)
  simpa [complexSourceDiagonal, a, mul_assoc] using hprod

private theorem analyticOnNhd_complexSourceEntry_comp
    {s : Set ℂ} {ω : ℂ → ℂ}
    (hω : AnalyticOnNhd ℂ ω s) (n m : ℤ) :
    AnalyticOnNhd ℂ (fun z : ℂ => complexSourceEntry (ω z) n m) s := by
  by_cases hnm : n = m
  · subst m
    simpa [complexSourceEntry, dividedDifferenceEntry] using
      analyticOnNhd_complexSourceDiagonal_comp hω n
  · have hn := analyticOnNhd_complexSourcePotential_comp hω n
    have hm := analyticOnNhd_complexSourcePotential_comp hω m
    simpa [complexSourceEntry, dividedDifferenceEntry, hnm] using
      (hn.sub hm).div_const (c := (((n - m : ℤ) : ℂ)))

/-- Any analytic complex source coordinate produces an analytic finite source
matrix. -/
theorem analyticOnNhd_complexSourceMatrix_comp
    {s : Set ℂ} {ω : ℂ → ℂ}
    (hω : AnalyticOnNhd ℂ ω s) (K : ℕ) :
    AnalyticOnNhd ℂ (fun z : ℂ => complexSourceMatrix (ω z) K) s := by
  rw [analyticOnNhd_pi_iff]
  intro i
  rw [analyticOnNhd_pi_iff]
  intro j
  simpa [complexSourceMatrix, dividedDifferenceMatrix] using
    analyticOnNhd_complexSourceEntry_comp hω
      (centeredIndex K i) (centeredIndex K j)

/-- One frozen prime-power source atom is analytic on the punctured source
strip. -/
theorem analyticOnNhd_complexPrimeSourceMatrix_sourceDomain
    (q K : ℕ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ =>
        complexSourceMatrix (complexPrimeSourceCoordinate q z) K)
      complexFrozenSourceDomain :=
  analyticOnNhd_complexSourceMatrix_comp
    (analyticOnNhd_complexPrimeSourceCoordinate_sourceDomain q) K

/-- The full frozen finite prime channel is analytic on the punctured source
strip.  The prime cutoff is finite and fixed, so no moving-floor issue enters
this theorem. -/
theorem analyticOnNhd_complexFrozenCanonicalPrimeMatrix_sourceDomain
    (Q K : ℕ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => complexFrozenCanonicalPrimeMatrix Q z K)
      complexFrozenSourceDomain := by
  classical
  have hsum := (Finset.Icc 2 Q).analyticOnNhd_fun_sum
    (𝕜 := ℂ)
    (f := fun q : ℕ => fun z : ℂ =>
      primeSourceWeight q •
        complexSourceMatrix (complexPrimeSourceCoordinate q z) K)
    (s := complexFrozenSourceDomain)
    (fun q _hq => by
      simpa using
        (analyticOnNhd_complexPrimeSourceMatrix_sourceDomain q K).const_smul
          (c := primeSourceWeight q))
  simpa [complexFrozenCanonicalPrimeMatrix] using hsum

/-- The quadratic pole denominator for one centered integer frequency has no
zero in the punctured source strip.  Its only complex roots are
`± 4*pi*m*i`; every nonzero such root lies far outside `|Im z| < pi`, while
`m = 0` leaves only the removed root `z = 0`. -/
theorem complexPoleQuadraticDenominator_ne_zero
    (m : ℤ) {z : ℂ} (hz : z ∈ complexFrozenSourceDomain) :
    z ^ 2 + 16 * (Real.pi : ℂ) ^ 2 * (m : ℂ) ^ 2 ≠ 0 := by
  have hzstrip : |z.im| < Real.pi := by
    exact hz.1
  have hz0 : z ≠ 0 := by
    have hnot : z ∉ ({0} : Set ℂ) := hz.2
    simpa using hnot
  by_cases hm0 : m = 0
  · subst m
    simpa using pow_ne_zero 2 hz0
  · intro hzero
    let a : ℂ := 4 * (Real.pi : ℂ) * (m : ℂ) * Complex.I
    have ha2 :
        a ^ 2 = -(16 * (Real.pi : ℂ) ^ 2 * (m : ℂ) ^ 2) := by
      dsimp [a]
      rw [Complex.I_sq]
      ring
    have hsq : z ^ 2 = a ^ 2 := by
      rw [ha2]
      exact eq_neg_of_add_eq_zero_left hzero
    have haim : a.im = 4 * Real.pi * (m : ℝ) := by
      dsimp [a]
      simp
      ring
    have haLower : Real.pi ≤ |a.im| := by
      rw [haim]
      rcases lt_or_gt_of_ne hm0 with hmneg | hmpos
      · have hm1Z : m ≤ (-1 : ℤ) := by omega
        have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast hm1Z
        have hvalneg : 4 * Real.pi * (m : ℝ) < 0 := by
          have hfourpi : 0 < 4 * Real.pi := by positivity
          exact mul_neg_of_pos_of_neg hfourpi (lt_of_le_of_lt hm1 (by norm_num))
        rw [abs_of_neg hvalneg]
        nlinarith [Real.pi_pos]
      · have hm1Z : (1 : ℤ) ≤ m := by omega
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1Z
        have hvalpos : 0 < 4 * Real.pi * (m : ℝ) := by positivity
        rw [abs_of_pos hvalpos]
        nlinarith [Real.pi_pos]
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with hza | hza
    · have hbad := hzstrip
      rw [hza] at hbad
      exact (not_lt_of_ge haLower) hbad
    · have hbad := hzstrip
      rw [hza] at hbad
      simp only [map_neg, abs_neg] at hbad
      exact (not_lt_of_ge haLower) hbad

/-- One literal pole entry is analytic throughout the punctured source strip. -/
theorem analyticOnNhd_complexPoleComponent_sourceDomain
    (n m : ℤ) :
    AnalyticOnNhd ℂ
      (complexPoleComponent n m)
      complexFrozenSourceDomain := by
  intro z hz
  let κ : ℂ := 16 * (Real.pi : ℂ) ^ 2
  have hdenM : z ^ 2 + κ * (m : ℂ) ^ 2 ≠ 0 := by
    simpa [κ, mul_assoc] using complexPoleQuadraticDenominator_ne_zero m hz
  have hdenN : z ^ 2 + κ * (n : ℂ) ^ 2 ≠ 0 := by
    simpa [κ, mul_assoc] using complexPoleQuadraticDenominator_ne_zero n hz
  have hC : AnalyticAt ℂ
      (fun w : ℂ => 32 * w * Complex.sinh (w / 4) ^ 2) z := by
    fun_prop
  have hnum : AnalyticAt ℂ
      (fun w : ℂ => w ^ 2 - κ * ((m * n : ℤ) : ℂ)) z := by
    fun_prop
  have hden : AnalyticAt ℂ
      (fun w : ℂ =>
        (w ^ 2 + κ * (m : ℂ) ^ 2) *
          (w ^ 2 + κ * (n : ℂ) ^ 2)) z := by
    fun_prop
  have hquot := (hC.mul hnum).div hden (mul_ne_zero hdenM hdenN)
  simpa [complexPoleComponent, κ, mul_assoc] using hquot

/-- The centered finite literal pole matrix is analytic throughout the
punctured source strip. -/
theorem analyticOnNhd_complexCanonicalPoleMatrix_sourceDomain
    (K : ℕ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => complexCanonicalPoleMatrix z K)
      complexFrozenSourceDomain := by
  rw [analyticOnNhd_pi_iff]
  intro i
  rw [analyticOnNhd_pi_iff]
  intro j
  simpa [complexCanonicalPoleMatrix] using
    analyticOnNhd_complexPoleComponent_sourceDomain
      (centeredIndex K i) (centeredIndex K j)

end Zeta23.CCM

#print axioms Zeta23.CCM.isOpen_complexFrozenSourceDomain
#print axioms Zeta23.CCM.analyticOnNhd_complexCanonicalArchWithoutWComponent_strip
#print axioms Zeta23.CCM.analyticOnNhd_complexCanonicalArchWithoutWMatrix_strip
#print axioms Zeta23.CCM.analyticOnNhd_complexPrimeSourceCoordinate_sourceDomain
#print axioms Zeta23.CCM.analyticOnNhd_complexSourceMatrix_comp
#print axioms Zeta23.CCM.analyticOnNhd_complexFrozenCanonicalPrimeMatrix_sourceDomain
#print axioms Zeta23.CCM.complexPoleQuadraticDenominator_ne_zero
#print axioms Zeta23.CCM.analyticOnNhd_complexCanonicalPoleMatrix_sourceDomain
