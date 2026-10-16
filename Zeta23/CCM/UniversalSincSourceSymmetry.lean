import Zeta23.CCM.UniversalSincSourceDensityIdentification

/-!
# Exact symmetry of the constructed original density

The inverse integral is reflection invariant by a literal change of
variable and evenness of the actual product. Its proved identity with the
constructed density transfers this to pointwise density symmetry.
-/

noncomputable section

open MeasureTheory Complex
open scoped Topology

namespace Zeta23.CCM.UniversalSinc

theorem inverseCandidate_neg (s x : ℝ) :
    inverseCandidate s (-x) = inverseCandidate s x := by
  have hFT : Zeta23.paperFT (fun ξ : ℝ => product s (ξ : ℂ)) (x : ℂ) =
      Zeta23.paperFT (fun ξ : ℝ => product s (ξ : ℂ)) ((-x : ℝ) : ℂ) := by
    rw [Zeta23.paperFT_def, Zeta23.paperFT_def]
    conv_lhs => rw [← integral_neg_eq_self]
    apply integral_congr_ae
    filter_upwards with ξ
    rw [Complex.ofReal_neg, product_neg]
    congr 1
    congr 1
    push_cast
    ring
  unfold inverseCandidate
  simpa only [neg_neg] using congrArg
    (fun z : ℂ => ((1 / (2 * Real.pi) : ℝ) : ℂ) * z) hFT

theorem originalDensityComplex_neg {s : ℝ} (hs : 0 < s) (x : ℝ) :
    originalDensityComplex s (-x) = originalDensityComplex s x := by
  rw [← inverseCandidate_eq_originalDensityComplex hs]
  exact inverseCandidate_neg s x

theorem originalDensityCandidate_even {s : ℝ} (hs : 0 < s) :
    Function.Even (originalDensityCandidate s) := by
  intro x
  apply Complex.ofReal_injective
  exact originalDensityComplex_neg hs x

theorem originalDensityComplex_even {s : ℝ} (hs : 0 < s) :
    Function.Even (originalDensityComplex s) := originalDensityComplex_neg hs

theorem originalDensityComplex_im (s x : ℝ) :
    (originalDensityComplex s x).im = 0 := by
  simp only [originalDensityComplex, Complex.ofReal_im]

end Zeta23.CCM.UniversalSinc

#print axioms Zeta23.CCM.UniversalSinc.originalDensityCandidate_even
#print axioms Zeta23.CCM.UniversalSinc.originalDensityComplex_even
