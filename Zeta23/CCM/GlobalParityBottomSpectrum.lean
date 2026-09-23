import Zeta23.CCM.CubicShellIncidence
import Zeta23.CCM.ConstrainedParitySpectrum
import Zeta23.CCM.FirstBadSpectralInterfaces
import Mathlib.Analysis.InnerProductSpace.Symmetric

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# PR #247 — Million Dollar PR: global parity spectral bottom

The existing first-bad stack selects some negative eigenvalue in one bad parity.
That is not enough for a parity-complete comparison when both successor
parities are bad.  This module introduces the actual Rayleigh bottom of each
finite parity-compressed canonical operator and the minimum across the two
parities.

The key point is elementary but structurally new for the project: at the common
shift

  lambda_* = min(lambda_even, lambda_odd),

both shifted successor parity operators are nonnegative.  If one parity bottom
is strictly larger than lambda_*, its shifted form has a quantitative positive
gap.

This module is unconditional CCM mathematics.  It imports no exceptional-zero
terminal layer, does not mention the terminal conjecture proposition, and proves no RH
claim.
-/

/-- Bottom Rayleigh quotient of one finite parity-compressed canonical
operator.  Downstream #247 modules mainly use it at successor size N+1. -/
def parityRayleighBottom
    (p : ReversalParity) (L : ℝ) (K : ℕ) : ℝ :=
  ⨅ z : {z : euclideanParityBoundaryFlatSubspace p K // z ≠ 0},
    RCLike.re
        (inner ℂ
          (parityCompressedCanonical p L K z)
          z) /
      ‖(z : euclideanParityBoundaryFlatSubspace p K)‖ ^ 2

/-- The Rayleigh family is bounded below by minus the operator norm. -/
private theorem parityRayleighRange_bddBelow
    (p : ReversalParity) (L : ℝ) (K : ℕ) :
    BddBelow
      (Set.range fun
        z : {z : euclideanParityBoundaryFlatSubspace p K // z ≠ 0} =>
          RCLike.re
              (inner ℂ
                (parityCompressedCanonical p L K z)
                z) /
            ‖(z : euclideanParityBoundaryFlatSubspace p K)‖ ^ 2) := by
  let V := euclideanParityBoundaryFlatSubspace p K
  let T : V →ₗ[ℂ] V := parityCompressedCanonical p L K
  let Tc : V →L[ℂ] V := parityCompressedCanonicalCLM p L K
  refine ⟨-‖Tc‖, ?_⟩
  rintro _ ⟨z, rfl⟩
  have habs :=
    ContinuousLinearMap.rayleighQuotient_le_norm
      (𝕜 := ℂ) Tc (z : V)
  have habs' :
      |RCLike.re (inner ℂ (Tc (z : V)) (z : V)) /
          ‖(z : V)‖ ^ 2| ≤ ‖Tc‖ := by
    simpa only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply] using habs
  have hTcT : Tc (z : V) = T z := rfl
  rw [hTcT] at habs'
  exact neg_le_of_abs_le habs'

/-- The bottom is below the Rayleigh quotient of every nonzero vector. -/
theorem parityRayleighBottom_le_rayleigh
    (p : ReversalParity) (L : ℝ) (K : ℕ)
    (x : euclideanParityBoundaryFlatSubspace p K)
    (hx : x ≠ 0) :
    parityRayleighBottom p L K ≤
      RCLike.re
          (inner ℂ
            (parityCompressedCanonical p L K x)
            x) /
        ‖x‖ ^ 2 := by
  unfold parityRayleighBottom
  exact ciInf_le (parityRayleighRange_bddBelow p L K) ⟨x, hx⟩

/-- Denominator-free Rayleigh lower bound, including the zero vector. -/
theorem parityRayleighBottom_mul_norm_sq_le
    (p : ReversalParity) (L : ℝ) (K : ℕ)
    (x : euclideanParityBoundaryFlatSubspace p K) :
    parityRayleighBottom p L K * ‖x‖ ^ 2 ≤
      RCLike.re
        (inner ℂ
          (parityCompressedCanonical p L K x)
          x) := by
  by_cases hx : x = 0
  · subst x
    simp
  · have h :=
      parityRayleighBottom_le_rayleigh p L K x hx
    have hden : 0 < ‖x‖ ^ 2 := by
      positivity
    exact (le_div_iff₀ hden).mp h

/-- At an arbitrary real shift lambda, the shifted quadratic form lies above
(bottom-lambda) times the norm square. -/
theorem parityRayleighBottom_gap_mul_norm_sq_le_shifted
    (p : ReversalParity) (L : ℝ) (K : ℕ)
    (lam : ℝ)
    (x : euclideanParityBoundaryFlatSubspace p K) :
    (parityRayleighBottom p L K - lam) * ‖x‖ ^ 2 ≤
      Complex.re
        (inner ℂ
          (parityCompressedCanonical p L K x - (lam : ℂ) • x)
          x) := by
  have hbottom :=
    parityRayleighBottom_mul_norm_sq_le p L K x
  have hsmul :
      inner ℂ ((lam : ℂ) • x) x =
        lam • inner ℂ x x := by
    exact inner_smul_real_left (𝕜 := ℂ) x x lam
  have hnorm :
      Complex.re (inner ℂ x x) = ‖x‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using
      (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  rw [inner_sub_left, Complex.sub_re, hsmul, Complex.smul_re,
    hnorm, smul_eq_mul]
  have hbottom' :
      parityRayleighBottom p L K * ‖x‖ ^ 2 ≤
        Complex.re
          (inner ℂ (parityCompressedCanonical p L K x) x) := by
    simpa only [RCLike.re_to_complex] using hbottom
  linarith

/-- Every shift at or below the parity bottom is positive semidefinite. -/
theorem shiftedParityCompressed_nonnegative_of_le_bottom
    (p : ReversalParity) (L : ℝ) (K : ℕ)
    {lam : ℝ}
    (hlam : lam ≤ parityRayleighBottom p L K)
    (x : euclideanParityBoundaryFlatSubspace p K) :
    0 ≤
      Complex.re
        (inner ℂ
          (parityCompressedCanonical p L K x - (lam : ℂ) • x)
          x) := by
  have hgap :=
    parityRayleighBottom_gap_mul_norm_sq_le_shifted
      p L K lam x
  have hleft :
      0 ≤ (parityRayleighBottom p L K - lam) * ‖x‖ ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hlam) (sq_nonneg ‖x‖)
  exact le_trans hleft hgap

/-- A strict gap above the shift is strictly positive on every nonzero vector. -/
theorem shiftedParityCompressed_pos_of_lt_bottom
    (p : ReversalParity) (L : ℝ) (K : ℕ)
    {lam : ℝ}
    (hlam : lam < parityRayleighBottom p L K)
    (x : euclideanParityBoundaryFlatSubspace p K)
    (hx : x ≠ 0) :
    0 <
      Complex.re
        (inner ℂ
          (parityCompressedCanonical p L K x - (lam : ℂ) • x)
          x) := by
  have hgap :=
    parityRayleighBottom_gap_mul_norm_sq_le_shifted
      p L K lam x
  have hnorm : 0 < ‖x‖ ^ 2 := by
    positivity
  have hleft :
      0 < (parityRayleighBottom p L K - lam) * ‖x‖ ^ 2 :=
    mul_pos (sub_pos.mpr hlam) hnorm
  exact lt_of_lt_of_le hleft hgap

/-- The bottom is attained by a genuine eigenmode in every nontrivial successor
parity sector N+1.  Nontriviality is supplied constructively by the already
proved nonzero intrinsic cubic shell coordinate. -/
theorem exists_eigenmode_at_parityRayleighBottom_succ
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hN : 1 ≤ N) :
    ∃ v : euclideanParityBoundaryFlatSubspace p (N + 1),
      v ≠ 0 ∧
      parityCompressedCanonical p L (N + 1) v =
        (parityRayleighBottom p L (N + 1) : ℂ) • v := by
  let V := euclideanParityBoundaryFlatSubspace p (N + 1)
  let T : V →ₗ[ℂ] V := parityCompressedCanonical p L (N + 1)
  let c : V :=
    (intrinsicCubicShellPart p N :
      euclideanParityBoundaryFlatSubspace p (N + 1))
  have hc : c ≠ 0 := by
    intro hc0
    apply intrinsicCubicShellPart_ne_zero p N hN
    apply Subtype.ext
    exact hc0
  letI : Nontrivial V := nontrivial_of_ne c 0 hc
  have hsym : LinearMap.IsSymmetric (𝕜 := ℂ) (E := V) T := by
    simpa only [T, V] using
      parityCompressedCanonical_isSymmetric p L (N + 1)
  have hbottomEig := hsym.hasEigenvalue_iInf_of_finiteDimensional
  obtain ⟨v, hv⟩ := hbottomEig.exists_hasEigenvector
  refine ⟨v, hv.2, ?_⟩
  change T v = (parityRayleighBottom p L (N + 1) : ℂ) • v
  have happly := hv.apply_eq_smul
  simpa [parityRayleighBottom, T, V] using happly

/-- Badness forces the true parity bottom to be strictly negative. -/
theorem parityRayleighBottom_neg_of_parityBad
    {p : ReversalParity} {L : ℝ} {K : ℕ}
    (hbad : ParityBad p L K) :
    parityRayleighBottom p L K < 0 := by
  obtain ⟨x, hxne, hxneg⟩ :=
    exists_negative_compressed_direction_of_parityBad hbad
  have hle :=
    parityRayleighBottom_le_rayleigh p L K x hxne
  have hden : 0 < ‖x‖ ^ 2 := by
    positivity
  have hrqneg :
      RCLike.re
          (inner ℂ (parityCompressedCanonical p L K x) x) /
        ‖x‖ ^ 2 < 0 := by
    exact div_neg_of_neg_of_pos
      (by simpa only [RCLike.re_to_complex] using hxneg) hden
  exact lt_of_le_of_lt hle hrqneg

/-- The common #247 shift: minimum of the two successor parity bottoms. -/
def globalParitySuccessorBottom
    (L : ℝ) (N : ℕ) : ℝ :=
  min
    (parityRayleighBottom .even L (N + 1))
    (parityRayleighBottom .odd L (N + 1))

theorem globalParitySuccessorBottom_le_even
    (L : ℝ) (N : ℕ) :
    globalParitySuccessorBottom L N ≤
      parityRayleighBottom .even L (N + 1) :=
  min_le_left _ _

theorem globalParitySuccessorBottom_le_odd
    (L : ℝ) (N : ℕ) :
    globalParitySuccessorBottom L N ≤
      parityRayleighBottom .odd L (N + 1) :=
  min_le_right _ _

/-- Any bad successor parity makes the common bottom shift negative. -/
theorem globalParitySuccessorBottom_neg_of_anyParityBad
    {L : ℝ} {N : ℕ}
    (hbad : AnyParityBad L (N + 1)) :
    globalParitySuccessorBottom L N < 0 := by
  rcases hbad with heven | hodd
  · exact lt_of_le_of_lt
      (globalParitySuccessorBottom_le_even L N)
      (parityRayleighBottom_neg_of_parityBad heven)
  · exact lt_of_le_of_lt
      (globalParitySuccessorBottom_le_odd L N)
      (parityRayleighBottom_neg_of_parityBad hodd)

/-- At successor size N+1 with N nonzero, negativity of the common
parity bottom is exactly the existing AnyParityBad condition.  This theorem
makes explicit that the global-bottom coordinate is a spectral normal form for
badness, not an independent terminal obstruction. -/
theorem globalParitySuccessorBottom_neg_iff_anyParityBad
    {L : ℝ} {N : ℕ}
    (hN : 1 ≤ N) :
    globalParitySuccessorBottom L N < 0 ↔
      AnyParityBad L (N + 1) := by
  constructor
  · intro hneg
    by_cases hle :
        parityRayleighBottom .even L (N + 1) ≤
          parityRayleighBottom .odd L (N + 1)
    · have hevenNeg :
          parityRayleighBottom .even L (N + 1) < 0 := by
        rw [globalParitySuccessorBottom, min_eq_left hle] at hneg
        exact hneg
      obtain ⟨v, hvne, hveig⟩ :=
        exists_eigenmode_at_parityRayleighBottom_succ .even L N hN
      exact Or.inl
        (parityBad_of_negative_eigenmode hevenNeg hvne hveig)
    · have hoddlt :
          parityRayleighBottom .odd L (N + 1) <
            parityRayleighBottom .even L (N + 1) :=
        lt_of_not_ge hle
      have hoddNeg :
          parityRayleighBottom .odd L (N + 1) < 0 := by
        rw [globalParitySuccessorBottom,
          min_eq_right (le_of_lt hoddlt)] at hneg
        exact hneg
      obtain ⟨v, hvne, hveig⟩ :=
        exists_eigenmode_at_parityRayleighBottom_succ .odd L N hN
      exact Or.inr
        (parityBad_of_negative_eigenmode hoddNeg hvne hveig)
  · exact globalParitySuccessorBottom_neg_of_anyParityBad

/-- At the common minimum shift both successor parity operators are
positive semidefinite. -/
theorem globalParitySuccessorBottom_shifted_nonnegative
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x : euclideanParityBoundaryFlatSubspace p (N + 1)) :
    0 ≤
      Complex.re
        (inner ℂ
          (parityCompressedCanonical p L (N + 1) x -
            (globalParitySuccessorBottom L N : ℂ) • x)
          x) := by
  cases p with
  | even =>
      exact shiftedParityCompressed_nonnegative_of_le_bottom
        .even L (N + 1)
        (globalParitySuccessorBottom_le_even L N) x
  | odd =>
      exact shiftedParityCompressed_nonnegative_of_le_bottom
        .odd L (N + 1)
        (globalParitySuccessorBottom_le_odd L N) x

/-- Exact parity-bottom trichotomy used by the #247 secular layer. -/
theorem paritySuccessorBottom_trichotomy
    (L : ℝ) (N : ℕ) :
    parityRayleighBottom .even L (N + 1) <
        parityRayleighBottom .odd L (N + 1) ∨
      parityRayleighBottom .even L (N + 1) =
        parityRayleighBottom .odd L (N + 1) ∨
      parityRayleighBottom .odd L (N + 1) <
        parityRayleighBottom .even L (N + 1) := by
  exact lt_trichotomy
    (parityRayleighBottom .even L (N + 1))
    (parityRayleighBottom .odd L (N + 1))

end Zeta23.CCM

#print axioms Zeta23.CCM.parityRayleighBottom_mul_norm_sq_le
#print axioms Zeta23.CCM.parityRayleighBottom_gap_mul_norm_sq_le_shifted
#print axioms Zeta23.CCM.exists_eigenmode_at_parityRayleighBottom_succ
#print axioms Zeta23.CCM.parityRayleighBottom_neg_of_parityBad
#print axioms Zeta23.CCM.globalParitySuccessorBottom_neg_of_anyParityBad
#print axioms Zeta23.CCM.globalParitySuccessorBottom_neg_iff_anyParityBad
#print axioms Zeta23.CCM.globalParitySuccessorBottom_shifted_nonnegative
