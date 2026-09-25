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


/-!
## Post-#267 exact carrier-bottom hierarchy

The next structural step is to put the unconstrained Euclidean carrier, the
complete boundary-flat carrier, and the two parity carriers into one exact
Rayleigh-bottom hierarchy.  This is a ground-value statement, not an ordered
eigenvalue interlacing theorem.

The boundary-flat bottom is defined directly as the infimum of the ambient
canonical Rayleigh quotient over the exact Euclidean boundary-flat subspace.
The parity split then proves that this bottom is exactly the minimum of the
even and odd parity bottoms.

Direction firewall:
* full-space bottom <= boundary-flat bottom;
* boundary-flat bottom = min(even bottom, odd bottom);
* full-space negativity alone does not imply boundary-flat negativity;
* no aperture monotonicity, prime-remainder domination, residual exclusion,
  or RH theorem is asserted.
-/

/-- Unconstrained Euclidean Rayleigh bottom of the canonical finite matrix. -/
def fullCanonicalRayleighBottom
    (L : ℝ) (N : ℕ) : ℝ :=
  ⨅ z : {z : EuclideanSpace ℂ (Fin (2 * N + 1)) // z ≠ 0},
    RCLike.re
        (inner ℂ
          ((canonicalSourceMatrix L N).toEuclideanLin z)
          z) /
      ‖(z : EuclideanSpace ℂ (Fin (2 * N + 1)))‖ ^ 2

/-- Rayleigh bottom of the complete Euclidean boundary-flat carrier. -/
def boundaryFlatRayleighBottom
    (L : ℝ) (N : ℕ) : ℝ :=
  ⨅ z : {z : euclideanBoundaryFlatSubspace N // z ≠ 0},
    RCLike.re
        (inner ℂ
          ((canonicalSourceMatrix L N).toEuclideanLin
            (z : EuclideanSpace ℂ (Fin (2 * N + 1))))
          (z : EuclideanSpace ℂ (Fin (2 * N + 1)))) /
      ‖(z : euclideanBoundaryFlatSubspace N)‖ ^ 2

private def fullCanonicalRayleighRange_bddBelow
    (L : ℝ) (N : ℕ) :
    BddBelow
      (Set.range fun
        z : {z : EuclideanSpace ℂ (Fin (2 * N + 1)) // z ≠ 0} =>
          RCLike.re
              (inner ℂ
                ((canonicalSourceMatrix L N).toEuclideanLin z)
                z) /
            ‖(z : EuclideanSpace ℂ (Fin (2 * N + 1)))‖ ^ 2) := by
  let E := EuclideanSpace ℂ (Fin (2 * N + 1))
  let T : E →ₗ[ℂ] E := (canonicalSourceMatrix L N).toEuclideanLin
  let Tc : E →L[ℂ] E := LinearMap.toContinuousLinearMap T
  refine ⟨-‖Tc‖, ?_⟩
  rintro _ ⟨z, rfl⟩
  have habs :=
    ContinuousLinearMap.rayleighQuotient_le_norm
      (𝕜 := ℂ) Tc (z : E)
  have habs' :
      |RCLike.re (inner ℂ (Tc (z : E)) (z : E)) /
          ‖(z : E)‖ ^ 2| ≤ ‖Tc‖ := by
    simpa only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply] using habs
  have hTcT : Tc (z : E) = T z := rfl
  rw [hTcT] at habs'
  exact neg_le_of_abs_le habs'

private def boundaryFlatRayleighRange_bddBelow
    (L : ℝ) (N : ℕ) :
    BddBelow
      (Set.range fun
        z : {z : euclideanBoundaryFlatSubspace N // z ≠ 0} =>
          RCLike.re
              (inner ℂ
                ((canonicalSourceMatrix L N).toEuclideanLin
                  (z : EuclideanSpace ℂ (Fin (2 * N + 1))))
                (z : EuclideanSpace ℂ (Fin (2 * N + 1)))) /
            ‖(z : euclideanBoundaryFlatSubspace N)‖ ^ 2) := by
  let E := EuclideanSpace ℂ (Fin (2 * N + 1))
  let T : E →ₗ[ℂ] E := (canonicalSourceMatrix L N).toEuclideanLin
  let Tc : E →L[ℂ] E := LinearMap.toContinuousLinearMap T
  refine ⟨-‖Tc‖, ?_⟩
  rintro _ ⟨z, rfl⟩
  have habs :=
    ContinuousLinearMap.rayleighQuotient_le_norm
      (𝕜 := ℂ) Tc
      (z : EuclideanSpace ℂ (Fin (2 * N + 1)))
  have habs' :
      |RCLike.re
          (inner ℂ
            (Tc (z : EuclideanSpace ℂ (Fin (2 * N + 1))))
            (z : EuclideanSpace ℂ (Fin (2 * N + 1)))) /
          ‖(z : euclideanBoundaryFlatSubspace N)‖ ^ 2| ≤ ‖Tc‖ := by
    simpa only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply] using habs
  have hTcT :
      Tc (z : EuclideanSpace ℂ (Fin (2 * N + 1))) =
        T (z : EuclideanSpace ℂ (Fin (2 * N + 1))) := rfl
  rw [hTcT] at habs'
  exact neg_le_of_abs_le habs'

private def boundaryFlatRayleighBottom_le_rayleigh
    (L : ℝ) (N : ℕ)
    (x : euclideanBoundaryFlatSubspace N)
    (hx : x ≠ 0) :
    boundaryFlatRayleighBottom L N ≤
      RCLike.re
          (inner ℂ
            ((canonicalSourceMatrix L N).toEuclideanLin
              (x : EuclideanSpace ℂ (Fin (2 * N + 1))))
            (x : EuclideanSpace ℂ (Fin (2 * N + 1)))) /
        ‖x‖ ^ 2 := by
  unfold boundaryFlatRayleighBottom
  exact ciInf_le (boundaryFlatRayleighRange_bddBelow L N) ⟨x, hx⟩

private def fullCanonicalRayleighBottom_le_rayleigh
    (L : ℝ) (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1)))
    (hx : x ≠ 0) :
    fullCanonicalRayleighBottom L N ≤
      RCLike.re
          (inner ℂ
            ((canonicalSourceMatrix L N).toEuclideanLin x)
            x) /
        ‖x‖ ^ 2 := by
  unfold fullCanonicalRayleighBottom
  exact ciInf_le (fullCanonicalRayleighRange_bddBelow L N) ⟨x, hx⟩

private def euclideanReverseNormEq
    (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    ‖(EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).symm
        (reverseCoefficients N
          ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x))‖ =
      ‖x‖ := by
  have hsq :
      ‖(EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).symm
          (reverseCoefficients N
            ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x))‖ ^ 2 =
        ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    rw [← Equiv.sum_comp Fin.revPerm]
    simp [reverseCoefficients]
  nlinarith
    [norm_nonneg
      ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).symm
        (reverseCoefficients N
          ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x))),
     norm_nonneg x]

private def euclideanEvenOddNormSqSplit
    (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    ‖x‖ ^ 2 =
      ‖(EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).symm
          (evenPart N
            ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x))‖ ^ 2 +
      ‖(EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).symm
          (oddPart N
            ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x))‖ ^ 2 := by
  let E := EuclideanSpace ℂ (Fin (2 * N + 1))
  let u : Fin (2 * N + 1) → ℂ :=
    (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x
  let r : E :=
    (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).symm
      (reverseCoefficients N u)
  let e : E :=
    (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).symm
      (evenPart N u)
  let o : E :=
    (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).symm
      (oddPart N u)
  have hrnorm : ‖r‖ = ‖x‖ := by
    simpa [r, u] using euclideanReverseNormEq N x
  have he :
      e = (1 / 2 : ℂ) • (x + r) := by
    apply (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).injective
    ext i
    simp [e, r, u, evenPart, reverseCoefficients, Pi.smul_apply, smul_eq_mul]
    ring
  have ho :
      o = (1 / 2 : ℂ) • (x - r) := by
    apply (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).injective
    ext i
    simp [o, r, u, oddPart, reverseCoefficients, Pi.smul_apply, smul_eq_mul]
    ring
  have hpara := parallelogram_law_with_norm ℂ x r
  rw [hrnorm] at hpara
  change ‖x‖ ^ 2 = ‖e‖ ^ 2 + ‖o‖ ^ 2
  rw [he, ho, norm_smul, norm_smul]
  norm_num at *
  nlinarith

/-- Restricting from the full finite Euclidean carrier to the exact
boundary-flat carrier can only raise the ground Rayleigh value. -/
theorem fullCanonicalRayleighBottom_le_boundaryFlatRayleighBottom
    (L : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    fullCanonicalRayleighBottom L N ≤
      boundaryFlatRayleighBottom L N := by
  have hfin :
      0 < Module.finrank ℂ (euclideanBoundaryFlatSubspace N) := by
    rw [finrank_euclideanBoundaryFlatSubspace N (by omega)]
    omega
  letI : Nontrivial (euclideanBoundaryFlatSubspace N) :=
    Module.nontrivial_of_finrank_pos hfin
  letI : Nonempty
      {z : euclideanBoundaryFlatSubspace N // z ≠ 0} := by
    obtain ⟨z, hz⟩ : ∃ z : euclideanBoundaryFlatSubspace N, z ≠ 0 :=
      exists_ne 0
    exact ⟨⟨z, hz⟩⟩
  unfold boundaryFlatRayleighBottom
  refine le_ciInf fun z => ?_
  let x : EuclideanSpace ℂ (Fin (2 * N + 1)) :=
    (z : euclideanBoundaryFlatSubspace N)
  have hx : x ≠ 0 := by
    intro hx0
    apply z.property
    apply Subtype.ext
    exact hx0
  simpa [x] using fullCanonicalRayleighBottom_le_rayleigh L N x hx

/-- The complete boundary-flat ground is exactly the minimum of the two
parity-compressed grounds. -/
theorem boundaryFlatRayleighBottom_eq_min_parity
    (L : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    boundaryFlatRayleighBottom L N =
      min
        (parityRayleighBottom .even L N)
        (parityRayleighBottom .odd L N) := by
  have hN1 : 1 ≤ N := by omega

  have hleParity :
      ∀ p : ReversalParity,
        boundaryFlatRayleighBottom L N ≤
          parityRayleighBottom p L N := by
    intro p
    have hfin :
        0 < Module.finrank ℂ
          (euclideanParityBoundaryFlatSubspace p N) := by
      rw [finrank_euclideanParityBoundaryFlatSubspace p N hN1]
      omega
    letI : Nontrivial
        (euclideanParityBoundaryFlatSubspace p N) :=
      Module.nontrivial_of_finrank_pos hfin
    letI : Nonempty
        {z : euclideanParityBoundaryFlatSubspace p N // z ≠ 0} := by
      obtain ⟨z, hz⟩ :
          ∃ z : euclideanParityBoundaryFlatSubspace p N, z ≠ 0 :=
        exists_ne 0
      exact ⟨⟨z, hz⟩⟩
    unfold parityRayleighBottom
    refine le_ciInf fun z => ?_
    let x0 : EuclideanSpace ℂ (Fin (2 * N + 1)) :=
      (z : euclideanParityBoundaryFlatSubspace p N)
    have hxflat : x0 ∈ euclideanBoundaryFlatSubspace N := by
      rw [mem_euclideanBoundaryFlatSubspace_iff]
      cases p with
      | even =>
          exact
            (show
              (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x0 ∈
                evenBoundaryFlatSubspace N from z.val.property).1
      | odd =>
          exact
            (show
              (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x0 ∈
                oddBoundaryFlatSubspace N from z.val.property).1
    let x : euclideanBoundaryFlatSubspace N := ⟨x0, hxflat⟩
    have hx : x ≠ 0 := by
      intro hx0
      apply z.property
      apply Subtype.ext
      exact congrArg Subtype.val hx0
    have hbf := boundaryFlatRayleighBottom_le_rayleigh L N x hx
    have hself :=
      re_inner_parityCompressedCanonical_self p L N
        (z : euclideanParityBoundaryFlatSubspace p N)
    change
      boundaryFlatRayleighBottom L N ≤
        RCLike.re
            (inner ℂ
              (parityCompressedCanonical p L N z)
              z) /
          ‖(z : euclideanParityBoundaryFlatSubspace p N)‖ ^ 2
    rw [hself]
    simpa [x, x0] using hbf

  apply le_antisymm
  · exact le_min (hleParity .even) (hleParity .odd)
  · unfold boundaryFlatRayleighBottom
    refine le_ciInf fun z => ?_
    let x : euclideanBoundaryFlatSubspace N := z
    let x0 : EuclideanSpace ℂ (Fin (2 * N + 1)) := x
    let u : Fin (2 * N + 1) → ℂ :=
      (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x0
    have huflat : u ∈ boundaryFlatSubspace N := by
      exact (mem_euclideanBoundaryFlatSubspace_iff N x0).mp x.property
    let e0 : EuclideanSpace ℂ (Fin (2 * N + 1)) :=
      (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).symm (evenPart N u)
    let o0 : EuclideanSpace ℂ (Fin (2 * N + 1)) :=
      (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).symm (oddPart N u)
    have heMem :
        e0 ∈ euclideanParityBoundaryFlatSubspace .even N := by
      change
        (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) e0 ∈
          evenBoundaryFlatSubspace N
      simpa [e0] using evenPart_mem_evenBoundaryFlatSubspace huflat
    have hoMem :
        o0 ∈ euclideanParityBoundaryFlatSubspace .odd N := by
      change
        (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) o0 ∈
          oddBoundaryFlatSubspace N
      simpa [o0] using oddPart_mem_oddBoundaryFlatSubspace huflat
    let e : euclideanParityBoundaryFlatSubspace .even N := ⟨e0, heMem⟩
    let o : euclideanParityBoundaryFlatSubspace .odd N := ⟨o0, hoMem⟩
    have heLower :=
      parityRayleighBottom_mul_norm_sq_le .even L N e
    have hoLower :=
      parityRayleighBottom_mul_norm_sq_le .odd L N o
    have heAmbient :
        Complex.re
            (inner ℂ
              (parityCompressedCanonical .even L N e)
              e) =
          (quadraticForm (canonicalSourceMatrix L N) (evenPart N u)).re := by
      rw [re_inner_parityCompressedCanonical_self]
      rw [← quadraticForm_re_eq_re_inner_apply_self
        (canonicalSourceMatrix L N) e0]
      simp [e, e0, u]
    have hoAmbient :
        Complex.re
            (inner ℂ
              (parityCompressedCanonical .odd L N o)
              o) =
          (quadraticForm (canonicalSourceMatrix L N) (oddPart N u)).re := by
      rw [re_inner_parityCompressedCanonical_self]
      rw [← quadraticForm_re_eq_re_inner_apply_self
        (canonicalSourceMatrix L N) o0]
      simp [o, o0, u]
    rw [heAmbient] at heLower
    rw [hoAmbient] at hoLower
    have hsplitC :=
      quadraticForm_evenPart_add_oddPart L N u
    have hsplit :
        (quadraticForm (canonicalSourceMatrix L N) (evenPart N u)).re +
            (quadraticForm (canonicalSourceMatrix L N) (oddPart N u)).re =
          (quadraticForm (canonicalSourceMatrix L N) u).re := by
      simpa only [Complex.add_re] using congrArg Complex.re hsplitC
    have hnorm :
        ‖x0‖ ^ 2 = ‖e0‖ ^ 2 + ‖o0‖ ^ 2 := by
      simpa [e0, o0, u] using euclideanEvenOddNormSqSplit N x0
    have hminEven :
        min
            (parityRayleighBottom .even L N)
            (parityRayleighBottom .odd L N) * ‖e‖ ^ 2 ≤
          parityRayleighBottom .even L N * ‖e‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg ‖e‖)
    have hminOdd :
        min
            (parityRayleighBottom .even L N)
            (parityRayleighBottom .odd L N) * ‖o‖ ^ 2 ≤
          parityRayleighBottom .odd L N * ‖o‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg ‖o‖)
    have hden : 0 < ‖x‖ ^ 2 := by
      positivity
    have hquad :
        min
            (parityRayleighBottom .even L N)
            (parityRayleighBottom .odd L N) * ‖x‖ ^ 2 ≤
          RCLike.re
            (inner ℂ
              ((canonicalSourceMatrix L N).toEuclideanLin x0)
              x0) := by
      have hxquad :
          RCLike.re
              (inner ℂ
                ((canonicalSourceMatrix L N).toEuclideanLin x0)
                x0) =
            (quadraticForm (canonicalSourceMatrix L N) u).re := by
        rw [← quadraticForm_re_eq_re_inner_apply_self
          (canonicalSourceMatrix L N) x0]
        simp [u]
      rw [hxquad]
      have henorm : ‖e‖ = ‖e0‖ := rfl
      have honorm : ‖o‖ = ‖o0‖ := rfl
      have hxnorm : ‖x‖ = ‖x0‖ := rfl
      rw [henorm, honorm, hxnorm]
      nlinarith
    exact (le_div_iff₀ hden).2 hquad

/-- Exact full/boundary-flat/parity ground hierarchy for the canonical finite
CCM problem. -/
theorem canonicalCarrierBottom_hierarchy
    (L : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    fullCanonicalRayleighBottom L N ≤
        boundaryFlatRayleighBottom L N ∧
      boundaryFlatRayleighBottom L N =
        min
          (parityRayleighBottom .even L N)
          (parityRayleighBottom .odd L N) := by
  exact ⟨
    fullCanonicalRayleighBottom_le_boundaryFlatRayleighBottom L hN,
    boundaryFlatRayleighBottom_eq_min_parity L hN⟩

/-- The common #247 shift: minimum of the two successor parity bottoms. -/
def globalParitySuccessorBottom
    (L : ℝ) (N : ℕ) : ℝ :=
  min
    (parityRayleighBottom .even L (N + 1))
    (parityRayleighBottom .odd L (N + 1))


/-- At every legal successor size, the existing #247 global parity bottom is
exactly the Rayleigh ground value of the complete boundary-flat carrier. -/
theorem boundaryFlatRayleighBottom_succ_eq_globalParitySuccessorBottom
    (L : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    boundaryFlatRayleighBottom L (N + 1) =
      globalParitySuccessorBottom L N := by
  rw [boundaryFlatRayleighBottom_eq_min_parity L (by omega)]
  rfl

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
#print axioms Zeta23.CCM.canonicalCarrierBottom_hierarchy
#print axioms Zeta23.CCM.boundaryFlatRayleighBottom_succ_eq_globalParitySuccessorBottom
