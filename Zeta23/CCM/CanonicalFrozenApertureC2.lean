import Zeta23.CCM.CanonicalApertureSourceHolomorphy
import Zeta23.CCM.FrozenCanonicalSourceComplex
import Zeta23.CCM.FrozenCanonicalSourceAnalytic
import Zeta23.CCM.CanonicalCompressedSeamJets
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set Filter
open scoped Topology BigOperators ComplexConjugate

/-!
# Post-#282 frozen production aperture calculus

The production floor is frozen before differentiation.  Every frozen source
entry is the restriction of the already-proved complex analytic continuation,
plus the explicit `-log L` scalar.  This gives genuine real C2 regularity on
the positive axis without differentiating the prime staircase.

The physical family is locally one frozen family in the interior.  At a
logarithmic integer threshold its left and right frozen continuations differ
only by the entering source atom.  `CanonicalCompressedSeamJets` proves the
first two legal-carrier jets of that atom vanish at entry.
-/

/-- Exact cutoff frozen at one evaluation aperture. -/
def canonicalDerivativeCutoff (L : ℝ) : ℕ :=
  ⌊Real.exp L⌋₊

/-- Entrywise first derivative of one fixed-cutoff production matrix. -/
def frozenCanonicalSourceFirstMatrix
    (Q : ℕ) (L : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  fun i j => deriv (fun s : ℝ => frozenCanonicalSourceMatrix Q s K i j) L

/-- Entrywise second derivative of one fixed-cutoff production matrix. -/
def frozenCanonicalSourceSecondMatrix
    (Q : ℕ) (L : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  fun i j =>
    deriv (fun s : ℝ => frozenCanonicalSourceFirstMatrix Q s K i j) L

/-- One entry of the frozen production source is genuinely C2 at every positive
real aperture.  The proof consumes the existing complex analytic continuation;
no floor is differentiated. -/
theorem contDiffAt_frozenCanonicalSourceMatrix_apply_pos
    (Q K : ℕ) (i j : Fin (2 * K + 1))
    {L : ℝ} (hL : 0 < L) :
    ContDiffAt ℝ 2
      (fun s : ℝ => frozenCanonicalSourceMatrix Q s K i j) L := by
  have hz :
      (L : ℂ) ∈ complexFrozenSourceDomain := by
    simpa using (ofReal_mem_complexFrozenSourceDomain_iff L).2 hL.ne'
  have han :=
    analyticOnNhd_complexFrozenCanonicalSourceRemainder_apply_sourceDomain
      Q K i j (L : ℂ) hz
  have hc :
      ContDiffAt ℂ 2
        (fun z : ℂ =>
          complexFrozenCanonicalSourceRemainder Q z K i j) (L : ℂ) :=
    han.contDiffAt
  have hcR :
      ContDiffAt ℝ 2
        (fun z : ℂ =>
          complexFrozenCanonicalSourceRemainder Q z K i j) (L : ℂ) :=
    hc.restrict_scalars ℝ
  have hof :
      ContDiffAt ℝ 2 (fun s : ℝ => (s : ℂ)) L :=
    Complex.ofRealCLM.contDiff.contDiffAt
  have hcomp :
      ContDiffAt ℝ 2
        (fun s : ℝ =>
          complexFrozenCanonicalSourceRemainder Q (s : ℂ) K i j) L :=
    hcR.comp L hof
  have hev :
      (fun s : ℝ =>
        complexFrozenCanonicalSourceRemainder Q (s : ℂ) K i j) =ᶠ[𝓝 L]
      (fun s : ℝ => frozenCanonicalSourceRemainderReal Q s K i j) := by
    filter_upwards [Ioi_mem_nhds hL] with s hs
    have hM := complexFrozenCanonicalSourceRemainder_ofReal Q hs K
    exact congrArg (fun M => M i j) hM
  have hrem :
      ContDiffAt ℝ 2
        (fun s : ℝ => frozenCanonicalSourceRemainderReal Q s K i j) L :=
    hcomp.congr_of_eventuallyEq hev.symm
  have hlog :
      ContDiffAt ℝ 2 (fun s : ℝ => (-(Real.log s : ℂ))) L := by
    fun_prop (disch := exact hL.ne')
  have hid :
      ContDiffAt ℝ 2
        (fun s : ℝ =>
          (-(Real.log s : ℂ)) *
            (1 : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ) i j) L :=
    hlog.mul contDiffAt_const
  have hsum := hid.add hrem
  have heq :
      (fun s : ℝ => frozenCanonicalSourceMatrix Q s K i j) =ᶠ[𝓝 L]
      (fun s : ℝ =>
        (-(Real.log s : ℂ)) *
            (1 : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ) i j +
          frozenCanonicalSourceRemainderReal Q s K i j) := by
    filter_upwards [Ioi_mem_nhds hL] with s hs
    have h :=
      frozenCanonicalSourceMatrix_eq_neg_log_identity_add_remainder
        Q K hs
    exact congrArg (fun M => M i j) h
  exact hsum.congr_of_eventuallyEq heq

/-- The first frozen derivative is differentiable, so the second derivative is
the actual derivative rather than a totalized fallback. -/
theorem hasDerivAt_frozenCanonicalSourceFirstMatrix_apply_pos
    (Q K : ℕ) (i j : Fin (2 * K + 1))
    {L : ℝ} (hL : 0 < L) :
    HasDerivAt
      (fun s : ℝ => frozenCanonicalSourceFirstMatrix Q s K i j)
      (frozenCanonicalSourceSecondMatrix Q L K i j) L := by
  unfold frozenCanonicalSourceFirstMatrix frozenCanonicalSourceSecondMatrix
  exact
    (contDiffAt_frozenCanonicalSourceMatrix_apply_pos Q K i j hL).deriv_contDiffAt
      |>.differentiableAt.hasDerivAt

/-- Fixed-cutoff first derivative is the derivative of the actual source entry
at every interior point of that cutoff cell. -/
theorem canonicalSourceMatrix_deriv_eq_frozenFirst_of_mem_cell
    {Q : ℕ} (hQ : 1 ≤ Q)
    {L : ℝ} (hcell : L ∈ fixedCanonicalCutoffCell Q)
    (K : ℕ) (i j : Fin (2 * K + 1)) :
    deriv (fun s : ℝ => canonicalSourceMatrix s K i j) L =
      frozenCanonicalSourceFirstMatrix Q L K i j := by
  have hev :
      (fun s : ℝ => canonicalSourceMatrix s K i j) =ᶠ[𝓝 L]
      (fun s : ℝ => frozenCanonicalSourceMatrix Q s K i j) := by
    have hnhds : fixedCanonicalCutoffCell Q ∈ 𝓝 L :=
      Ioo_mem_nhds hcell.1 hcell.2
    filter_upwards [hnhds] with s hs
    exact congrArg (fun M => M i j)
      (frozenCanonicalSourceMatrix_eq_canonicalSourceMatrix_fixedCell hQ hs K).symm
  exact Filter.EventuallyEq.deriv_eq hev

/-- General frozen-prime update before specializing to the seam value. -/
theorem frozenCanonicalPrimeMatrix_eq_pred_add_entering
    (q K : ℕ) (hq : 2 ≤ q) (L : ℝ) :
    frozenCanonicalPrimeMatrix q L K =
      frozenCanonicalPrimeMatrix (q - 1) L K +
        primeSourceWeight q • sourceMatrix (primeSourceCoordinate q L) K := by
  classical
  have hsucc : q - 1 + 1 = q := by omega
  calc
    frozenCanonicalPrimeMatrix q L K =
        frozenCanonicalPrimeMatrix (q - 1 + 1) L K := by rw [hsucc]
    _ =
        frozenCanonicalPrimeMatrix (q - 1) L K +
          primeSourceWeight (q - 1 + 1) •
            sourceMatrix (primeSourceCoordinate (q - 1 + 1) L) K := by
      unfold frozenCanonicalPrimeMatrix
      rw [Finset.sum_Icc_succ_top (by omega)]
    _ = _ := by rw [hsucc]

/-- The complete q-frozen source differs from the predecessor continuation by
exactly the entering atom with the production minus sign. -/
theorem frozenCanonicalSourceMatrix_eq_pred_sub_entering
    (q K : ℕ) (hq : 2 ≤ q) (L : ℝ) :
    frozenCanonicalSourceMatrix q L K =
      frozenCanonicalSourceMatrix (q - 1) L K -
        primeSourceWeight q • sourceMatrix (primeSourceCoordinate q L) K := by
  unfold frozenCanonicalSourceMatrix
  rw [frozenCanonicalPrimeMatrix_eq_pred_add_entering q K hq L]
  abel

/-- At a seam the entering atom contributes zero value, zero first legal
quadratic jet and zero second legal quadratic jet. -/
theorem frozenSource_seam_energy_jets_agree
    (q K : ℕ) (hq : 2 ≤ q)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    let L := Real.log (q : ℝ)
    Complex.re
      (inner ℂ
        ((frozenCanonicalSourceMatrix q L K).toEuclideanLin x) x) =
      Complex.re
        (inner ℂ
          ((frozenCanonicalSourceMatrix (q - 1) L K).toEuclideanLin x) x) ∧
    deriv
      (fun s : ℝ =>
        Complex.re
          (inner ℂ
            ((frozenCanonicalSourceMatrix q s K).toEuclideanLin x) x)) L =
      deriv
        (fun s : ℝ =>
          Complex.re
            (inner ℂ
              ((frozenCanonicalSourceMatrix (q - 1) s K).toEuclideanLin x) x)) L ∧
    deriv
      (fun s : ℝ =>
        deriv
          (fun r : ℝ =>
            Complex.re
              (inner ℂ
                ((frozenCanonicalSourceMatrix q r K).toEuclideanLin x) x)) s) L =
      deriv
        (fun s : ℝ =>
          deriv
            (fun r : ℝ =>
              Complex.re
                (inner ℂ
                  ((frozenCanonicalSourceMatrix (q - 1) r K).toEuclideanLin x) x)) s) L := by
  dsimp
  constructor
  · rw [frozenCanonicalSourceMatrix_log_nat_eq_pred q K hq]
  · constructor
    · have hdiff :
          (fun s : ℝ =>
            Complex.re
              (inner ℂ
                ((frozenCanonicalSourceMatrix q s K).toEuclideanLin x) x)) =
          (fun s : ℝ =>
            Complex.re
              (inner ℂ
                ((frozenCanonicalSourceMatrix (q - 1) s K).toEuclideanLin x) x) -
              enteringPrimeSourceEnergy q K x s) := by
          funext s
          rw [frozenCanonicalSourceMatrix_eq_pred_sub_entering q K hq s]
          simp [enteringPrimeSourceEnergy, sourceAtomRealEnergy,
            Matrix.toEuclideanLin_sub, inner_sub_left]
      rw [hdiff, deriv_sub]
      · rw [enteringPrimeSourceEnergy_firstJet_zero q K hq x hflat, sub_zero]
      · exact
          (contDiffAt_frozenCanonicalSourceMatrix_apply_pos (q - 1) K 0 0
            (Real.log_pos (by exact_mod_cast hq))).differentiableAt
      · exact
          (show DifferentiableAt ℝ (enteringPrimeSourceEnergy q K x)
              (Real.log q) from
            differentiableAt_of_deriv_ne_zero_or_deriv_eq_zero
              (Or.inr (enteringPrimeSourceEnergy_firstJet_zero q K hq x hflat)))
    · have hjet :=
        enteringPrimeSourceEnergy_secondJet_zero q K hq x hflat
      have hdiff :
          (fun s : ℝ =>
            deriv
              (fun r : ℝ =>
                Complex.re
                  (inner ℂ
                    ((frozenCanonicalSourceMatrix q r K).toEuclideanLin x) x)) s) =
          (fun s : ℝ =>
            deriv
              (fun r : ℝ =>
                Complex.re
                  (inner ℂ
                    ((frozenCanonicalSourceMatrix (q - 1) r K).toEuclideanLin x) x)) s -
            deriv (enteringPrimeSourceEnergy q K x) s) := by
          funext s
          rw [show
            (fun r : ℝ =>
              Complex.re
                (inner ℂ
                  ((frozenCanonicalSourceMatrix q r K).toEuclideanLin x) x)) =
            (fun r : ℝ =>
              Complex.re
                (inner ℂ
                  ((frozenCanonicalSourceMatrix (q - 1) r K).toEuclideanLin x) x) -
                enteringPrimeSourceEnergy q K x r) by
              funext r
              rw [frozenCanonicalSourceMatrix_eq_pred_sub_entering q K hq r]
              simp [enteringPrimeSourceEnergy, sourceAtomRealEnergy,
                Matrix.toEuclideanLin_sub, inner_sub_left]]
          rw [deriv_sub]
      rw [hdiff, deriv_sub, hjet, sub_zero]

end Zeta23.CCM

#print axioms Zeta23.CCM.contDiffAt_frozenCanonicalSourceMatrix_apply_pos
#print axioms Zeta23.CCM.canonicalSourceMatrix_deriv_eq_frozenFirst_of_mem_cell
#print axioms Zeta23.CCM.frozenCanonicalPrimeMatrix_eq_pred_add_entering
#print axioms Zeta23.CCM.frozenSource_seam_energy_jets_agree
