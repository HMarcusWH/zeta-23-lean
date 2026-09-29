import Zeta23.CCM.ParityRayleighPerturbation
import Zeta23.CCM.CanonicalApertureContinuity
import Mathlib.Topology.Order.LeftRight

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators

/-!
# Post-#277 fixed-N legal-ground continuity

PR #277 proves fixed-N sign opposition under a hypothetical off-line zeta zero.
The remaining subterminal topology gate is continuity in aperture of the exact
legal successor ground.

The first layer below closes the value-gluing problem at every logarithmic
integer cutoff seam.  The production finite-prime sum changes its syntactic
horizon at `L = log q`, but the entering source atom has coordinate zero there
and hence contributes the zero matrix.

No simplicity, moving eigenbranch, aperture monotonicity, all-aperture
positivity, or RH premise is used.
-/

/-- The complete canonical source matrix with a frozen finite-prime horizon.
Unlike the production matrix, this is an ordinary continuous finite expression
on the positive aperture axis. -/
def frozenCanonicalSourceMatrix
    (Q : ℕ) (L : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  fun i j =>
    (poleComponent (centeredIndex K i) (centeredIndex K j) L : ℂ) -
      (sourceEq44ArchComponent (centeredIndex K i) (centeredIndex K j) L : ℂ) -
        frozenCanonicalPrimeMatrix Q L K i j

/-- A frozen complete source entry is continuous throughout the positive
aperture axis. -/
theorem continuous_frozenCanonicalSourceMatrix_apply_pos
    (Q K : ℕ) (i j : Fin (2 * K + 1)) :
    Continuous
      (fun L : Ioi (0 : ℝ) =>
        frozenCanonicalSourceMatrix Q (L : ℝ) K i j) := by
  let n : ℤ := centeredIndex K i
  let m : ℤ := centeredIndex K j
  have hpoleReal := continuous_poleComponent_pos n m
  have harchReal := continuous_sourceEq44ArchComponent_pos n m
  have hpole :
      Continuous (fun L : Ioi (0 : ℝ) => (poleComponent n m (L : ℝ) : ℂ)) := by
    exact Complex.continuous_ofReal.comp hpoleReal
  have harch :
      Continuous
        (fun L : Ioi (0 : ℝ) =>
          (sourceEq44ArchComponent n m (L : ℝ) : ℂ)) := by
    exact Complex.continuous_ofReal.comp harchReal
  have hprime :=
    continuous_frozenCanonicalPrimeMatrix_apply_pos Q K i j
  simpa [frozenCanonicalSourceMatrix, n, m] using
    (hpole.sub harch).sub hprime

/-- Frozen and production complete source matrices agree whenever the
production natural cutoff is the frozen horizon. -/
theorem frozenCanonicalSourceMatrix_eq_canonicalSourceMatrix_of_floor
    (Q : ℕ) (L : ℝ) (K : ℕ)
    (hfloor : ⌊Real.exp L⌋₊ = Q) :
    frozenCanonicalSourceMatrix Q L K = canonicalSourceMatrix L K := by
  have hprime :=
    frozenCanonicalPrimeMatrix_eq_canonicalPrimeMatrix
      (Q := Q) L K hfloor
  ext i j
  let n : ℤ := centeredIndex K i
  let m : ℤ := centeredIndex K j
  have hprimeEntry :
      frozenCanonicalPrimeMatrix Q L K i j =
        (primeComponent n m L : ℂ) := by
    calc
      frozenCanonicalPrimeMatrix Q L K i j =
          canonicalPrimeMatrix L K i j := by
        exact congrArg (fun M => M i j) hprime
      _ = (primeComponent n m L : ℂ) := rfl
  calc
    frozenCanonicalSourceMatrix Q L K i j =
        (poleComponent n m L : ℂ) -
          (sourceEq44ArchComponent n m L : ℂ) -
            frozenCanonicalPrimeMatrix Q L K i j := by
      rfl
    _ = (sourceEq44Entry n m L : ℂ) := by
      unfold sourceEq44Entry
      push_cast
      rw [hprimeEntry]
    _ = sourceEq44Matrix L K i j := rfl
    _ = canonicalSourceMatrix L K i j := by
      exact congrArg (fun M => M i j)
        (canonicalSourceMatrix_eq_sourceEq44Matrix L K).symm

/-- At a positive natural logarithmic threshold the production cutoff is the
threshold integer itself. -/
theorem natFloor_exp_log_nat
    (q : ℕ) (hq : 1 ≤ q) :
    ⌊Real.exp (Real.log (q : ℝ))⌋₊ = q := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hq)
  rw [Real.exp_log hqpos]
  simp

/-- The newly admitted q atom is exactly zero at its own logarithmic seam, so
the q-frozen and (q-1)-frozen prime matrices have identical seam values. -/
theorem frozenCanonicalPrimeMatrix_log_nat_eq_pred
    (q K : ℕ) (hq : 2 ≤ q) :
    frozenCanonicalPrimeMatrix q (Real.log (q : ℝ)) K =
      frozenCanonicalPrimeMatrix (q - 1) (Real.log (q : ℝ)) K := by
  classical
  have hsucc : q - 1 + 1 = q := by omega
  calc
    frozenCanonicalPrimeMatrix q (Real.log (q : ℝ)) K =
        frozenCanonicalPrimeMatrix (q - 1 + 1) (Real.log (q : ℝ)) K := by
      rw [hsucc]
    _ =
        frozenCanonicalPrimeMatrix (q - 1) (Real.log (q : ℝ)) K +
          primeSourceWeight (q - 1 + 1) •
            sourceMatrix
              (primeSourceCoordinate (q - 1 + 1) (Real.log (q : ℝ))) K := by
      unfold frozenCanonicalPrimeMatrix
      rw [Finset.sum_Icc_succ_top (by omega)]
    _ = frozenCanonicalPrimeMatrix (q - 1) (Real.log (q : ℝ)) K := by
      rw [hsucc, sourceMatrix_primeSourceCoordinate_log_self q K hq]
      simp

/-- The same seam identity for the complete frozen canonical source matrix. -/
theorem frozenCanonicalSourceMatrix_log_nat_eq_pred
    (q K : ℕ) (hq : 2 ≤ q) :
    frozenCanonicalSourceMatrix q (Real.log (q : ℝ)) K =
      frozenCanonicalSourceMatrix (q - 1) (Real.log (q : ℝ)) K := by
  unfold frozenCanonicalSourceMatrix
  rw [frozenCanonicalPrimeMatrix_log_nat_eq_pred q K hq]

/-- Production value at a logarithmic integer seam equals either frozen
continuation because the entering atom vanishes exactly. -/
theorem canonicalSourceMatrix_log_nat_eq_frozen_pred
    (q K : ℕ) (hq : 2 ≤ q) :
    canonicalSourceMatrix (Real.log (q : ℝ)) K =
      frozenCanonicalSourceMatrix (q - 1) (Real.log (q : ℝ)) K := by
  have hfloor :
      ⌊Real.exp (Real.log (q : ℝ))⌋₊ = q :=
    natFloor_exp_log_nat q (by omega)
  have hqFrozen :=
    frozenCanonicalSourceMatrix_eq_canonicalSourceMatrix_of_floor
      q (Real.log (q : ℝ)) K hfloor
  calc
    canonicalSourceMatrix (Real.log (q : ℝ)) K =
        frozenCanonicalSourceMatrix q (Real.log (q : ℝ)) K := hqFrozen.symm
    _ = frozenCanonicalSourceMatrix (q - 1) (Real.log (q : ℝ)) K :=
      frozenCanonicalSourceMatrix_log_nat_eq_pred q K hq

/-- Exact seam continuity of every production matrix entry.  This closes the
C0 value-gluing problem at every integer cutoff threshold q >= 2, including
both true von-Mangoldt seams and zero-weight controls. -/
theorem continuousAt_canonicalSourceMatrix_apply_log_nat
    (q K : ℕ) (hq : 2 ≤ q)
    (i j : Fin (2 * K + 1)) :
    ContinuousAt
      (fun L : ℝ => canonicalSourceMatrix L K i j)
      (Real.log (q : ℝ)) := by
  have hpred : 1 ≤ q - 1 := by omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (by omega : 0 < q)
  have hpredpos : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < q - 1)
  have hnextpos : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
  have hlogpos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast hq)
  have hpredlt :
      Real.log ((q - 1 : ℕ) : ℝ) < Real.log (q : ℝ) :=
    Real.strictMonoOn_log hpredpos hqpos (by exact_mod_cast (by omega : q - 1 < q))
  have hnextlt :
      Real.log (q : ℝ) < Real.log ((q + 1 : ℕ) : ℝ) :=
    Real.strictMonoOn_log hqpos hnextpos (by exact_mod_cast Nat.lt_succ_self q)
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · let f : ℝ → ℂ :=
      fun L => frozenCanonicalSourceMatrix (q - 1) L K i j
    have hfOn :
        ContinuousOn f (Ioi (0 : ℝ)) := by
      exact continuousOn_iff_continuous_domRestrict.mpr
        (continuous_frozenCanonicalSourceMatrix_apply_pos (q - 1) K i j)
    have hfAt : ContinuousAt f (Real.log (q : ℝ)) :=
      (hfOn _ hlogpos).continuousAt (isOpen_Ioi.mem_nhds hlogpos)
    have hevent :
        (fun L : ℝ => canonicalSourceMatrix L K i j) =ᶠ[𝓝[<] Real.log (q : ℝ)] f := by
      filter_upwards [Ioo_mem_nhdsLT hpredlt] with L hL
      have hfloor :=
        natFloor_exp_eq_on_fixedCanonicalCutoffCell
          (Q := q - 1) hpred hL
      have heq :=
        frozenCanonicalSourceMatrix_eq_canonicalSourceMatrix_of_floor
          (q - 1) L K hfloor
      exact (congrArg (fun M => M i j) heq).symm
    have hvalue :
        canonicalSourceMatrix (Real.log (q : ℝ)) K i j =
          f (Real.log (q : ℝ)) := by
      exact congrArg (fun M => M i j)
        (canonicalSourceMatrix_log_nat_eq_frozen_pred q K hq)
    exact hfAt.continuousWithinAt.congr_of_eventuallyEq hevent hvalue
  · let f : ℝ → ℂ :=
      fun L => frozenCanonicalSourceMatrix q L K i j
    have hfOn :
        ContinuousOn f (Ioi (0 : ℝ)) := by
      exact continuousOn_iff_continuous_domRestrict.mpr
        (continuous_frozenCanonicalSourceMatrix_apply_pos q K i j)
    have hfAt : ContinuousAt f (Real.log (q : ℝ)) :=
      (hfOn _ hlogpos).continuousAt (isOpen_Ioi.mem_nhds hlogpos)
    have hevent :
        (fun L : ℝ => canonicalSourceMatrix L K i j) =ᶠ[𝓝[>] Real.log (q : ℝ)] f := by
      filter_upwards [Ioo_mem_nhdsGT hnextlt] with L hL
      have hfloor :=
        natFloor_exp_eq_on_fixedCanonicalCutoffCell
          (Q := q) (by omega) hL
      have heq :=
        frozenCanonicalSourceMatrix_eq_canonicalSourceMatrix_of_floor
          q L K hfloor
      exact (congrArg (fun M => M i j) heq).symm
    have hfloor :
        ⌊Real.exp (Real.log (q : ℝ))⌋₊ = q :=
      natFloor_exp_log_nat q (by omega)
    have heq :=
      frozenCanonicalSourceMatrix_eq_canonicalSourceMatrix_of_floor
        q (Real.log (q : ℝ)) K hfloor
    have hvalue :
        canonicalSourceMatrix (Real.log (q : ℝ)) K i j =
          f (Real.log (q : ℝ)) := by
      exact (congrArg (fun M => M i j) heq).symm
    exact hfAt.continuousWithinAt.congr_of_eventuallyEq hevent hvalue

/-- Exact continuity obligation for every nontrivial fixed successor index.
The seam-value theorem above is a production ingredient; this proposition is
not promoted until the full positive-axis ground proof is compiler-closed. -/
def CanonicalFixedNGroundContinuity : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    ContinuousOn
      (fun L : ℝ => globalParitySuccessorBottom L N)
      (Ioi (0 : ℝ))

/-- Registry/downstream-facing eliminator for the fixed-N continuity
interface.  This theorem does not prove the interface. -/
theorem continuousOn_globalParitySuccessorBottom_Ioi_of_fixedN
    (h : CanonicalFixedNGroundContinuity)
    (N : ℕ) (hN : 1 ≤ N) :
    ContinuousOn
      (fun L : ℝ => globalParitySuccessorBottom L N)
      (Ioi (0 : ℝ)) :=
  h N hN

end Zeta23.CCM

#print axioms Zeta23.CCM.frozenCanonicalPrimeMatrix_log_nat_eq_pred
#print axioms Zeta23.CCM.continuousAt_canonicalSourceMatrix_apply_log_nat
#print axioms Zeta23.CCM.continuousOn_globalParitySuccessorBottom_Ioi_of_fixedN
