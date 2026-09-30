import Zeta23.CCM.ParityRayleighPerturbation
import Zeta23.CCM.CanonicalApertureContinuity
import Zeta23.CCM.FrozenCanonicalSourceAnalytic
import Mathlib.Topology.Order.LeftRight
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators Topology

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

/-- A frozen complete source entry is continuous throughout the positive
aperture axis. -/
theorem continuous_frozenCanonicalSourceMatrix_apply_pos
    (Q K : ℕ) (i j : Fin (2 * K + 1)) :
    Continuous
      (fun L : Ioi (0 : ℝ) =>
        frozenCanonicalSourceMatrix Q (L : ℝ) K i j) := by
  have hpoleReal :=
    continuous_poleComponent_pos (centeredIndex K i) (centeredIndex K j)
  have harchReal :=
    continuous_sourceEq44ArchComponent_pos (centeredIndex K i) (centeredIndex K j)
  have hpole :
      Continuous
        (fun L : Ioi (0 : ℝ) =>
          (poleComponent
            (centeredIndex K i) (centeredIndex K j) (L : ℝ) : ℂ)) := by
    exact Complex.continuous_ofReal.comp hpoleReal
  have harch :
      Continuous
        (fun L : Ioi (0 : ℝ) =>
          (sourceEq44ArchComponent
            (centeredIndex K i) (centeredIndex K j) (L : ℝ) : ℂ)) := by
    exact Complex.continuous_ofReal.comp harchReal
  have hprime :=
    continuous_frozenCanonicalPrimeMatrix_apply_pos Q K i j
  change
    Continuous
      (fun L : Ioi (0 : ℝ) =>
        (poleComponent
          (centeredIndex K i) (centeredIndex K j) (L : ℝ) : ℂ) -
          (sourceEq44ArchComponent
            (centeredIndex K i) (centeredIndex K j) (L : ℝ) : ℂ) -
            frozenCanonicalPrimeMatrix Q (L : ℝ) K i j)
  exact (hpole.sub harch).sub hprime

/-- Frozen and production complete source matrices agree whenever the
production natural cutoff is the frozen horizon. -/
theorem frozenCanonicalSourceMatrix_eq_canonicalSourceMatrix_of_floor
    (Q : ℕ) (L : ℝ) (K : ℕ)
    (hfloor : ⌊Real.exp L⌋₊ = Q) :
    frozenCanonicalSourceMatrix Q L K = canonicalSourceMatrix L K := by
  rw [frozenCanonicalSourceMatrix,
    canonicalSourceMatrix_eq_pole_sub_arch_sub_prime,
    frozenCanonicalPrimeMatrix_eq_canonicalPrimeMatrix
      (Q := Q) L K hfloor]

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
      have hsucc : q - 1 + 1 = q := by omega
      have hcell :
          L ∈ fixedCanonicalCutoffCell (q - 1) := by
        simpa [fixedCanonicalCutoffCell, hsucc] using hL
      have hfloor :=
        natFloor_exp_eq_on_fixedCanonicalCutoffCell
          (Q := q - 1) hpred hcell
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

/-- Every positive aperture is either a logarithmic integer seam or lies
strictly inside the physical cutoff cell selected by its production floor. -/
theorem continuousAt_canonicalSourceMatrix_apply_of_pos
    (K : ℕ) (i j : Fin (2 * K + 1))
    {L : ℝ} (hL : 0 < L) :
    ContinuousAt
      (fun t : ℝ => canonicalSourceMatrix t K i j) L := by
  let Q : ℕ := ⌊Real.exp L⌋₊
  have hexp1 : (1 : ℝ) < Real.exp L := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hL
  have hQpos : 0 < Q := by
    exact Nat.floor_pos.mpr (le_of_lt hexp1)
  have hQ : 1 ≤ Q := by omega
  have hQlower : (Q : ℝ) ≤ Real.exp L := by
    exact Nat.floor_le (Real.exp_pos L).le
  have hQupper : Real.exp L < ((Q + 1 : ℕ) : ℝ) := by
    simpa [Q, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (Real.exp L))
  by_cases hseam : (Q : ℝ) = Real.exp L
  · have hQtwo : 2 ≤ Q := by
      have h1Q : (1 : ℝ) < (Q : ℝ) := by
        rw [hseam]
        exact hexp1
      exact_mod_cast h1Q
    have hlog : L = Real.log (Q : ℝ) := by
      calc
        L = Real.log (Real.exp L) := (Real.log_exp L).symm
        _ = Real.log (Q : ℝ) := by rw [hseam]
    rw [hlog]
    exact continuousAt_canonicalSourceMatrix_apply_log_nat Q K hQtwo i j
  · have hQstrict : (Q : ℝ) < Real.exp L :=
      lt_of_le_of_ne hQlower hseam
    have hQrealpos : (0 : ℝ) < (Q : ℝ) := by
      exact_mod_cast hQpos
    have hQ1realpos : (0 : ℝ) < ((Q + 1 : ℕ) : ℝ) := by positivity
    have hleft : Real.log (Q : ℝ) < L := by
      have h :=
        Real.strictMonoOn_log hQrealpos (Real.exp_pos L) hQstrict
      simpa using h
    have hright : L < Real.log ((Q + 1 : ℕ) : ℝ) := by
      have h :=
        Real.strictMonoOn_log (Real.exp_pos L) hQ1realpos hQupper
      simpa using h
    have hcell : L ∈ fixedCanonicalCutoffCell Q := ⟨hleft, hright⟩
    have hwithin :=
      (continuousOn_canonicalSourceMatrix_apply_fixedCell
        Q K hQ i j) L hcell
    exact hwithin.continuousAt
      ((isOpen_fixedCanonicalCutoffCell Q).mem_nhds hcell)

/-- Every production canonical matrix entry is continuous on the complete
positive aperture axis, including all floor cutoffs. -/
theorem continuousOn_canonicalSourceMatrix_apply_Ioi
    (K : ℕ) (i j : Fin (2 * K + 1)) :
    ContinuousOn
      (fun L : ℝ => canonicalSourceMatrix L K i j)
      (Ioi (0 : ℝ)) := by
  intro L hL
  exact
    (continuousAt_canonicalSourceMatrix_apply_of_pos K i j hL).continuousWithinAt

/-- Matrix-valued production continuity in the ordinary finite product
topology.  The legal parity carrier itself is independent of aperture. -/
theorem continuousOn_canonicalSourceMatrix_Ioi
    (K : ℕ) :
    ContinuousOn
      (fun L : ℝ => canonicalSourceMatrix L K)
      (Ioi (0 : ℝ)) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  exact continuousOn_canonicalSourceMatrix_apply_Ioi K i j

/-- The production canonical matrix is continuous after bundling it as the
ambient Euclidean continuous linear operator.  Finite-dimensionality supplies
continuity of the linear matrix-to-operator equivalence in the repository's
ordinary matrix topology. -/
theorem continuousOn_canonicalSourceMatrix_toEuclideanCLM_Ioi
    (K : ℕ) :
    ContinuousOn
      (fun L : ℝ =>
        Matrix.toEuclideanCLM
          (n := Fin (2 * K + 1)) (𝕜 := ℂ)
          (canonicalSourceMatrix L K))
      (Ioi (0 : ℝ)) := by
  have hto :
      Continuous
        (Matrix.toEuclideanCLM
          (n := Fin (2 * K + 1)) (𝕜 := ℂ)) := by
    exact
      LinearMap.continuous_of_finiteDimensional
        (Matrix.toEuclideanCLM
          (n := Fin (2 * K + 1)) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap
  exact hto.comp_continuousOn (continuousOn_canonicalSourceMatrix_Ioi K)

/-- Aperture-continuity of the exact parity-compressed canonical operator in
operator norm.  The parity carrier and both orthogonal maps are fixed in L. -/
theorem continuousOn_parityCompressedCanonicalCLM_Ioi
    (p : ReversalParity) (K : ℕ) :
    ContinuousOn
      (fun L : ℝ => parityCompressedCanonicalCLM p L K)
      (Ioi (0 : ℝ)) := by
  let V := euclideanParityBoundaryFlatSubspace p K
  have hamb :=
    continuousOn_canonicalSourceMatrix_toEuclideanCLM_Ioi K
  have hsub :
      ContinuousOn
        (fun _ : ℝ =>
          (V.subtypeL :
            V →L[ℂ] EuclideanSpace ℂ (Fin (2 * K + 1))))
        (Ioi (0 : ℝ)) :=
    continuousOn_const
  have hmid :
      ContinuousOn
        (fun L : ℝ =>
          (Matrix.toEuclideanCLM
            (n := Fin (2 * K + 1)) (𝕜 := ℂ)
            (canonicalSourceMatrix L K)).comp
              (V.subtypeL :
                V →L[ℂ] EuclideanSpace ℂ (Fin (2 * K + 1))))
        (Ioi (0 : ℝ)) :=
    hamb.clm_comp hsub
  have hproj :
      ContinuousOn
        (fun _ : ℝ =>
          (V.orthogonalProjectionOnto :
            EuclideanSpace ℂ (Fin (2 * K + 1)) →L[ℂ] V))
        (Ioi (0 : ℝ)) :=
    continuousOn_const
  have hfull :
      ContinuousOn
        (fun L : ℝ =>
          (V.orthogonalProjectionOnto :
            EuclideanSpace ℂ (Fin (2 * K + 1)) →L[ℂ] V).comp
              ((Matrix.toEuclideanCLM
                (n := Fin (2 * K + 1)) (𝕜 := ℂ)
                (canonicalSourceMatrix L K)).comp
                  (V.subtypeL :
                    V →L[ℂ] EuclideanSpace ℂ (Fin (2 * K + 1)))))
        (Ioi (0 : ℝ)) :=
    hproj.clm_comp hmid
  refine hfull.congr ?_
  intro L hL
  ext x
  rfl

/-- Multiplicity-safe continuity of one successor parity Rayleigh bottom.  The
proof uses only operator-norm continuity and the already-proved Rayleigh
perturbation inequality; no eigenvector is selected continuously. -/
theorem continuousOn_parityRayleighBottom_succ_Ioi
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N) :
    ContinuousOn
      (fun L : ℝ => parityRayleighBottom p L (N + 1))
      (Ioi (0 : ℝ)) := by
  intro L hL
  apply Metric.continuousWithinAt_iff'.2
  intro ε hε
  have hT :=
    (continuousOn_parityCompressedCanonicalCLM_Ioi p (N + 1)) L hL
  have hTmetric :
      ∀ δ > 0,
        ∀ᶠ L' in 𝓝[Ioi (0 : ℝ)] L,
          dist
            (parityCompressedCanonicalCLM p L' (N + 1))
            (parityCompressedCanonicalCLM p L (N + 1)) < δ := by
    with_reducible_and_instances
      exact Metric.continuousWithinAt_iff'.1 hT
  filter_upwards [hTmetric ε hε] with L' hdist
  have hpert :=
    parityRayleighPerturbationBound_of_clmNorm
      p L' L (N + 1)
  have hbottom :=
    abs_parityRayleighBottom_sub_le_of_perturbation_succ
      p L' L
      ‖parityCompressedCanonicalCLM p L' (N + 1) -
        parityCompressedCanonicalCLM p L (N + 1)‖
      N hN hpert
  have hnormlt :
      ‖parityCompressedCanonicalCLM p L' (N + 1) -
        parityCompressedCanonicalCLM p L (N + 1)‖ < ε := by
    with_reducible_and_instances
      simpa only [dist_eq_norm_sub] using hdist
  have habslt :
      |parityRayleighBottom p L' (N + 1) -
        parityRayleighBottom p L (N + 1)| < ε :=
    lt_of_le_of_lt hbottom hnormlt
  simpa [Real.dist_eq] using habslt

/-- The actual legal fixed-N successor ground, the minimum of the two parity
bottoms, is continuous throughout the positive aperture axis. -/
theorem continuousOn_globalParitySuccessorBottom_Ioi
    (N : ℕ) (hN : 1 ≤ N) :
    ContinuousOn
      (fun L : ℝ => globalParitySuccessorBottom L N)
      (Ioi (0 : ℝ)) := by
  unfold globalParitySuccessorBottom
  have heven :=
    continuousOn_parityRayleighBottom_succ_Ioi .even N hN
  have hodd :=
    continuousOn_parityRayleighBottom_succ_Ioi .odd N hN
  simpa [Function.comp_def] using
    continuous_min.comp_continuousOn (heven.prodMk hodd)

/-- Exact continuity obligation for every nontrivial fixed successor index.
The seam-value theorem above is a production ingredient; this proposition is
not promoted until the full positive-axis ground proof is compiler-closed. -/
def CanonicalFixedNGroundContinuity : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    ContinuousOn
      (fun L : ℝ => globalParitySuccessorBottom L N)
      (Ioi (0 : ℝ))

/-- Production theorem closing the post-#277 topology gate:
every nontrivial fixed successor ground is continuous for all positive
apertures. -/
theorem canonicalFixedNGroundContinuity_proved :
    CanonicalFixedNGroundContinuity := by
  intro N hN
  exact continuousOn_globalParitySuccessorBottom_Ioi N hN

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
#print axioms Zeta23.CCM.continuousOn_canonicalSourceMatrix_apply_Ioi
#print axioms Zeta23.CCM.continuousOn_parityRayleighBottom_succ_Ioi
#print axioms Zeta23.CCM.continuousOn_globalParitySuccessorBottom_Ioi
#print axioms Zeta23.CCM.canonicalFixedNGroundContinuity_proved
#print axioms Zeta23.CCM.continuousOn_globalParitySuccessorBottom_Ioi_of_fixedN
