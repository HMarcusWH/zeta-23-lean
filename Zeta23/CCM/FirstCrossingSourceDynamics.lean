import Zeta23.CCM.FirstCrossingSchurReduction
import Zeta23.CCM.SourceDerivativeTransport
import Zeta23.CCM.MixedSourceDerivativeTransport
import Zeta23.CCM.CanonicalSourceEnergyJets
import Zeta23.CCM.CanonicalSourceMomentJets
import Zeta23.CCM.LiftedPredecessorRegularity
import Zeta23.CCM.CanonicalApertureLocation

noncomputable section

namespace Zeta23.CCM

open scoped Topology

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Post-#278 first-crossing source-dynamics interface

At a regular predecessor block the canonical cubic shell coupling has a unique
zero-shift preimage.  This module packages that preimage and its scalar Schur
endpoint as a canonical function of the regular state.

The source-derivative and endpoint-jet modules are imported here because this
scalar is the object whose production aperture germ must be controlled next.
No sign theorem for that germ is asserted.
-/

/-- Canonical zero-shift preimage on a regular predecessor block. -/
noncomputable def regularCubicZeroShiftPreimage
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hreg : IntrinsicPredecessorRegular p L N) :
    intrinsicParityPredecessorSubspace p N :=
  Classical.choose
    (existsUnique_cubicZeroShiftPreimage_of_regular p L N hreg).exists

/-- The chosen regular preimage solves the actual shell-coupling equation. -/
theorem regularCubicZeroShiftPreimage_spec
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hreg : IntrinsicPredecessorRegular p L N) :
    intrinsicPredecessorBlock p L N
        (regularCubicZeroShiftPreimage p L N hreg) =
      intrinsicShellToPredecessor p L N
        (intrinsicCubicShellPart p N) := by
  exact
    Classical.choose_spec
      (existsUnique_cubicZeroShiftPreimage_of_regular p L N hreg).exists

/-- Canonical regular zero-shift Schur endpoint. -/
noncomputable def regularZeroShiftSchurEndpoint
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hreg : IntrinsicPredecessorRegular p L N) : ℂ :=
  cubicZeroShiftSchurEndpoint p L N
    (regularCubicZeroShiftPreimage p L N hreg)

/-- Exact real-energy normal form of the canonical regular endpoint. -/
theorem regularZeroShiftSchurEndpoint_re_eq_shell_sub_predecessor
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hreg : IntrinsicPredecessorRegular p L N) :
    Complex.re (regularZeroShiftSchurEndpoint p L N hreg) =
      cubicShellRealEnergy p L N -
        intrinsicPredecessorRealEnergy p L N
          (regularCubicZeroShiftPreimage p L N hreg) := by
  unfold regularZeroShiftSchurEndpoint
  exact
    cubicZeroShiftSchurEndpoint_re_eq_shell_sub_predecessorRealEnergy
      p L N
      (regularCubicZeroShiftPreimage p L N hreg)
      (regularCubicZeroShiftPreimage_spec p L N hreg)

/-- At any regular bad successor over a nonnegative predecessor, the canonical
regular endpoint is strictly negative. -/
theorem regularZeroShiftSchurEndpoint_re_neg_of_parityBad
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev : PredecessorSectorNonnegative p L N)
    (hbad : ParityBad p L (N + 1))
    (hreg : IntrinsicPredecessorRegular p L N) :
    Complex.re (regularZeroShiftSchurEndpoint p L N hreg) < 0 := by
  unfold regularZeroShiftSchurEndpoint
  exact
    cubicZeroShiftSchurEndpoint_re_neg_of_parityBad_of_preimage
      p hL N hN hprev hbad
      (regularCubicZeroShiftPreimage p L N hreg)
      (regularCubicZeroShiftPreimage_spec p L N hreg)

/-- Dense regularity turns any nonempty open fixed-cell region consisting
of bad successors over nonnegative predecessors into an actual negative
canonical regular zero-shift endpoint. -/
theorem exists_regularZeroShiftEndpoint_neg_in_open_bad_cell
    {Q : ℕ} (hQ : 1 ≤ Q)
    (p : ReversalParity)
    (N : ℕ) (hN : 1 ≤ N)
    {J : Set ℝ}
    (hJopen : IsOpen J)
    (hJne : J.Nonempty)
    (hJcell : J ⊆ fixedCanonicalCutoffCell Q)
    (hJpos : ∀ L ∈ J, 0 < L)
    (hprev : ∀ L ∈ J, PredecessorSectorNonnegative p L N)
    (hbad : ∀ L ∈ J, ParityBad p L (N + 1)) :
    ∃ L : ℝ, ∃ hLJ : L ∈ J,
      ∃ hreg : IntrinsicPredecessorRegular p L N,
        Complex.re (regularZeroShiftSchurEndpoint p L N hreg) < 0 := by
  obtain ⟨L, hLJ, hreg⟩ :=
    exists_intrinsicPredecessorRegular_in_open_fixedCell
      hQ p N hJopen hJne hJcell
  refine ⟨L, hLJ, hreg, ?_⟩
  exact
    regularZeroShiftSchurEndpoint_re_neg_of_parityBad
      p (hJpos L hLJ) N hN (hprev L hLJ) (hbad L hLJ) hreg


/-- Main structural compression before the production sign barrier:
every canonical first-crossing shell forces regular zero-shift Schur endpoints
with strictly negative real part arbitrarily close to the right of the contact.

The proof uses only:
* right-crossing of the selected successor bottom;
* a right-neighborhood where the predecessor sector is nonnegative;
* continuity of the successor parity bottom;
* a fixed right-cell window;
* dense regularity of the actual intrinsic predecessor determinant.

No production endpoint sign theorem is used. -/
theorem CanonicalParityFirstCrossingShell.exists_arbitrarilyClose_regularZeroShiftEndpoint_neg
    (c : CanonicalParityFirstCrossingShell) :
    ∀ ε : ℝ, 0 < ε →
      ∃ L : ℝ,
        c.Lstar < L ∧
        L < c.Lstar + ε ∧
        PredecessorSectorNonnegative c.p L c.k ∧
        ∃ hreg : IntrinsicPredecessorRegular c.p L c.k,
          Complex.re
            (regularZeroShiftSchurEndpoint c.p L c.k hreg) < 0 := by
  intro ε hε
  have hk1 : 1 ≤ c.k := le_trans c.one_le_n c.n_le_k
  have hstarpos : 0 < c.Lstar :=
    lt_trans c.Lsmall_pos c.Lsmall_lt_Lstar
  obtain ⟨w⟩ := exists_canonicalRightCellWindow_of_pos hstarpos
  obtain ⟨δprev, hδprev, hprevWindow⟩ :=
    c.exists_predecessorSectorNonnegative_right_window
  let η : ℝ := min ε (min w.δ δprev)
  have hη : 0 < η := by
    exact lt_min hε (lt_min w.δ_pos hδprev)
  obtain ⟨L₀, hL₀lo, hL₀hi, hL₀neg⟩ :=
    c.successor_right_crossing η hη

  have hL₀pos : 0 < L₀ := lt_trans hstarpos hL₀lo
  have hcontGround :
      ContinuousAt (fun L : ℝ => paritySuccessorGround c.p c.k L) L₀ := by
    have hwithin :=
      (continuousOn_parityRayleighBottom_succ_Ioi c.p c.k hk1)
        L₀ hL₀pos
    have hat :=
      hwithin.continuousAt (isOpen_Ioi.mem_nhds hL₀pos)
    simpa [paritySuccessorGround] using hat
  have hnegNhds :
      (fun L : ℝ => paritySuccessorGround c.p c.k L) ⁻¹'
          Set.Iio (0 : ℝ) ∈ 𝓝 L₀ :=
    hcontGround.tendsto (isOpen_Iio.mem_nhds hL₀neg)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnegNhds

  let J : Set ℝ :=
    Metric.ball L₀ r ∩ Set.Ioo c.Lstar (c.Lstar + η)
  have hJopen : IsOpen J := by
    exact Metric.isOpen_ball.inter isOpen_Ioo
  have hJne : J.Nonempty := by
    refine ⟨L₀, ?_⟩
    exact ⟨Metric.mem_ball_self hr, ⟨hL₀lo, hL₀hi⟩⟩
  have hJcell : J ⊆ fixedCanonicalCutoffCell w.Q := by
    intro L hLJ
    apply w.window_subset
    refine ⟨hLJ.2.1, ?_⟩
    have hηδ : η ≤ w.δ := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith [hLJ.2.2]
  have hJpos : ∀ L ∈ J, 0 < L := by
    intro L hLJ
    exact lt_trans hstarpos hLJ.2.1
  have hJprev :
      ∀ L ∈ J, PredecessorSectorNonnegative c.p L c.k := by
    intro L hLJ
    apply hprevWindow L hLJ.2.1
    have hηprev : η ≤ δprev :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith [hLJ.2.2]
  have hJbad :
      ∀ L ∈ J, ParityBad c.p L (c.k + 1) := by
    intro L hLJ
    have hmem := hball hLJ.1
    have hnegL :
        paritySuccessorGround c.p c.k L < 0 := by
      simpa using hmem
    exact parityBad_of_paritySuccessorGround_neg
      c.p c.k hk1 hnegL

  obtain ⟨L, hLJ, hreg, hend⟩ :=
    exists_regularZeroShiftEndpoint_neg_in_open_bad_cell
      w.one_le_Q c.p c.k hk1
      hJopen hJne hJcell hJpos hJprev hJbad
  refine ⟨L, hLJ.2.1, ?_, hJprev L hLJ, hreg, hend⟩
  have hηε : η ≤ ε := min_le_left _ _
  linarith [hLJ.2.2]


end Zeta23.CCM

#print axioms Zeta23.CCM.regularCubicZeroShiftPreimage_spec
#print axioms Zeta23.CCM.regularZeroShiftSchurEndpoint_re_eq_shell_sub_predecessor
#print axioms Zeta23.CCM.regularZeroShiftSchurEndpoint_re_neg_of_parityBad
#print axioms Zeta23.CCM.exists_regularZeroShiftEndpoint_neg_in_open_bad_cell
#print axioms Zeta23.CCM.CanonicalParityFirstCrossingShell.exists_arbitrarilyClose_regularZeroShiftEndpoint_neg
