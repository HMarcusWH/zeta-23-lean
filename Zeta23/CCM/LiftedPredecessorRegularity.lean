import Zeta23.CCM.FrozenIntrinsicPredecessorHolomorphy
import Zeta23.CCM.LiftedPredecessorDeterminantRigidity
import Zeta23.CCM.CanonicalApertureRegularityScaffold
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set Filter
open scoped BigOperators ComplexConjugate ArithmeticFunction Topology

/-!
# FIRST-BAD-RIGIDITY-E4-A4R4: lifted determinant regularity

The algebraic deck argument already proves that the lifted finite-dimensional
predecessor determinant is not identically zero.  This module supplies the
separate analytic half of that argument: basis-coordinate holomorphy and hence
holomorphy of the finite determinant.

For the identity theorem we use a deliberately small connected corridor rather
than proving unnecessary global topology of the whole logarithmic cover.  The
corridor contains both the positive-real logarithms used by physical apertures
and the imaginary-axis deck orbit used by determinant rigidity.

No positivity, negative-root exclusion, finite-to-infinite closure, or RH
claim is made here.
-/

/-- A connected corridor sufficient for the analytic-continuation argument:
the real axis, together with the closed left half-plane. -/
def liftedFrozenRigidityDomain : Set ℂ :=
  {z : ℂ | z.im = 0} ∪ {z : ℂ | z.re ≤ 0}

/-- The real-axis part of the rigidity corridor is convex. -/
private theorem convex_liftedFrozenRigidity_realAxis :
    Convex ℝ {z : ℂ | z.im = 0} := by
  have hset :
      {z : ℂ | z.im = 0} =
        {z : ℂ | z.im ≤ 0} ∩ {z : ℂ | 0 ≤ z.im} := by
    ext z
    simp [le_antisymm_iff]
  rw [hset]
  exact (convex_halfSpace_im_le (r := 0)).inter (convex_halfSpace_im_ge (r := 0))

/-- The left-half-plane part of the rigidity corridor is convex. -/
private theorem convex_liftedFrozenRigidity_leftHalfPlane :
    Convex ℝ {z : ℂ | z.re ≤ 0} :=
  convex_halfSpace_re_le (r := 0)

/-- The rigidity corridor is preconnected; its two convex pieces meet at the
origin. -/
theorem isPreconnected_liftedFrozenRigidityDomain :
    IsPreconnected liftedFrozenRigidityDomain := by
  unfold liftedFrozenRigidityDomain
  exact IsPreconnected.union (0 : ℂ)
    (by simp) (by simp)
    convex_liftedFrozenRigidity_realAxis.isPreconnected
    convex_liftedFrozenRigidity_leftHalfPlane.isPreconnected

/-- The rigidity corridor lies inside the true lifted source domain.  On the
left half-plane, `|Im(exp z)| <= 1 < pi`; on the real axis it vanishes. -/
theorem liftedFrozenRigidityDomain_subset_liftedFrozenPredecessorDomain :
    liftedFrozenRigidityDomain ⊆ liftedFrozenPredecessorDomain := by
  intro z hz
  change Complex.exp z ∈ complexFrozenSourceDomain
  constructor
  · change |(Complex.exp z).im| < Real.pi
    rcases hz with hzreal | hzleft
    · have hzim : z.im = 0 := hzreal
      rw [Complex.exp_im, hzim, Real.sin_zero, mul_zero, abs_zero]
      exact Real.pi_pos
    · rw [Complex.exp_im, abs_mul, abs_of_nonneg (Real.exp_nonneg z.re)]
      have hexp : Real.exp z.re ≤ 1 := Real.exp_le_one_iff.mpr hzleft
      have hsin : |Real.sin z.im| ≤ 1 := Real.abs_sin_le_one z.im
      have hnonneg : 0 ≤ |Real.sin z.im| := abs_nonneg _
      have hle : Real.exp z.re * |Real.sin z.im| ≤ 1 := by
        calc
          Real.exp z.re * |Real.sin z.im| ≤ 1 * 1 :=
            mul_le_mul hexp hsin hnonneg (Real.exp_nonneg z.re)
          _ = 1 := by norm_num
      exact lt_of_le_of_lt hle (by linarith [Real.pi_gt_three])
  · simpa using Complex.exp_ne_zero z

/-- Every real point belongs to the rigidity corridor. -/
@[simp] theorem ofReal_mem_liftedFrozenRigidityDomain (x : ℝ) :
    (x : ℂ) ∈ liftedFrozenRigidityDomain := by
  left
  simp

/-- Every natural deck translate of the origin belongs to the rigidity
corridor, because it lies on the imaginary axis. -/
theorem nat_two_pi_I_mem_liftedFrozenRigidityDomain (k : ℕ) :
    (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) ∈
      liftedFrozenRigidityDomain := by
  right
  simp

/-- Coordinate matrix of the actual lifted intrinsic predecessor in one fixed
finite basis. -/
noncomputable def liftedFrozenIntrinsicPredecessorMatrix
    (Q : ℕ) (p : ReversalParity) (N : ℕ) (z : ℂ) :
    Matrix
      (Fin (Module.finrank ℂ (intrinsicParityPredecessorSubspace p N)))
      (Fin (Module.finrank ℂ (intrinsicParityPredecessorSubspace p N))) ℂ :=
  let b := Module.finBasis ℂ (intrinsicParityPredecessorSubspace p N)
  LinearMap.toMatrix b b (liftedFrozenIntrinsicPredecessorBlock Q p N z)

/-- Every basis coordinate of the lifted predecessor matrix is analytic on the
true lifted source domain. -/
theorem analyticOnNhd_liftedFrozenIntrinsicPredecessorMatrix_apply
    (Q : ℕ) (p : ReversalParity) (N : ℕ)
    (i j : Fin (Module.finrank ℂ (intrinsicParityPredecessorSubspace p N))) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => liftedFrozenIntrinsicPredecessorMatrix Q p N z i j)
      liftedFrozenPredecessorDomain := by
  let E := intrinsicParityPredecessorSubspace p N
  let b := Module.finBasis ℂ E
  have hfun :
      (fun z : ℂ => liftedFrozenIntrinsicPredecessorMatrix Q p N z i j) =
        (fun z : ℂ =>
          (b.coord i) (liftedFrozenIntrinsicPredecessorBlock Q p N z (b j))) := by
    funext z
    simp [liftedFrozenIntrinsicPredecessorMatrix, E, b, LinearMap.toMatrix_apply]
  rw [hfun]
  exact analyticOnNhd_liftedFrozenIntrinsicPredecessorBlock_coord
    Q p N (b.coord i) (b j)

/-- Lifted determinant of the actual intrinsic predecessor block. -/
noncomputable def liftedFrozenIntrinsicPredecessorDet
    (Q : ℕ) (p : ReversalParity) (N : ℕ) (z : ℂ) : ℂ :=
  LinearMap.det (liftedFrozenIntrinsicPredecessorBlock Q p N z)

/-- The basis-coordinate matrix determinant is exactly the basis-independent
linear-map determinant. -/
@[simp] theorem det_liftedFrozenIntrinsicPredecessorMatrix
    (Q : ℕ) (p : ReversalParity) (N : ℕ) (z : ℂ) :
    Matrix.det (liftedFrozenIntrinsicPredecessorMatrix Q p N z) =
      liftedFrozenIntrinsicPredecessorDet Q p N z := by
  simp [liftedFrozenIntrinsicPredecessorMatrix,
    liftedFrozenIntrinsicPredecessorDet]

/-- The lifted predecessor determinant is analytic on the true lifted domain.
The proof is only the finite Leibniz determinant polynomial applied to the
already-analytic basis entries. -/
theorem analyticOnNhd_liftedFrozenIntrinsicPredecessorDet
    (Q : ℕ) (p : ReversalParity) (N : ℕ) :
    AnalyticOnNhd ℂ
      (liftedFrozenIntrinsicPredecessorDet Q p N)
      liftedFrozenPredecessorDomain := by
  have hmatrix : AnalyticOnNhd ℂ
      (fun z : ℂ => Matrix.det (liftedFrozenIntrinsicPredecessorMatrix Q p N z))
      liftedFrozenPredecessorDomain := by
    intro z hz
    simp_rw [Matrix.det_apply']
    apply Finset.analyticAt_fun_sum
    intro σ _hσ
    apply analyticAt_const.mul
    apply Finset.analyticAt_fun_prod
    intro i _hi
    exact analyticOnNhd_liftedFrozenIntrinsicPredecessorMatrix_apply
      Q p N (σ i) i z hz
  simpa [liftedFrozenIntrinsicPredecessorDet] using hmatrix

/-- The algebraic deck witness can be chosen inside the connected rigidity
corridor used for analytic continuation. -/
theorem exists_mem_liftedFrozenRigidityDomain_det_ne_zero
    (Q : ℕ) (p : ReversalParity) (N : ℕ) :
    ∃ z ∈ liftedFrozenRigidityDomain,
      liftedFrozenIntrinsicPredecessorDet Q p N z ≠ 0 := by
  obtain ⟨k, hk⟩ :=
    exists_nat_deck_translate_liftedFrozenIntrinsicPredecessor_det_ne_zero
      Q p N 0
  refine ⟨(k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I),
    nat_two_pi_I_mem_liftedFrozenRigidityDomain k, ?_⟩
  simpa [liftedFrozenIntrinsicPredecessorDet, zero_add] using hk

/-- On the rigidity corridor the determinant cannot vanish identically. -/
theorem liftedFrozenIntrinsicPredecessorDet_not_zero_on_rigidityDomain
    (Q : ℕ) (p : ReversalParity) (N : ℕ) :
    ¬ Set.EqOn (liftedFrozenIntrinsicPredecessorDet Q p N) 0
      liftedFrozenRigidityDomain := by
  rintro hzero
  obtain ⟨z, hz, hzne⟩ :=
    exists_mem_liftedFrozenRigidityDomain_det_ne_zero Q p N
  exact hzne (hzero hz)

/-- Every nonempty open real interval inside one physical cutoff cell contains
an aperture at which the actual intrinsic predecessor is regular.

If every point of the interval were singular, their logarithms would give an
accumulating zero set for the lifted analytic determinant on the connected
rigidity corridor.  The identity theorem would then make the determinant zero
on the whole corridor, contradicting the deck-forced nonzero determinant. -/
theorem exists_intrinsicPredecessorRegular_in_open_fixedCell
    {Q : ℕ} (hQ : 1 ≤ Q)
    (p : ReversalParity) (N : ℕ)
    {J : Set ℝ}
    (hJopen : IsOpen J)
    (hJne : J.Nonempty)
    (hJcell : J ⊆ fixedCanonicalCutoffCell Q) :
    ∃ L ∈ J, IntrinsicPredecessorRegular p L N := by
  classical
  by_contra hnone
  push_neg at hnone
  obtain ⟨L₀, hL₀J⟩ := hJne
  have hL₀cell : L₀ ∈ fixedCanonicalCutoffCell Q := hJcell hL₀J
  have hL₀pos : 0 < L₀ := fixedCanonicalCutoffCell_subset_Ioi hQ hL₀cell
  let f : ℂ → ℂ := liftedFrozenIntrinsicPredecessorDet Q p N
  have hf : AnalyticOnNhd ℂ f liftedFrozenRigidityDomain := by
    intro z hz
    exact analyticOnNhd_liftedFrozenIntrinsicPredecessorDet Q p N z
      (liftedFrozenRigidityDomain_subset_liftedFrozenPredecessorDomain hz)
  have hzeroReal :
      ∀ L ∈ J, f (Real.log L : ℂ) = 0 := by
    intro L hLJ
    have hLcell : L ∈ fixedCanonicalCutoffCell Q := hJcell hLJ
    have hLpos : 0 < L := fixedCanonicalCutoffCell_subset_Ioi hQ hLcell
    have hsing : ¬ IntrinsicPredecessorRegular p L N := hnone L hLJ
    change ¬ intrinsicPredecessorDet p L N ≠ 0 at hsing
    have hdet0 : intrinsicPredecessorDet p L N = 0 := not_ne_iff.mp hsing
    have hbridge :=
      liftedFrozenIntrinsicPredecessorBlock_of_log_fixedCell hQ hLcell p N
    change LinearMap.det
      (liftedFrozenIntrinsicPredecessorBlock Q p N (Real.log L : ℂ)) = 0
    rw [hbridge]
    exact hdet0
  have hJevent : ∀ᶠ L in 𝓝[≠] L₀, L ∈ J :=
    (hJopen.mem_nhds hL₀J).filter_mono nhdsWithin_le_nhds
  have hrealEvent :
      ∀ᶠ L in 𝓝[≠] L₀, L ∈ J ∧ f (Real.log L : ℂ) = 0 := by
    filter_upwards [hJevent] with L hLJ
    exact ⟨hLJ, hzeroReal L hLJ⟩
  have hreal :
      ∃ᶠ L in 𝓝[≠] L₀, L ∈ J ∧ f (Real.log L : ℂ) = 0 :=
    hrealEvent.frequently
  have hcomplex :
      ∃ᶠ z in 𝓝[≠] (Real.log L₀ : ℂ), f z = 0 := by
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hxs_tendsto, hxs_zero⟩ := hreal
    refine ⟨fun n => (Real.log (xs n) : ℂ), ?_, fun n => (hxs_zero n).2⟩
    rw [tendsto_nhdsWithin_iff] at hxs_tendsto ⊢
    constructor
    · rw [tendsto_ofReal_iff]
      exact (Real.continuousAt_log hL₀pos.ne').tendsto.comp hxs_tendsto.1
    · filter_upwards [hxs_tendsto.2] with n hxsne
      have hxsJ : xs n ∈ J := (hxs_zero n).1
      have hxscell : xs n ∈ fixedCanonicalCutoffCell Q := hJcell hxsJ
      have hxspos : 0 < xs n := fixedCanonicalCutoffCell_subset_Ioi hQ hxscell
      have hlogne : Real.log (xs n) ≠ Real.log L₀ := by
        intro heq
        exact hxsne (Real.log_injOn_pos hxspos hL₀pos heq)
      simpa using hlogne
  have hidenticallyZero : Set.EqOn f 0 liftedFrozenRigidityDomain :=
    AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
      hf analyticOnNhd_const
      isPreconnected_liftedFrozenRigidityDomain
      (z₀ := (Real.log L₀ : ℂ))
      (ofReal_mem_liftedFrozenRigidityDomain (Real.log L₀))
      hcomplex
  exact
    (liftedFrozenIntrinsicPredecessorDet_not_zero_on_rigidityDomain Q p N)
      hidenticallyZero

end Zeta23.CCM

#print axioms Zeta23.CCM.isPreconnected_liftedFrozenRigidityDomain
#print axioms Zeta23.CCM.liftedFrozenRigidityDomain_subset_liftedFrozenPredecessorDomain
#print axioms Zeta23.CCM.analyticOnNhd_liftedFrozenIntrinsicPredecessorMatrix_apply
#print axioms Zeta23.CCM.analyticOnNhd_liftedFrozenIntrinsicPredecessorDet
#print axioms Zeta23.CCM.exists_mem_liftedFrozenRigidityDomain_det_ne_zero
#print axioms Zeta23.CCM.exists_intrinsicPredecessorRegular_in_open_fixedCell
