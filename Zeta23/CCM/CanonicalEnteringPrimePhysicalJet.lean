import Zeta23.CCM.CanonicalContactOlderPrimeBudget
import Zeta23.CCM.CanonicalPrimeSeamTaylor
import Mathlib.Analysis.Calculus.Taylor

noncomputable section

namespace Zeta23.CCM

open Matrix Finset
open scoped BigOperators ComplexConjugate ArithmeticFunction Nat

/-!
# POST284 follow-up M44: entering-prime physical jet (Step 81)

Fix a cutoff `K`, a legal even vector `v` (raw coefficients `z`, `M₄ = M₄(z)`) and
`u = Dz` (`sourceIndexAction`).  The physical second-order scalar of the fixed test
`t² e_{Dz}(1 - t/L)` is `Q_v(L) = A_L[t² e_{Dz}(1 - t/L)]`.  Its prime sum carries, for
each active `q ≤ e^L`, the atom `-β_q e_{Dz}(ω_q(L))`, `β_q = Λ(q)(log q)²/√q`,
`ω_q(L) = 1 - log q / L`.  Comparing `Q_v` with and without the `q`-atom (same `v`,
same pole/archimedean background, same other atoms) gives exactly

`ΔQ_v(log q + h) = -β_q e_{Dz}(h / (log q + h))`, `h ≥ 0`.

`Dz` is legal odd with `M₃(Dz) = M₄(z)`, so the merged seventh source jet
(`boundaryFlat_sourceAtom_seventh_jet_package`) and Taylor's theorem with the Lagrange
remainder bound on `[0, 1]` give (81.1):

`|ΔQ_v(log q + h) - a h⁷| ≤ C h⁸` for all `h ≥ 0`, with
`a = 2 Λ(q) (2π)⁶ |M₄|² / (7! √q (log q)⁵)`,

and `a > 0` when `q` is a prime power and `M₄ ≠ 0`.  Independently, M45 on `Dz` gives the
explicit one-sided bound `ΔQ_v(log q + h) ≥ (π⁶/90) β_q |M₄|² ω_h⁷` inside the
odd-endpoint angle of `Dz`.

Scope: a **fixed-vector, one-sided** statement about the newly entering physical source
atom.  It is not positivity of the total `Q`, not an eigenvalue or Schur/resolvent jump
theorem, and says nothing at a contact.  It is a different observable from the negative
ninth-order even-energy seam term `e_z` (Step 56), so the two signs do not conflict.
-/

/-! ## The entering atom -/

/-- The `q`-atom of the physical scalar at aperture `L`: `ΔQ_v(L) = -β_q e_{Dz}(ω_q(L))`. -/
def enteringPrimePhysicalJump (q K : ℕ) (v : euclideanEvenBoundaryFlatSubspace K)
    (L : ℝ) : ℝ :=
  -(contactPrimeWeight q * productionContactIndexEnergy L K v (Real.log q))

/-- The physical scalar with the `q`-atom removed: same vector, same pole/archimedean
background, same other atoms. -/
def productionContactValueWithoutAtom (q K : ℕ) (v : euclideanEvenBoundaryFlatSubspace K)
    (L : ℝ) : ℝ :=
  productionPoleArchValue L (fun t => t ^ 2 * productionContactIndexEnergy L K v t) -
    ∑ p ∈ (Finset.Icc 2 ⌊Real.exp L⌋₊).erase q,
      contactPrimeWeight p * productionContactIndexEnergy L K v (Real.log p)

/-- Once `log q ≤ L`, the atom `q` is active. -/
theorem mem_Icc_floor_exp_of_log_le {q : ℕ} (hq : 2 ≤ q) {L : ℝ}
    (hL : Real.log q ≤ L) :
    q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊ := by
  refine Finset.mem_Icc.mpr ⟨hq, ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  apply Nat.le_floor
  calc (q : ℝ) = Real.exp (Real.log q) := (Real.exp_log hq0).symm
    _ ≤ Real.exp L := Real.exp_le_exp.mpr hL

/-- **With versus without the atom.**  For an active `q`,
`Q_v(L) = Q_v^{(q removed)}(L) + ΔQ_v(L)`. -/
theorem productionContactValue_eq_withoutAtom_add_jump {q K : ℕ}
    (v : euclideanEvenBoundaryFlatSubspace K) {L : ℝ}
    (hq : q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊) :
    productionArithmeticRealValue L
        (fun t => t ^ 2 * productionContactIndexEnergy L K v t) =
      productionContactValueWithoutAtom q K v L + enteringPrimePhysicalJump q K v L := by
  rw [productionArithmeticRealValue_eq_poleArch_sub_primes, ← Finset.add_sum_erase _ _ hq]
  unfold productionContactValueWithoutAtom enteringPrimePhysicalJump contactPrimeWeight
  have hsum : ∀ p ∈ (Finset.Icc 2 ⌊Real.exp L⌋₊).erase q,
      Λ p / Real.sqrt p * (Real.log p ^ 2 * productionContactIndexEnergy L K v (Real.log p)) =
        Λ p / Real.sqrt p * Real.log p ^ 2 *
          productionContactIndexEnergy L K v (Real.log p) :=
    fun p _ => by ring
  rw [Finset.sum_congr rfl hsum]
  ring

/-- At the seam, `ΔQ_v(log q + h) = -β_q e_{Dz}(h / (log q + h))`. -/
theorem enteringPrimePhysicalJump_log_add (q K : ℕ) (v : euclideanEvenBoundaryFlatSubspace K)
    {h : ℝ} (hden : Real.log q + h ≠ 0) :
    enteringPrimePhysicalJump q K v (Real.log q + h) =
      -(contactPrimeWeight q *
        sourceAtomRealEnergy K (sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1))))
          (h / (Real.log q + h))) := by
  unfold enteringPrimePhysicalJump productionContactIndexEnergy
  rw [← primeSourceCoordinate_log_add q h hden]
  rfl

/-! ## The fixed source `Dz` -/

/-- `Dz` is boundary flat for legal even `z`. -/
theorem sourceIndexAction_boundaryFlat (K : ℕ) (v : euclideanEvenBoundaryFlatSubspace K) :
    BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
        (sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1))))) := by
  rw [sourceIndexAction_coordinates]
  have hz : evenBoundaryFlatRawCoefficients K v ∈ evenBoundaryFlatSubspace K :=
    (mem_euclideanEvenBoundaryFlatSubspace_iff K _).mp v.property
  exact (mem_boundaryFlatSubspace_iff K _).mp
    (Submodule.mem_inf.mp (indexMatrix_mulVec_mem_oddBoundaryFlat hz)).1

/-- `|M₃(Dz)|² = |M₄(z)|²`. -/
theorem normSq_centeredMoment_three_sourceIndexAction (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    Complex.normSq (centeredMoment K 3 ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
        (sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))))) =
      ‖centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)‖ ^ 2 := by
  rw [sourceIndexAction_coordinates, centeredMoment_three_indexMatrix_mulVec,
    Complex.normSq_eq_norm_sq]
  rfl

/-- **Seventh-order Taylor remainder for a fixed boundary-flat source.**  On `[0, 1]`,
`|e_x(ω) + 2(2π)⁶ |M₃(x)|² ω⁷ / 7!| ≤ C ω⁸` (Lagrange remainder bound on the smooth
source energy, with the merged exact jets through order seven). -/
theorem sourceAtomRealEnergy_seventh_taylor (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω ∈ Set.Icc (0 : ℝ) 1,
      |sourceAtomRealEnergy K x ω +
          2 * (2 * Real.pi) ^ 6 *
            Complex.normSq (centeredMoment K 3 ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) /
              (7 ! : ℝ) * ω ^ 7| ≤ C * ω ^ 8 := by
  set f := sourceAtomRealEnergy K x with hfdef
  set m := Complex.normSq (centeredMoment K 3 ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
    with hmdef
  have hf : ContDiff ℝ ⊤ f := contDiff_sourceAtomRealEnergy K x
  obtain ⟨hjets, h7⟩ := boundaryFlat_sourceAtom_seventh_jet_package K x hflat
  have hU : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hwithin : ∀ k : ℕ, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      iteratedDerivWithin k f (Set.Icc 0 1) y = iteratedDeriv k f y :=
    fun k y hy => iteratedDerivWithin_eq_iteratedDeriv hU (hf.contDiffAt.of_le le_top) hy
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hf.continuous_iteratedDeriv 8 le_top).continuousOn (s := Set.Icc (0 : ℝ) 1))
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  refine ⟨max C 0 / (7 ! : ℝ), by positivity, fun ω hω => ?_⟩
  have hbound := taylor_mean_remainder_bound (n := 7) (zero_le_one' ℝ)
    (hf.contDiffOn.of_le le_top) hω (C := max C 0)
    (fun y hy => by
      rw [hwithin _ y hy]
      exact (hC y hy).trans (le_max_left _ _))
  have htaylor : taylorWithinEval f 7 (Set.Icc 0 1) 0 ω =
      -(2 * (2 * Real.pi) ^ 6 * m / (7 ! : ℝ)) * ω ^ 7 := by
    rw [taylor_within_apply, Finset.sum_congr rfl fun k _ => by rw [hwithin k 0 h0]]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDeriv_zero, hfdef,
      sourceAtomRealEnergy_zero, hjets 1 (by norm_num) (by norm_num),
      hjets 2 (by norm_num) (by norm_num), hjets 3 (by norm_num) (by norm_num),
      hjets 4 (by norm_num) (by norm_num), hjets 5 (by norm_num) (by norm_num),
      hjets 6 (by norm_num) (by norm_num), h7, smul_eq_mul, sub_zero]
    ring
  rw [htaylor, Real.norm_eq_abs, sub_zero] at hbound
  have he : f ω + 2 * (2 * Real.pi) ^ 6 * m / (7 ! : ℝ) * ω ^ 7 =
      f ω - -(2 * (2 * Real.pi) ^ 6 * m / (7 ! : ℝ)) * ω ^ 7 := by ring
  rw [he]
  calc _ ≤ max C 0 * ω ^ (7 + 1) / (7 ! : ℝ) := hbound
    _ = max C 0 / (7 ! : ℝ) * ω ^ 8 := by ring

/-! ## The jet in the aperture -/

/-- Leading coefficient of (81.1): `2 Λ(q) (2π)⁶ |M₄(z)|² / (7! √q (log q)⁵)`. -/
def enteringPrimeLeadingCoefficient (q K : ℕ) (v : euclideanEvenBoundaryFlatSubspace K) : ℝ :=
  2 * Λ q * (2 * Real.pi) ^ 6 * ‖centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)‖ ^ 2 /
    ((7 ! : ℝ) * Real.sqrt q * Real.log q ^ 5)

/-- The leading coefficient is strictly positive for a prime power `q` and `M₄(z) ≠ 0`. -/
theorem enteringPrimeLeadingCoefficient_pos {q K : ℕ} (hq : IsPrimePow q)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hM : centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v) ≠ 0) :
    0 < enteringPrimeLeadingCoefficient q K v := by
  have hΛ : 0 < Λ q := ArithmeticFunction.vonMangoldt_pos_iff.mpr hq
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hlog : 0 < Real.log q := Real.log_pos (by linarith)
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
  have hm : 0 < ‖centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)‖ := norm_pos_iff.mpr hM
  have hpi := Real.pi_pos
  unfold enteringPrimeLeadingCoefficient
  positivity

private theorem pow_seven_sub_pow_seven_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    b ^ 7 - a ^ 7 ≤ 7 * b ^ 6 * (b - a) := by
  have hb : 0 ≤ b := ha.trans hab
  have hfac : b ^ 7 - a ^ 7 =
      (b - a) * (b ^ 6 + b ^ 5 * a + b ^ 4 * a ^ 2 + b ^ 3 * a ^ 3 + b ^ 2 * a ^ 4 +
        b * a ^ 5 + a ^ 6) := by ring
  have hk : ∀ j : ℕ, j ≤ 6 → b ^ (6 - j) * a ^ j ≤ b ^ 6 := by
    intro j hj
    calc b ^ (6 - j) * a ^ j ≤ b ^ (6 - j) * b ^ j :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab j) (pow_nonneg hb _)
      _ = b ^ 6 := by rw [← pow_add, Nat.sub_add_cancel hj]
  have h1 := hk 1 (by norm_num)
  have h2 := hk 2 (by norm_num)
  have h3 := hk 3 (by norm_num)
  have h4 := hk 4 (by norm_num)
  have h5 := hk 5 (by norm_num)
  have h6 := hk 6 (by norm_num)
  norm_num at h1 h2 h3 h4 h5 h6
  rw [hfac]
  have hs : b ^ 6 + b ^ 5 * a + b ^ 4 * a ^ 2 + b ^ 3 * a ^ 3 + b ^ 2 * a ^ 4 +
      b * a ^ 5 + a ^ 6 ≤ 7 * b ^ 6 := by linarith
  nlinarith [sub_nonneg.mpr hab]

/-- **M44, (81.1).**  For `q ≥ 2` and every legal even `v` there is `C ≥ 0` with
`|ΔQ_v(log q + h) - a h⁷| ≤ C h⁸` for all `h ≥ 0`,
`a = 2 Λ(q) (2π)⁶ |M₄(z)|² / (7! √q (log q)⁵)`. -/
theorem enteringPrimePhysicalJump_seventh_order {q : ℕ} (hq : 2 ≤ q) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 ≤ h →
      |enteringPrimePhysicalJump q K v (Real.log q + h) -
          enteringPrimeLeadingCoefficient q K v * h ^ 7| ≤ C * h ^ 8 := by
  set L₀ := Real.log q with hL₀def
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hL₀ : 0 < L₀ := Real.log_pos (by linarith)
  set x := sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1))) with hxdef
  obtain ⟨C, hC0, hC⟩ := sourceAtomRealEnergy_seventh_taylor K x
    (sourceIndexAction_boundaryFlat K v)
  rw [normSq_centeredMoment_three_sourceIndexAction] at hC
  set m := ‖centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)‖ ^ 2 with hmdef
  set β := contactPrimeWeight q with hβdef
  have hβ : 0 ≤ β := contactPrimeWeight_nonneg q
  set c := 2 * (2 * Real.pi) ^ 6 * m / (7 ! : ℝ) with hcdef
  have hc : 0 ≤ c := by positivity
  have ha : enteringPrimeLeadingCoefficient q K v = β * c / L₀ ^ 7 := by
    unfold enteringPrimeLeadingCoefficient
    rw [hβdef, hcdef, hmdef, contactPrimeWeight, ← hL₀def]
    field_simp
  refine ⟨β * (C + 7 * c) / L₀ ^ 8, by positivity, fun h hh => ?_⟩
  have hpos : 0 < L₀ + h := by linarith
  rw [enteringPrimePhysicalJump_log_add q K v hpos.ne', ha]
  set ω := h / (L₀ + h) with hωdef
  have hω0 : 0 ≤ ω := div_nonneg hh hpos.le
  have hω1 : ω ≤ 1 := (div_le_one hpos).mpr (by linarith)
  have hωh : ω ≤ h / L₀ := div_le_div_of_nonneg_left hh hL₀ (by linarith)
  have hr := abs_le.mp (hC ω ⟨hω0, hω1⟩)
  set F := sourceAtomRealEnergy K x ω with hFdef
  have hdiff : h / L₀ - ω ≤ h ^ 2 / L₀ ^ 2 := by
    have : h / L₀ - ω = h ^ 2 / (L₀ * (L₀ + h)) := by
      rw [hωdef]
      field_simp
      ring
    rw [this]
    exact div_le_div_of_nonneg_left (sq_nonneg h) (by positivity)
      (by nlinarith)
  have hgap : (h / L₀) ^ 7 - ω ^ 7 ≤ 7 * (h ^ 8 / L₀ ^ 8) := by
    calc (h / L₀) ^ 7 - ω ^ 7 ≤ 7 * (h / L₀) ^ 6 * (h / L₀ - ω) :=
          pow_seven_sub_pow_seven_le hω0 hωh
      _ ≤ 7 * (h / L₀) ^ 6 * (h ^ 2 / L₀ ^ 2) :=
          mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = 7 * (h ^ 8 / L₀ ^ 8) := by
          field_simp
  have hgap0 : 0 ≤ (h / L₀) ^ 7 - ω ^ 7 := sub_nonneg.mpr (pow_le_pow_left₀ hω0 hωh 7)
  have hω8 : ω ^ 8 ≤ h ^ 8 / L₀ ^ 8 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ hω0 hωh 8
  have hsplit : -(β * F) - β * c / L₀ ^ 7 * h ^ 7 =
      -(β * (F + c * ω ^ 7)) - β * c * ((h / L₀) ^ 7 - ω ^ 7) := by
    rw [div_pow]
    ring
  have hrhs : β * (C + 7 * c) / L₀ ^ 8 * h ^ 8 =
      β * C * (h ^ 8 / L₀ ^ 8) + β * c * (7 * (h ^ 8 / L₀ ^ 8)) := by ring
  have e1 : β * (F + c * ω ^ 7) ≤ β * (C * ω ^ 8) := mul_le_mul_of_nonneg_left hr.2 hβ
  have e2 : β * -(C * ω ^ 8) ≤ β * (F + c * ω ^ 7) := mul_le_mul_of_nonneg_left hr.1 hβ
  have e3 : β * C * ω ^ 8 ≤ β * C * (h ^ 8 / L₀ ^ 8) :=
    mul_le_mul_of_nonneg_left hω8 (mul_nonneg hβ hC0)
  have e4 : β * c * ((h / L₀) ^ 7 - ω ^ 7) ≤ β * c * (7 * (h ^ 8 / L₀ ^ 8)) :=
    mul_le_mul_of_nonneg_left hgap (mul_nonneg hβ hc)
  have e5 : 0 ≤ β * c * ((h / L₀) ^ 7 - ω ^ 7) := mul_nonneg (mul_nonneg hβ hc) hgap0
  rw [hsplit, hrhs, abs_le]
  constructor <;> nlinarith

/-- **M44, explicit one-sided bound.**  If `ω_h = h / (log q + h)` lies in the
odd-endpoint angle of `Dz`, `(2π ω_h)² B(Dz) ≤ 5 |M₄(z)|`, then
`ΔQ_v(log q + h) ≥ (π⁶/90) β_q |M₄(z)|² ω_h⁷` (M45 on `Dz`). -/
theorem enteringPrimePhysicalJump_ge_of_angle {q : ℕ} (hq : 2 ≤ q) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) {h : ℝ} (hh : 0 ≤ h)
    (hθ : (2 * Real.pi * (h / (Real.log q + h))) ^ 2 *
        sourceOddTaylorWeight K (indexMatrix K *ᵥ evenBoundaryFlatRawCoefficients K v) ≤
      5 * ‖centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)‖) :
    Real.pi ^ 6 / 90 * contactPrimeWeight q *
        ‖centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)‖ ^ 2 *
        (h / (Real.log q + h)) ^ 7 ≤
      enteringPrimePhysicalJump q K v (Real.log q + h) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hL₀ : 0 < Real.log q := Real.log_pos (by linarith)
  have hpos : 0 < Real.log q + h := by linarith
  rw [enteringPrimePhysicalJump_log_add q K v hpos.ne']
  set ω := h / (Real.log q + h) with hωdef
  have hω : 0 ≤ ω := div_nonneg hh hpos.le
  have hz : evenBoundaryFlatRawCoefficients K v ∈ evenBoundaryFlatSubspace K :=
    (mem_euclideanEvenBoundaryFlatSubspace_iff K _).mp v.property
  have hb := re_quadraticForm_index_le_of_mem_evenBoundaryFlat hz hω hθ
  have hE : sourceAtomRealEnergy K (sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1))))
      ω = (quadraticForm (sourceMatrix ω K)
        (indexMatrix K *ᵥ evenBoundaryFlatRawCoefficients K v)).re := by
    change matrixRealEnergy (sourceMatrix ω K)
      (sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))) = _
    unfold matrixRealEnergy
    congr 2
  rw [hE]
  have hβ := contactPrimeWeight_nonneg q
  nlinarith [mul_le_mul_of_nonneg_left hb hβ]

/-- **M44, one-sided sign.**  For a prime power `q` and `M₄(z) ≠ 0`, the entering atom is
strictly positive on a right neighbourhood of the seam: `ΔQ_v(log q + h) > 0` for
`0 < h ≤ h₀`.  Fixed vector only; no statement about the total `Q`. -/
theorem enteringPrimePhysicalJump_pos_near_seam {q : ℕ} (hq : IsPrimePow q) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hM : centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v) ≠ 0) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      0 < enteringPrimePhysicalJump q K v (Real.log q + h) := by
  obtain ⟨C, hC0, hC⟩ := enteringPrimePhysicalJump_seventh_order hq.two_le K v
  set a := enteringPrimeLeadingCoefficient q K v with hadef
  have ha : 0 < a := enteringPrimeLeadingCoefficient_pos hq v hM
  refine ⟨a / (C + 1), by positivity, fun h hh hh0 => ?_⟩
  have hb := (abs_le.mp (hC h hh.le)).1
  have hCh : C * h < a := by
    calc C * h ≤ C * (a / (C + 1)) := mul_le_mul_of_nonneg_left hh0 hC0
      _ < a := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
  have h7 : 0 < h ^ 7 := pow_pos hh 7
  have hkey : 0 < h ^ 7 * (a - C * h) := mul_pos h7 (by linarith)
  nlinarith

end Zeta23.CCM

#print axioms Zeta23.CCM.mem_Icc_floor_exp_of_log_le
#print axioms Zeta23.CCM.productionContactValue_eq_withoutAtom_add_jump
#print axioms Zeta23.CCM.enteringPrimePhysicalJump_log_add
#print axioms Zeta23.CCM.sourceIndexAction_boundaryFlat
#print axioms Zeta23.CCM.normSq_centeredMoment_three_sourceIndexAction
#print axioms Zeta23.CCM.sourceAtomRealEnergy_seventh_taylor
#print axioms Zeta23.CCM.enteringPrimeLeadingCoefficient_pos
#print axioms Zeta23.CCM.enteringPrimePhysicalJump_seventh_order
#print axioms Zeta23.CCM.enteringPrimePhysicalJump_ge_of_angle
#print axioms Zeta23.CCM.enteringPrimePhysicalJump_pos_near_seam
