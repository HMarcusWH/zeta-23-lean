import Zeta23.CCM.BoundaryFlatApproximation
import Zeta23.ExceptionalZero.WeilContinuity
import Zeta23.ExceptionalZero.NegativeWeilTestSupport
import Zeta23.ExceptionalZero.BoundaryFlatFiniteWeil

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Function MeasureTheory Real Set
open scoped BigOperators ComplexConjugate

/-!
# F1: finite canonical negative obstruction

F0-B1C-B produces legal boundary-flat finite hard-window approximants in
exactly the L¹ + second-derivative L¹ topology controlled by WCONT-A.

This module first proves strict-sign stability of the genuine concrete-zeta
diagonal Weil form under those approximations. It then composes that result
with the exact F0-B1A carrier identity to obtain the finite canonical
obstruction:

a hypothetical off-critical-line zeta zero forces a negative direction of one
finite `canonicalSourceMatrix` inside the exact three-moment boundary-flat
sector.

No positivity theorem for the canonical matrix and no proof of RH is asserted
here.
-/

/-- The L¹ norm of an approximant is bounded by the L¹ norm of its error plus
the L¹ norm of the target. -/
theorem integral_norm_le_integral_norm_sub_add
    {p h : ℝ → ℂ}
    (hp : Integrable p)
    (hh : Integrable h) :
    (∫ x, ‖p x‖) ≤
      (∫ x, ‖(p - h) x‖) + ∫ x, ‖h x‖ := by
  have he : Integrable (p - h) := hp.sub hh
  have hpoint :
      ∀ x : ℝ, ‖p x‖ ≤ ‖(p - h) x‖ + ‖h x‖ := by
    intro x
    have htri := norm_add_le ((p - h) x) (h x)
    simpa [Pi.sub_apply] using htri
  calc
    (∫ x, ‖p x‖)
        ≤ ∫ x, (‖(p - h) x‖ + ‖h x‖) := by
          exact integral_mono hp.norm (he.norm.add hh.norm) hpoint
    _ =
      (∫ x, ‖(p - h) x‖) + ∫ x, ‖h x‖ := by
        exact integral_add he.norm hh.norm

/-- WCONT-A specialized to an approximation whose two load-bearing errors are
bounded by one common tolerance. The resulting constant depends only on the
fixed support aperture and the target, not on the finite bandwidth. -/
theorem zeta_W_self_sub_self_norm_le_of_WCONT_errors
    {L η : ℝ}
    (hL : 0 < L)
    (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1)
    {p h : ℝ → ℂ}
    (hp : ContDiff ℝ 2 p)
    (hh : ContDiff ℝ 2 h)
    (hpsupp : ∀ x, p x ≠ 0 → |x| ≤ L)
    (hhsupp : ∀ x, h x ≠ 0 → |x| ≤ L)
    (he0 :
      (∫ x, ‖(p - h) x‖) ≤ η)
    (he2 :
      (∫ x, ‖deriv (deriv (p - h)) x‖) ≤ η) :
    ‖zetaZeroConfig.W p p - zetaZeroConfig.W h h‖
      ≤
      Real.exp L * zetaInvSqZeroMass * η *
        (3 * (∫ x, ‖h x‖) +
          (∫ x, ‖deriv (deriv h) x‖) + 2) := by
  have hpc : HasCompactSupport p :=
    hasCompactSupport_of_support_subset_abs hpsupp
  have hhc : HasCompactSupport h :=
    hasCompactSupport_of_support_subset_abs hhsupp
  have hpInt : Integrable p :=
    hp.continuous.integrable_of_hasCompactSupport hpc
  have hhInt : Integrable h :=
    hh.continuous.integrable_of_hasCompactSupport hhc
  have hpNorm :=
    integral_norm_le_integral_norm_sub_add hpInt hhInt

  have hE0 : 0 ≤ ∫ x, ‖(p - h) x‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hE2 : 0 ≤ ∫ x, ‖deriv (deriv (p - h)) x‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hP0 : 0 ≤ ∫ x, ‖p x‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hH0 : 0 ≤ ∫ x, ‖h x‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hH2 : 0 ≤ ∫ x, ‖deriv (deriv h) x‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hZ :
      0 ≤ Real.exp L * zetaInvSqZeroMass :=
    mul_nonneg (Real.exp_pos L).le zetaInvSqZeroMass_nonneg

  have hpNorm' :
      (∫ x, ‖p x‖) ≤ (∫ x, ‖h x‖) + 1 := by
    calc
      (∫ x, ‖p x‖)
          ≤ (∫ x, ‖(p - h) x‖) + ∫ x, ‖h x‖ := hpNorm
      _ ≤ η + ∫ x, ‖h x‖ := by
        exact add_le_add_right he0 _
      _ ≤ 1 + ∫ x, ‖h x‖ := by
        exact add_le_add_right hη1 _
      _ = (∫ x, ‖h x‖) + 1 := by ring

  have hsumE :
      (∫ x, ‖(p - h) x‖) +
          (∫ x, ‖deriv (deriv (p - h)) x‖)
        ≤ 2 * η := by
    nlinarith

  have hterm1 :
      ((∫ x, ‖(p - h) x‖) +
          (∫ x, ‖deriv (deriv (p - h)) x‖)) *
          (∫ x, ‖p x‖)
        ≤
      (2 * η) * ((∫ x, ‖h x‖) + 1) := by
    calc
      ((∫ x, ‖(p - h) x‖) +
          (∫ x, ‖deriv (deriv (p - h)) x‖)) *
          (∫ x, ‖p x‖)
          ≤
        (2 * η) * (∫ x, ‖p x‖) :=
          mul_le_mul_of_nonneg_right hsumE hP0
      _ ≤
        (2 * η) * ((∫ x, ‖h x‖) + 1) :=
          mul_le_mul_of_nonneg_left hpNorm' (by nlinarith)

  have hterm2 :
      ((∫ x, ‖h x‖) +
          ∫ x, ‖deriv (deriv h) x‖) *
          (∫ x, ‖(p - h) x‖)
        ≤
      ((∫ x, ‖h x‖) +
          ∫ x, ‖deriv (deriv h) x‖) * η :=
    mul_le_mul_of_nonneg_left he0 (add_nonneg hH0 hH2)

  have hterms :
      (((∫ x, ‖(p - h) x‖) +
            ∫ x, ‖deriv (deriv (p - h)) x‖) *
            (∫ x, ‖p x‖) +
          ((∫ x, ‖h x‖) +
            ∫ x, ‖deriv (deriv h) x‖) *
            (∫ x, ‖(p - h) x‖))
        ≤
      (2 * η) * ((∫ x, ‖h x‖) + 1) +
        ((∫ x, ‖h x‖) +
          ∫ x, ‖deriv (deriv h) x‖) * η :=
    add_le_add hterm1 hterm2

  have hW :=
    zeta_W_self_sub_self_norm_le_commonSupport
      hL.le hp hh hpsupp hhsupp

  calc
    ‖zetaZeroConfig.W p p - zetaZeroConfig.W h h‖
        ≤
      Real.exp L * zetaInvSqZeroMass *
        (((∫ x, ‖(p - h) x‖) +
            ∫ x, ‖deriv (deriv (p - h)) x‖) *
            (∫ x, ‖p x‖) +
          ((∫ x, ‖h x‖) +
            ∫ x, ‖deriv (deriv h) x‖) *
            (∫ x, ‖(p - h) x‖)) := hW
    _ ≤
      Real.exp L * zetaInvSqZeroMass *
        ((2 * η) * ((∫ x, ‖h x‖) + 1) +
          ((∫ x, ‖h x‖) +
            ∫ x, ‖deriv (deriv h) x‖) * η) :=
      mul_le_mul_of_nonneg_left hterms hZ
    _ =
      Real.exp L * zetaInvSqZeroMass * η *
        (3 * (∫ x, ‖h x‖) +
          (∫ x, ‖deriv (deriv h) x‖) + 2) := by
      ring

/-- **Strict finite sign transfer.**

A strictly negative compact C² Weil test supported inside one positive aperture
has a legal boundary-flat finite approximation whose genuine diagonal Weil
value is still strictly negative. -/
theorem exists_boundaryFlatFinite_negativeW_of_strictAperture
    {L : ℝ} (hL : 0 < L)
    {h : ℝ → ℂ}
    (hh : ContDiff ℝ 2 h)
    (hhc : HasCompactSupport h)
    (hs : tsupport h ⊆ Ioo 0 L)
    (hneg : (zetaZeroConfig.W h h).re < 0) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∃ u : Fin (2 * N + 1) → ℂ,
        Zeta23.CCM.BoundaryFlatCoefficients N u ∧
        (zetaZeroConfig.W
          (Zeta23.CCM.localizedFiniteVector L N u)
          (Zeta23.CCM.localizedFiniteVector L N u)).re < 0 := by
  let m : ℝ := -(zetaZeroConfig.W h h).re
  let H0 : ℝ := ∫ x, ‖h x‖
  let H2 : ℝ := ∫ x, ‖deriv (deriv h) x‖
  let K : ℝ :=
    Real.exp L * zetaInvSqZeroMass *
      (3 * H0 + H2 + 2)
  let d : ℝ := 2 * (K + 1)
  let η : ℝ := min 1 (m / d)

  have hm : 0 < m := by
    dsimp [m]
    exact neg_pos.mpr hneg
  have hH0 : 0 ≤ H0 := by
    dsimp [H0]
    exact integral_nonneg fun _ => norm_nonneg _
  have hH2 : 0 ≤ H2 := by
    dsimp [H2]
    exact integral_nonneg fun _ => norm_nonneg _
  have hK : 0 ≤ K := by
    dsimp [K]
    exact
      mul_nonneg
        (mul_nonneg (Real.exp_pos L).le zetaInvSqZeroMass_nonneg)
        (by nlinarith)
  have hd : 0 < d := by
    dsimp [d]
    nlinarith
  have hη : 0 < η := by
    dsimp [η]
    apply lt_min
    · norm_num
    · exact div_pos hm hd
  have hη1 : η ≤ 1 := by
    dsimp [η]
    exact min_le_left _ _
  have hηfrac : η ≤ m / d := by
    dsimp [η]
    exact min_le_right _ _

  have hKd : K < d := by
    dsimp [d]
    nlinarith
  have hmKd : m * K < m * d :=
    mul_lt_mul_of_pos_left hKd hm
  have hfrac :
      K * (m / d) < m := by
    have hrewrite : K * (m / d) = (m * K) / d := by
      ring
    rw [hrewrite]
    exact (div_lt_iff₀ hd).2 (by
      simpa [mul_assoc] using hmKd)
  have hηmargin : K * η < m := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hηfrac hK)
      hfrac

  obtain ⟨N, hN, u, hflat, he0, he2⟩ :=
    Zeta23.CCM.exists_boundaryFlatFinite_WCONT_approx
      hL hh hs hη

  let p : ℝ → ℂ :=
    Zeta23.CCM.localizedFiniteVector L N u

  have hp : ContDiff ℝ 2 p := by
    simpa [p] using
      Zeta23.CCM.contDiff_localizedFiniteVector_of_boundaryFlat
        N u hL hflat

  have hpsupp :
      ∀ x, p x ≠ 0 → |x| ≤ L := by
    intro x hx
    have hxI : x ∈ Icc (0 : ℝ) L :=
      Zeta23.CCM.localizedFiniteVector_support_subset
        L N u (by simpa [p] using hx)
    rw [abs_of_nonneg hxI.1]
    exact hxI.2

  have hhsupp :
      ∀ x, h x ≠ 0 → |x| ≤ L := by
    intro x hx
    have hxt : x ∈ tsupport h :=
      subset_closure (by simpa [Function.mem_support] using hx)
    have hxi := hs hxt
    rw [abs_of_pos hxi.1]
    exact hxi.2.le

  have he0' :
      (∫ x, ‖(p - h) x‖) ≤ η := by
    simpa [p] using he0.le
  have he2' :
      (∫ x, ‖deriv (deriv (p - h)) x‖) ≤ η := by
    simpa [p] using he2.le

  have hWdiff :=
    zeta_W_self_sub_self_norm_le_of_WCONT_errors
      hL hη.le hη1 hp hh hpsupp hhsupp he0' he2'

  have hWdiff' :
      ‖zetaZeroConfig.W p p -
          zetaZeroConfig.W h h‖
        ≤ K * η := by
    simpa [K, H0, H2, mul_assoc] using hWdiff

  have hWnorm :
      ‖zetaZeroConfig.W p p -
          zetaZeroConfig.W h h‖ < m :=
    lt_of_le_of_lt hWdiff' hηmargin

  have hre :
      (zetaZeroConfig.W p p -
          zetaZeroConfig.W h h).re < m := by
    have habs :
        |(zetaZeroConfig.W p p -
            zetaZeroConfig.W h h).re|
          ≤
        ‖zetaZeroConfig.W p p -
            zetaZeroConfig.W h h‖ :=
      Complex.abs_re_le_norm _
    have hle :
        (zetaZeroConfig.W p p -
            zetaZeroConfig.W h h).re
          ≤
        |(zetaZeroConfig.W p p -
            zetaZeroConfig.W h h).re| :=
      le_abs_self _
    exact lt_of_le_of_lt (hle.trans habs) hWnorm

  have hpneg :
      (zetaZeroConfig.W p p).re < 0 := by
    change
      (zetaZeroConfig.W p p).re -
          (zetaZeroConfig.W h h).re < m at hre
    dsimp [m] at hre
    linarith

  exact ⟨N, hN, u, hflat, by simpa [p] using hpneg⟩

/-- **F1: canonical finite negative obstruction.**

Every hypothetical off-critical-line zeta zero forces a strictly negative
quadratic direction of one finite canonical CCM matrix in the exact
three-moment boundary-flat sector. -/
theorem
    exists_boundaryFlat_negativeCanonicalSourceQuadraticForm_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ N : ℕ, 1 ≤ N ∧
        ∃ u : Fin (2 * N + 1) → ℂ,
          Zeta23.CCM.BoundaryFlatCoefficients N u ∧
          (Zeta23.CCM.quadraticForm
            (Zeta23.CCM.canonicalSourceMatrix L N) u).re < 0 := by
  obtain ⟨L, hL, h, hh, hhc, hs, hneg⟩ :=
    exists_strictAperture_negativeWeilTest_of_offLine_zero
      ρ₀ hoff

  obtain ⟨N, hN, u, hflat, hfiniteNeg⟩ :=
    exists_boundaryFlatFinite_negativeW_of_strictAperture
      hL hh hhc hs hneg

  refine ⟨L, hL, N, hN, u, hflat, ?_⟩
  rw [
    ← zeta_W_boundaryFlatFiniteVector_eq_canonicalSourceQuadraticForm
      N u hL hflat
  ]
  exact hfiniteNeg

/-- Existential F1 wrapper: existence of any off-line zeta zero forces one
finite canonical negative obstruction. -/
theorem
    exists_boundaryFlat_negativeCanonicalSourceQuadraticForm_of_exists_offLine_zero
    (hoff :
      ∃ ρ : zetaZeroConfig.carrier,
        (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ N : ℕ, 1 ≤ N ∧
        ∃ u : Fin (2 * N + 1) → ℂ,
          Zeta23.CCM.BoundaryFlatCoefficients N u ∧
          (Zeta23.CCM.quadraticForm
            (Zeta23.CCM.canonicalSourceMatrix L N) u).re < 0 := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact
    exists_boundaryFlat_negativeCanonicalSourceQuadraticForm_of_offLine_zero
      ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.integral_norm_le_integral_norm_sub_add
#print axioms Zeta23.ExceptionalZero.zeta_W_self_sub_self_norm_le_of_WCONT_errors
#print axioms Zeta23.ExceptionalZero.exists_boundaryFlatFinite_negativeW_of_strictAperture
#print axioms Zeta23.ExceptionalZero.exists_boundaryFlat_negativeCanonicalSourceQuadraticForm_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_boundaryFlat_negativeCanonicalSourceQuadraticForm_of_exists_offLine_zero
