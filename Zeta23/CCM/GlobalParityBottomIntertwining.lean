import Zeta23.CCM.GlobalParityBottomSpectrum
import Zeta23.CCM.SourceExplicitCubicDefect
import Zeta23.CCM.ParityCubicFactorization

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# PR #247 — ground-state rank-one parity intertwining

The parity-compression defect is already known exactly:

  T_odd D - D T_even = S(.) * g_odd,

where S is the canonical quadratic source moment.  This module evaluates that
identity on true parity ground eigenvectors.

A strict separation of parity bottoms then forces a quantitative lower bound on
the source defect.  Thus the rank-one parity defect cannot vanish on a ground
state in the lower parity.  The reverse strict branch is handled through the
already-proved algebraic D-equivalence and conjugated rank-one defect; no
unitarity or isometry of D is assumed.
-/

/-- Exact intertwining identity on an even eigenmode, with the rank-one defect
written as the actual canonical quadratic source moment. -/
theorem evenEigenmode_shiftedOdd_eq_sourceCubic
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    (lam : ℝ)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hveig :
      parityCompressedCanonical .even L K v = (lam : ℂ) • v) :
    oddCompressedCanonical L K
          (euclideanEvenToOddIndexLinearMap K v) -
        (lam : ℂ) • euclideanEvenToOddIndexLinearMap K v =
      evenQuadraticSourceMoment L K v • oddCubicCompressionVector K := by
  have hfac :=
    evenOddCompressedIntertwiningDefect_eq_cubicFunctional_smul
      hL K hK v
  have hsource :=
    cubicDefectFunctional_eq_evenQuadraticSourceMoment
      hL K hK v
  change
    oddCompressedCanonical L K (euclideanEvenToOddIndexLinearMap K v) -
        euclideanEvenToOddIndexLinearMap K (evenCompressedCanonical L K v) =
      cubicDefectFunctional L K v • oddCubicCompressionVector K at hfac
  change evenCompressedCanonical L K v = (lam : ℂ) • v at hveig
  rw [hveig, map_smul, hsource] at hfac
  exact hfac

/-- In the strict-even branch, an even ground eigenvector carries a nonzero
canonical source defect.  The denominator-free inequality records the exact
spectral-gap coercivity before any cancellation. -/
theorem exists_evenGround_source_gap_bound_of_strict
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hstrict :
      parityRayleighBottom .even L (N + 1) <
        parityRayleighBottom .odd L (N + 1)) :
    ∃ v : euclideanEvenBoundaryFlatSubspace (N + 1),
      v ≠ 0 ∧
      parityCompressedCanonical .even L (N + 1) v =
        (parityRayleighBottom .even L (N + 1) : ℂ) • v ∧
      evenQuadraticSourceMoment L (N + 1) v ≠ 0 ∧
      (parityRayleighBottom .odd L (N + 1) -
          parityRayleighBottom .even L (N + 1)) *
          ‖euclideanEvenToOddIndexLinearMap (N + 1) v‖ ^ 2 ≤
        ‖evenQuadraticSourceMoment L (N + 1) v‖ *
          ‖oddCubicCompressionVector (N + 1)‖ *
          ‖euclideanEvenToOddIndexLinearMap (N + 1) v‖ := by
  obtain ⟨v, hvne, hveig⟩ :=
    exists_eigenmode_at_parityRayleighBottom_succ
      .even L N hN
  let Dv : euclideanOddBoundaryFlatSubspace (N + 1) :=
    euclideanEvenToOddIndexLinearMap (N + 1) v
  have hDvne : Dv ≠ 0 := by
    intro hDv
    apply hvne
    apply euclideanEvenToOddIndexLinearMap_injective (N + 1)
    exact hDv.trans (map_zero (euclideanEvenToOddIndexLinearMap (N + 1))).symm
  have hshift :=
    parityRayleighBottom_gap_mul_norm_sq_le_shifted
      .odd L (N + 1)
      (parityRayleighBottom .even L (N + 1)) Dv
  change
    (parityRayleighBottom .odd L (N + 1) -
        parityRayleighBottom .even L (N + 1)) * ‖Dv‖ ^ 2 ≤
      Complex.re
        (inner ℂ
          (oddCompressedCanonical L (N + 1) Dv -
            (parityRayleighBottom .even L (N + 1) : ℂ) • Dv)
          Dv) at hshift
  have hident :=
    evenEigenmode_shiftedOdd_eq_sourceCubic
      hL (N + 1) (by omega)
      (parityRayleighBottom .even L (N + 1)) v hveig
  rw [hident] at hshift
  have hupp :
      Complex.re
          (inner ℂ
            (evenQuadraticSourceMoment L (N + 1) v •
              oddCubicCompressionVector (N + 1))
            Dv) ≤
        ‖evenQuadraticSourceMoment L (N + 1) v‖ *
          ‖oddCubicCompressionVector (N + 1)‖ * ‖Dv‖ := by
    calc
      Complex.re
          (inner ℂ
            (evenQuadraticSourceMoment L (N + 1) v •
              oddCubicCompressionVector (N + 1))
            Dv) ≤
        |Complex.re
          (inner ℂ
            (evenQuadraticSourceMoment L (N + 1) v •
              oddCubicCompressionVector (N + 1))
            Dv)| := le_abs_self _
      _ ≤ ‖inner ℂ
          (evenQuadraticSourceMoment L (N + 1) v •
            oddCubicCompressionVector (N + 1))
          Dv‖ := Complex.abs_re_le_norm _
      _ ≤
        ‖evenQuadraticSourceMoment L (N + 1) v •
            oddCubicCompressionVector (N + 1)‖ * ‖Dv‖ :=
          norm_inner_le_norm _ _
      _ =
        ‖evenQuadraticSourceMoment L (N + 1) v‖ *
          ‖oddCubicCompressionVector (N + 1)‖ * ‖Dv‖ := by
          rw [norm_smul]
  have hbound := le_trans hshift hupp
  have hsourceNe : evenQuadraticSourceMoment L (N + 1) v ≠ 0 := by
    intro hzero
    have hnorm : 0 < ‖Dv‖ ^ 2 := by positivity
    have hleft :
        0 <
          (parityRayleighBottom .odd L (N + 1) -
              parityRayleighBottom .even L (N + 1)) *
            ‖Dv‖ ^ 2 :=
      mul_pos (sub_pos.mpr hstrict) hnorm
    rw [hzero] at hbound
    simp at hbound
    exact (not_lt_of_ge hbound) hleft
  exact ⟨v, hvne, hveig, hsourceNe, by simpa [Dv] using hbound⟩

/-- Exact reverse same-space identity obtained by pulling an odd eigenmode back
through the algebraic D-equivalence.  The metric is never transported through
D; the identity is purely linear-algebraic. -/
theorem oddEigenmode_pulledBack_shiftedEven_eq_neg_sourceCubic
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    (lam : ℝ)
    (w : euclideanOddBoundaryFlatSubspace K)
    (hweig :
      parityCompressedCanonical .odd L K w = (lam : ℂ) • w) :
    let E := euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)
    let v := E.symm w
    evenCompressedCanonical L K v - (lam : ℂ) • v =
      -(evenQuadraticSourceMoment L K v) •
        pulledBackCubicCompressionVector K hK := by
  let E := euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)
  let v : euclideanEvenBoundaryFlatSubspace K := E.symm w
  have hfac :=
    conjugatedParityCompressionDefect_eq_cubicFunctional_smul
      hL K hK v
  have hsource :=
    cubicDefectFunctional_eq_evenQuadraticSourceMoment
      hL K hK v
  have hconj :
      oddCompressedCanonicalConjugated L K (by omega) v =
        (lam : ℂ) • v := by
    change
      E.symm
          (oddCompressedCanonical L K (E v)) =
        (lam : ℂ) • v
    change oddCompressedCanonical L K w = (lam : ℂ) • w at hweig
    calc
      E.symm (oddCompressedCanonical L K (E v)) =
          E.symm (oddCompressedCanonical L K w) := by
            rw [show E v = w by simp [v, E]]
      _ = E.symm ((lam : ℂ) • w) := by rw [hweig]
      _ = (lam : ℂ) • E.symm w := by rw [map_smul]
      _ = (lam : ℂ) • v := by rfl
  change
    oddCompressedCanonicalConjugated L K (by omega) v -
        evenCompressedCanonical L K v =
      cubicDefectFunctional L K v •
        pulledBackCubicCompressionVector K hK at hfac
  rw [hconj, hsource] at hfac
  dsimp
  change
    evenCompressedCanonical L K v - (lam : ℂ) • v =
      -(evenQuadraticSourceMoment L K v) •
        pulledBackCubicCompressionVector K hK
  simpa only [neg_sub, neg_smul] using congrArg Neg.neg hfac

/-- Strict-odd analogue of the source-gap theorem.  The source moment is now
evaluated on the even vector obtained by pulling the odd ground state back
through the D-equivalence. -/
theorem exists_pulledBackOddGround_source_gap_bound_of_strict
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hstrict :
      parityRayleighBottom .odd L (N + 1) <
        parityRayleighBottom .even L (N + 1)) :
    ∃ v : euclideanEvenBoundaryFlatSubspace (N + 1),
      v ≠ 0 ∧
      evenQuadraticSourceMoment L (N + 1) v ≠ 0 ∧
      (parityRayleighBottom .even L (N + 1) -
          parityRayleighBottom .odd L (N + 1)) * ‖v‖ ^ 2 ≤
        ‖evenQuadraticSourceMoment L (N + 1) v‖ *
          ‖pulledBackCubicCompressionVector (N + 1) (by omega)‖ * ‖v‖ := by
  obtain ⟨w, hwne, hweig⟩ :=
    exists_eigenmode_at_parityRayleighBottom_succ
      .odd L N hN
  let E :=
    euclideanEvenOddBoundaryFlatLinearEquiv (N + 1) (by omega)
  let v : euclideanEvenBoundaryFlatSubspace (N + 1) := E.symm w
  have hvne : v ≠ 0 := by
    intro hv
    apply hwne
    apply E.symm.injective
    exact hv.trans (map_zero E.symm).symm
  have hshift :=
    parityRayleighBottom_gap_mul_norm_sq_le_shifted
      .even L (N + 1)
      (parityRayleighBottom .odd L (N + 1)) v
  change
    (parityRayleighBottom .even L (N + 1) -
        parityRayleighBottom .odd L (N + 1)) * ‖v‖ ^ 2 ≤
      Complex.re
        (inner ℂ
          (evenCompressedCanonical L (N + 1) v -
            (parityRayleighBottom .odd L (N + 1) : ℂ) • v)
          v) at hshift
  have hident :=
    oddEigenmode_pulledBack_shiftedEven_eq_neg_sourceCubic
      hL (N + 1) (by omega)
      (parityRayleighBottom .odd L (N + 1)) w hweig
  dsimp only at hident
  rw [hident] at hshift
  have hupp :
      Complex.re
          (inner ℂ
            (-(evenQuadraticSourceMoment L (N + 1) v) •
              pulledBackCubicCompressionVector (N + 1) (by omega))
            v) ≤
        ‖evenQuadraticSourceMoment L (N + 1) v‖ *
          ‖pulledBackCubicCompressionVector (N + 1) (by omega)‖ * ‖v‖ := by
    calc
      Complex.re
          (inner ℂ
            (-(evenQuadraticSourceMoment L (N + 1) v) •
              pulledBackCubicCompressionVector (N + 1) (by omega))
            v) ≤
        |Complex.re
          (inner ℂ
            (-(evenQuadraticSourceMoment L (N + 1) v) •
              pulledBackCubicCompressionVector (N + 1) (by omega))
            v)| := le_abs_self _
      _ ≤ ‖inner ℂ
          (-(evenQuadraticSourceMoment L (N + 1) v) •
            pulledBackCubicCompressionVector (N + 1) (by omega))
          v‖ := Complex.abs_re_le_norm _
      _ ≤
        ‖-(evenQuadraticSourceMoment L (N + 1) v) •
            pulledBackCubicCompressionVector (N + 1) (by omega)‖ * ‖v‖ :=
          norm_inner_le_norm _ _
      _ =
        ‖evenQuadraticSourceMoment L (N + 1) v‖ *
          ‖pulledBackCubicCompressionVector (N + 1) (by omega)‖ * ‖v‖ := by
          rw [norm_smul, norm_neg]
  have hbound := le_trans hshift hupp
  have hsourceNe : evenQuadraticSourceMoment L (N + 1) v ≠ 0 := by
    intro hzero
    have hnorm : 0 < ‖v‖ ^ 2 := by positivity
    have hleft :
        0 <
          (parityRayleighBottom .even L (N + 1) -
              parityRayleighBottom .odd L (N + 1)) * ‖v‖ ^ 2 :=
      mul_pos (sub_pos.mpr hstrict) hnorm
    rw [hzero] at hbound
    simp at hbound
    exact (not_lt_of_ge hbound) hleft
  exact ⟨v, hvne, hsourceNe, by simpa [v, E] using hbound⟩

/-- On a tied ground level, vanishing source defect on an even ground eigenmode
forces its D-image to be an odd eigenmode at the same eigenvalue.  This shows
exactly why the tie/source-zero branch is not killed by generic linear algebra:
it becomes exact ground-space transport. -/
theorem evenGround_maps_to_oddEigenmode_of_source_zero
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (v : euclideanEvenBoundaryFlatSubspace (N + 1))
    (hveig :
      parityCompressedCanonical .even L (N + 1) v =
        (parityRayleighBottom .even L (N + 1) : ℂ) • v)
    (hsource :
      evenQuadraticSourceMoment L (N + 1) v = 0) :
    parityCompressedCanonical .odd L (N + 1)
        (euclideanEvenToOddIndexLinearMap (N + 1) v) =
      (parityRayleighBottom .even L (N + 1) : ℂ) •
        euclideanEvenToOddIndexLinearMap (N + 1) v := by
  have hident :=
    evenEigenmode_shiftedOdd_eq_sourceCubic
      hL (N + 1) (by omega)
      (parityRayleighBottom .even L (N + 1)) v hveig
  rw [hsource, zero_smul] at hident
  change
    oddCompressedCanonical L (N + 1)
        (euclideanEvenToOddIndexLinearMap (N + 1) v) =
      (parityRayleighBottom .even L (N + 1) : ℂ) •
        euclideanEvenToOddIndexLinearMap (N + 1) v
  exact sub_eq_zero.mp hident

end Zeta23.CCM

#print axioms Zeta23.CCM.evenEigenmode_shiftedOdd_eq_sourceCubic
#print axioms Zeta23.CCM.exists_evenGround_source_gap_bound_of_strict
#print axioms Zeta23.CCM.oddEigenmode_pulledBack_shiftedEven_eq_neg_sourceCubic
#print axioms Zeta23.CCM.exists_pulledBackOddGround_source_gap_bound_of_strict
#print axioms Zeta23.CCM.evenGround_maps_to_oddEigenmode_of_source_zero
