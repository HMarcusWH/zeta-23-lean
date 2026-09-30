import Zeta23.CCM.CanonicalGroundContinuity

noncomputable section

namespace Zeta23.CCM

/-!
# Production aperture location split

Every positive production aperture is either exactly a logarithmic integer
cutoff seam or lies strictly inside one fixed cutoff cell.  The proof is the
same floor/exp geometry already used by the global continuity theorem, exported
as a reusable branch object for the first-crossing barrier.

No assertion is made about the sign of the entering prime weight.
-/

/-- Exhaustive production location classification for a positive aperture. -/
inductive CanonicalApertureLocation (L : ℝ) : Prop
  | seam
      (q : ℕ)
      (two_le_q : 2 ≤ q)
      (eq_log : L = Real.log (q : ℝ))
  | interior
      (Q : ℕ)
      (one_le_Q : 1 ≤ Q)
      (mem_cell : L ∈ fixedCanonicalCutoffCell Q)

/-- Every positive aperture is either one exact log-integer seam or one open
physical cutoff cell. -/
theorem canonicalApertureLocation_of_pos
    {L : ℝ} (hL : 0 < L) :
    CanonicalApertureLocation L := by
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
    exact .seam Q hQtwo hlog
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
    exact .interior Q hQ ⟨hleft, hright⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalApertureLocation_of_pos
