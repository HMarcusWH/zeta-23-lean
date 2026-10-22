import Zeta23.OPICAFollowup.MultiplicityTail

/-! Independent full-scope Laguerre norm and physical-domain consumers.
The expected type is written explicitly rather than obtained by reflection.
No moment, residual or terminal-memory conclusion is supplied as an input. -/
noncomputable section
open Set MeasureTheory Polynomial
open scoped Topology
open Zeta23.OPICAFollowup
namespace OPICAMultiplicityExpected

example (m : ℕ) (hm : 1 ≤ m) (p : ℂ) (hp : 0 < p.re) (T : ℝ) :
    (monicLaguerre (m-1)).Monic ∧
    (∀ Q : Polynomial ℝ, Q.natDegree < m-1 →
      laguerreWeightedPair (monicLaguerre (m-1)) Q = 0) ∧
    MemLp (monicLaguerreTail (m-1) p T) 2 volume ∧
    (monicLaguerreTailL2 (m-1) p T hp : ℝ → ℂ) =ᵐ[volume]
      monicLaguerreTail (m-1) p T ∧
    ‖monicLaguerreTailL2 (m-1) p T hp‖^2 =
      Real.exp (-2*p.re*T)*((m-1).factorial:ℝ)^2/(2*p.re)^(2*(m-1)+1) ∧
    ‖monicLaguerreTailL2 (m-1) p T hp‖ =
      Real.exp (-p.re*T)*((m-1).factorial:ℝ)/(2*p.re)^((m:ℝ)-1/2) := by
  exact laguerre_tail_norm m hm p hp T

/-- The degree-zero test is the literal constant polynomial. -/
example : monicLaguerre 0 = (1 : Polynomial ℝ) := by
  simp [monicLaguerre]

/-- The pointwise representative retains the conjugation and real shift. -/
example (n : ℕ) (p : ℂ) (T t : ℝ) (ht : T ≤ t) :
    monicLaguerreTail n p T t =
      (((2*p.re)^n)⁻¹*(monicLaguerre n).eval (2*p.re*(t-T)):ℝ)*
        Complex.exp (-(starRingEnd ℂ p)*(t:ℂ)) := by
  exact Set.indicator_of_mem ht _

example (n : ℕ) (p : ℂ) (T t : ℝ) (ht : t < T) :
    monicLaguerreTail n p T t = 0 := by
  exact Set.indicator_of_notMem (not_le.mpr ht) _

/-- Negative lower endpoints and either sign of the ordinate are permitted. -/
example (tau : ℝ) :
    ‖monicLaguerreTailL2 0 (1 + (tau:ℂ)*Complex.I) (-3) (by simp)‖ =
      Real.exp 3 / (2:ℝ)^(1/2:ℝ) := by
  have h := (laguerre_tail_norm 1 (by norm_num)
    (1 + (tau:ℂ)*Complex.I) (by simp) (-3)).2.2.2.2.2
  norm_num at h ⊢
  exact h

example (n : ℕ) (p : ℂ) (hp : 0 < p.re) (T : ℝ) :
    (∫ t : ℝ, ‖monicLaguerreTail n p T t‖^2) =
      Real.exp (-2*p.re*T)*(n.factorial:ℝ)^2/(2*p.re)^(2*n+1) := by
  exact monicLaguerreTail_integral_norm_sq n p T hp

#print axioms Zeta23.OPICAFollowup.laguerre_tail_norm
#print axioms Zeta23.OPICAFollowup.monicLaguerre_exact_norm_sq
#print axioms Zeta23.OPICAFollowup.monicLaguerre_orthogonality
#print axioms Zeta23.OPICAFollowup.laguerre_iterated_ibp
#print axioms Zeta23.OPICAFollowup.monicLaguerreTail_integral_norm_sq
end OPICAMultiplicityExpected
