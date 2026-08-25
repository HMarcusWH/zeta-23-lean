import Zeta23.ExceptionalZero.PoleKiller

noncomputable section

namespace Zeta23.ZeroConfig

/-- Reflection is an involutive permutation of every abstract zero configuration. -/
def reflectEquiv (Z : ZeroConfig) : Z.carrier ≃ Z.carrier where
  toFun ρ := ⟨reflect ρ, Z.reflect_mem ρ ρ.2⟩
  invFun ρ := ⟨reflect ρ, Z.reflect_mem ρ ρ.2⟩
  left_inv ρ := by
    ext
    simp [reflect]
  right_inv ρ := by
    ext
    simp [reflect]

end Zeta23.ZeroConfig

namespace Zeta23.ExceptionalZero

open Complex
open scoped BigOperators ComplexConjugate

/-!
# X0: two-translate Weil algebra

This file is deliberately algebraic. It proves the sign/conjugation package for
`ZeroConfig.W` in the repository's exact Fourier convention before any exposed-pole
growth argument is attempted.
-/

/-- Reflection of a zero conjugates its centered spectral coordinate. -/
theorem gammaOf_reflect_weil (ρ : ℂ) :
    gammaOf (reflect ρ) = (starRingEnd ℂ) (gammaOf ρ) := by
  simp only [gammaOf, reflect, map_div₀, map_sub, map_one, map_ofNat, Complex.conj_I]
  field_simp
  ring

/-- The two Fourier phases created by translating both arguments by the same real amount cancel. -/
theorem translate_phase_cancel (z : ℂ) (t : ℝ) :
    Complex.exp (Complex.I * z * (t : ℂ)) *
        (starRingEnd ℂ)
          (Complex.exp (Complex.I * (starRingEnd ℂ) z * (t : ℂ))) = 1 := by
  change Complex.exp (Complex.I * z * (t : ℂ)) *
      conj (Complex.exp (Complex.I * conj z * (t : ℂ))) = 1
  rw [← Complex.exp_conj]
  have harg :
      conj (Complex.I * conj z * (t : ℂ)) =
        -(Complex.I * z * (t : ℂ)) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
    ring
  rw [harg, ← Complex.exp_add]
  ring_nf
  simp

/-- Simultaneously translating both arguments leaves the genuine Weil form unchanged. -/
theorem W_translateRight_both (Z : ZeroConfig) (f g : ℝ → ℂ) (t : ℝ) :
    Z.W (translateRight f t) (translateRight g t) = Z.W f g := by
  unfold ZeroConfig.W
  refine tsum_congr fun ρ => ?_
  unfold ZeroConfig.Wsummand
  rw [paperFT_translateRight, paperFT_translateRight, map_mul]
  have hp := translate_phase_cancel (gammaOf (ρ : ℂ)) t
  calc
    (Z.mult (ρ : ℂ) : ℂ) *
          (Complex.exp (Complex.I * gammaOf (ρ : ℂ) * (t : ℂ)) *
            paperFT f (gammaOf (ρ : ℂ))) *
          ((starRingEnd ℂ)
              (Complex.exp
                (Complex.I * (starRingEnd ℂ) (gammaOf (ρ : ℂ)) * (t : ℂ))) *
            (starRingEnd ℂ)
              (paperFT g ((starRingEnd ℂ) (gammaOf (ρ : ℂ))))) =
        (Complex.exp (Complex.I * gammaOf (ρ : ℂ) * (t : ℂ)) *
            (starRingEnd ℂ)
              (Complex.exp
                (Complex.I * (starRingEnd ℂ) (gammaOf (ρ : ℂ)) * (t : ℂ)))) *
          ((Z.mult (ρ : ℂ) : ℂ) * paperFT f (gammaOf (ρ : ℂ)) *
            (starRingEnd ℂ)
              (paperFT g ((starRingEnd ℂ) (gammaOf (ρ : ℂ))))) := by
      ring
    _ = (Z.mult (ρ : ℂ) : ℂ) * paperFT f (gammaOf (ρ : ℂ)) *
          (starRingEnd ℂ) (paperFT g ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))) := by
      rw [hp]
      ring

/-- The exact `ZeroConfig.W` convention is Hermitian under the zero reflection involution. -/
theorem W_star_swap (Z : ZeroConfig) (f g : ℝ → ℂ) :
    (starRingEnd ℂ) (Z.W f g) = Z.W g f := by
  unfold ZeroConfig.W
  change star (∑' ρ : Z.carrier, Z.Wsummand f g ρ) =
    ∑' ρ : Z.carrier, Z.Wsummand g f ρ
  rw [tsum_star]
  calc
    (∑' ρ : Z.carrier, star (Z.Wsummand f g ρ)) =
        ∑' ρ : Z.carrier, Z.Wsummand g f (Z.reflectEquiv ρ) := by
      refine tsum_congr fun ρ => ?_
      have hm : Z.mult (reflect (ρ : ℂ)) = Z.mult (ρ : ℂ) :=
        Z.mult_reflect (ρ : ℂ) ρ.2
      change
        (starRingEnd ℂ) (Z.Wsummand f g (ρ : ℂ)) =
          Z.Wsummand g f (Z.reflectEquiv ρ)
      simp [ZeroConfig.Wsummand, ZeroConfig.reflectEquiv, hm,
        gammaOf_reflect_weil] <;> ring
    _ = ∑' ρ : Z.carrier, Z.Wsummand g f ρ :=
      Equiv.tsum_eq (Z.reflectEquiv) (fun ρ : Z.carrier => Z.Wsummand g f ρ)

/-- Equivalent Hermitian-symmetry orientation. -/
theorem W_swap_eq_star (Z : ZeroConfig) (f g : ℝ → ℂ) :
    Z.W g f = (starRingEnd ℂ) (Z.W f g) :=
  (W_star_swap Z f g).symm

/-- Every diagonal Weil value is fixed by complex conjugation. -/
theorem W_self_star (Z : ZeroConfig) (f : ℝ → ℂ) :
    (starRingEnd ℂ) (Z.W f f) = Z.W f f :=
  W_star_swap Z f f

/-- Hence every diagonal Weil value is real. -/
theorem W_self_im_eq_zero (Z : ZeroConfig) (f : ℝ → ℂ) :
    (Z.W f f).im = 0 := by
  have h := congrArg Complex.im (W_self_star Z f)
  simp only [Complex.conj_im] at h
  linarith

/-- Diagonal translation invariance, isolated for the two-translate construction. -/
theorem W_translateRight_self (Z : ZeroConfig) (f : ℝ → ℂ) (t : ℝ) :
    Z.W (translateRight f t) (translateRight f t) = Z.W f f :=
  W_translateRight_both Z f f t

/-- Relative-translation cross-correlation used by X1--X3. -/
def weilRelativeCorrelation (Z : ZeroConfig) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  Z.W (translateRight f t) f

/-- The opposite off-diagonal entry is the conjugate relative correlation. -/
theorem W_f_translateRight_eq_star_relativeCorrelation
    (Z : ZeroConfig) (f : ℝ → ℂ) (t : ℝ) :
    Z.W f (translateRight f t) =
      (starRingEnd ℂ) (weilRelativeCorrelation Z f t) := by
  exact (W_star_swap Z (translateRight f t) f).symm

#print axioms Zeta23.ExceptionalZero.W_translateRight_both
#print axioms Zeta23.ExceptionalZero.W_star_swap
#print axioms Zeta23.ExceptionalZero.W_self_im_eq_zero

end Zeta23.ExceptionalZero
