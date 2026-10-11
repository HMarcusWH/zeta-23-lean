import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Ring.Units

noncomputable section

/-!
# M08 (Step 34): abstract cubic Schur formula

Write a self-adjoint family in block form along a kernel line and its
complement: `a(t)` is the scalar block, `b(t)` the coupling into the
complement and `H(t)` the complementary block.  A simple normalized kernel
vector at `t₀` means `a(t₀) = 0` and `b(t₀) = 0`; a positive complementary block
is used only through invertibility of `H(t₀)`.  The Schur scalar is
`s(t) = a(t) - ⟪b(t), H(t)⁻¹ b(t)⟫`.

* `cubic_schur_third_deriv`: with `R = H(t₀)⁻¹`,
  `s'''(t₀) = a''' - 3⟪b', R b''⟫ - 3⟪b'', R b'⟫ + 6⟪b', R H' R b'⟫`.
* `cubic_schur_third_deriv_response`: if `H(t₀)` is symmetric,
  `s'''(t₀) = a''' - 6⟪b', R b''⟫ + 6⟪R b', H' R b'⟫`, and with the response
  `w = -R b'` (`H w = -b'`), `s'''(t₀) = a''' + 6⟪b'', w⟫ + 6⟪H' w, w⟫`.
* `cubic_schur_third_nonpos_of_right_negative`: at a zero of order three that
  turns negative to the right (a stationary first-negative crossing with
  `s' = s'' = 0`), that expression is `≤ 0`.  This is a necessary condition
  only.

The setting is a real inner product space (complete for the inverse); a complex
Hermitian family is covered through its underlying real inner product
`Re ⟪·, ·⟫`.  Derivatives are passed as explicit functions near `t₀`.

Scope: abstract finite-order calculus.  The arithmetic third identity
`⟨F''' z, z⟩ = -(2π)² A_L[t³ e'_{Dz}(1 - t/L)]/L⁶ - 12 C/L` is a separate task,
gated on moving-aperture `C³` transport, and is not proved here.  Nothing here
concerns contacts or RH.
-/

namespace Zeta23.CCM

open Filter Set
open scoped Topology InnerProductSpace

section CubicSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Product rule for `t ↦ ⟪u t, M t (v t)⟫`. -/
theorem hasDerivAt_inner_clm_apply {u v : ℝ → E} {M : ℝ → E →L[ℝ] E} {u' v' : E}
    {M' : E →L[ℝ] E} {t : ℝ} (hu : HasDerivAt u u' t) (hM : HasDerivAt M M' t)
    (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => ⟪u s, M s (v s)⟫_ℝ)
      (⟪u', M t (v t)⟫_ℝ + ⟪u t, M' (v t)⟫_ℝ + ⟪u t, M t v'⟫_ℝ) t := by
  have h := hu.inner ℝ (hM.clm_apply hv)
  refine h.congr_deriv ?_
  rw [inner_add_right]
  ring

/-- **M08, abstract quadratic layer.**  If `b(t₀) = 0`, the Schur-type scalar
`s(t) = a(t) - ⟪b(t), G(t) b(t)⟫` is three times differentiable at `t₀` along
the chain `s, s', s''`, and
`s'''(t₀) = a''' - 3⟪b', G b''⟫ - 3⟪b'', G b'⟫ - 6⟪b', G' b'⟫`.  Derivatives
are given as explicit functions near `t₀`. -/
theorem schur_quadratic_chain {a a1 a2 : ℝ → ℝ} {a3 : ℝ} {b b1 b2 : ℝ → E} {b3 : E}
    {G G1 G2 : ℝ → E →L[ℝ] E} {G3 : E →L[ℝ] E} {t₀ : ℝ}
    (ha : ∀ᶠ t in 𝓝 t₀, HasDerivAt a (a1 t) t) (ha1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt a1 (a2 t) t)
    (ha2 : HasDerivAt a2 a3 t₀)
    (hb : ∀ᶠ t in 𝓝 t₀, HasDerivAt b (b1 t) t) (hb1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt b1 (b2 t) t)
    (hb2 : HasDerivAt b2 b3 t₀)
    (hG : ∀ᶠ t in 𝓝 t₀, HasDerivAt G (G1 t) t) (hG1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt G1 (G2 t) t)
    (hG2 : HasDerivAt G2 G3 t₀) (h0 : b t₀ = 0) :
    (∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => a t - ⟪b t, G t (b t)⟫_ℝ)
      (deriv (fun t => a t - ⟪b t, G t (b t)⟫_ℝ) t) t) ∧
    (∀ᶠ t in 𝓝 t₀, HasDerivAt (deriv fun t => a t - ⟪b t, G t (b t)⟫_ℝ)
      (deriv (deriv fun t => a t - ⟪b t, G t (b t)⟫_ℝ) t) t) ∧
    HasDerivAt (deriv (deriv fun t => a t - ⟪b t, G t (b t)⟫_ℝ))
      (a3 - 3 * ⟪b1 t₀, G t₀ (b2 t₀)⟫_ℝ - 3 * ⟪b2 t₀, G t₀ (b1 t₀)⟫_ℝ
        - 6 * ⟪b1 t₀, G1 t₀ (b1 t₀)⟫_ℝ) t₀ := by
  set Φ1 : ℝ → ℝ := fun t =>
    a1 t - (⟪b1 t, G t (b t)⟫_ℝ + ⟪b t, G1 t (b t)⟫_ℝ + ⟪b t, G t (b1 t)⟫_ℝ) with hΦ1
  set Φ2 : ℝ → ℝ := fun t =>
    a2 t - ((⟪b2 t, G t (b t)⟫_ℝ + ⟪b1 t, G1 t (b t)⟫_ℝ + ⟪b1 t, G t (b1 t)⟫_ℝ) +
      (⟪b1 t, G1 t (b t)⟫_ℝ + ⟪b t, G2 t (b t)⟫_ℝ + ⟪b t, G1 t (b1 t)⟫_ℝ) +
      (⟪b1 t, G t (b1 t)⟫_ℝ + ⟪b t, G1 t (b1 t)⟫_ℝ + ⟪b t, G t (b2 t)⟫_ℝ)) with hΦ2
  have hd1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => a t - ⟪b t, G t (b t)⟫_ℝ) (Φ1 t) t := by
    filter_upwards [ha, hb, hG] with t hat hbt hGt
    exact hat.sub (hasDerivAt_inner_clm_apply hbt hGt hbt)
  have hd2 : ∀ᶠ t in 𝓝 t₀, HasDerivAt Φ1 (Φ2 t) t := by
    filter_upwards [ha1, hb, hb1, hG, hG1] with t hat hbt hb1t hGt hG1t
    exact hat.sub (((hasDerivAt_inner_clm_apply hb1t hGt hbt).add
      (hasDerivAt_inner_clm_apply hbt hG1t hbt)).add (hasDerivAt_inner_clm_apply hbt hGt hb1t))
  have hbt := hb.self_of_nhds
  have hb1t := hb1.self_of_nhds
  have hGt := hG.self_of_nhds
  have hG1t := hG1.self_of_nhds
  have hd3 : HasDerivAt Φ2 _ t₀ := ha2.sub ((((hasDerivAt_inner_clm_apply hb2 hGt hbt).add
      (hasDerivAt_inner_clm_apply hb1t hG1t hbt)).add (hasDerivAt_inner_clm_apply hb1t hGt hb1t)).add
      (((hasDerivAt_inner_clm_apply hb1t hG1t hbt).add (hasDerivAt_inner_clm_apply hbt hG2 hbt)).add
        (hasDerivAt_inner_clm_apply hbt hG1t hb1t)) |>.add
      (((hasDerivAt_inner_clm_apply hb1t hGt hb1t).add (hasDerivAt_inner_clm_apply hbt hG1t hb1t)).add
        (hasDerivAt_inner_clm_apply hbt hGt hb2)))
  have e1 : deriv (fun t => a t - ⟪b t, G t (b t)⟫_ℝ) =ᶠ[𝓝 t₀] Φ1 :=
    hd1.mono fun t ht => ht.deriv
  have e2 : deriv (deriv fun t => a t - ⟪b t, G t (b t)⟫_ℝ) =ᶠ[𝓝 t₀] Φ2 :=
    e1.deriv.trans (hd2.mono fun t ht => ht.deriv)
  refine ⟨hd1.mono fun t ht => ht.differentiableAt.hasDerivAt, ?_, ?_⟩
  · filter_upwards [e1.eventuallyEq_nhds, hd2] with t het ht
    exact (ht.congr_of_eventuallyEq het).differentiableAt.hasDerivAt
  · refine (hd3.congr_of_eventuallyEq e2).congr_deriv ?_
    simp only [h0, map_zero, inner_zero_left, inner_zero_right, add_zero, zero_add]
    ring

/-- **M08, abstract quadratic layer, third derivative.** -/
theorem schur_quadratic_third_deriv {a a1 a2 : ℝ → ℝ} {a3 : ℝ} {b b1 b2 : ℝ → E} {b3 : E}
    {G G1 G2 : ℝ → E →L[ℝ] E} {G3 : E →L[ℝ] E} {t₀ : ℝ}
    (ha : ∀ᶠ t in 𝓝 t₀, HasDerivAt a (a1 t) t) (ha1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt a1 (a2 t) t)
    (ha2 : HasDerivAt a2 a3 t₀)
    (hb : ∀ᶠ t in 𝓝 t₀, HasDerivAt b (b1 t) t) (hb1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt b1 (b2 t) t)
    (hb2 : HasDerivAt b2 b3 t₀)
    (hG : ∀ᶠ t in 𝓝 t₀, HasDerivAt G (G1 t) t) (hG1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt G1 (G2 t) t)
    (hG2 : HasDerivAt G2 G3 t₀) (h0 : b t₀ = 0) :
    deriv (deriv (deriv fun t => a t - ⟪b t, G t (b t)⟫_ℝ)) t₀ =
      a3 - 3 * ⟪b1 t₀, G t₀ (b2 t₀)⟫_ℝ - 3 * ⟪b2 t₀, G t₀ (b1 t₀)⟫_ℝ
        - 6 * ⟪b1 t₀, G1 t₀ (b1 t₀)⟫_ℝ :=
  (schur_quadratic_chain ha ha1 ha2 hb hb1 hb2 hG hG1 hG2 h0).2.2.deriv

/-- Derivative of `t ↦ H(t)⁻¹` at a point where `H(t)` is invertible. -/
theorem hasDerivAt_ringInverse_comp [CompleteSpace E] {H : ℝ → E →L[ℝ] E}
    {H' : E →L[ℝ] E} {t : ℝ} (hu : IsUnit (H t)) (hd : HasDerivAt H H' t) :
    HasDerivAt (fun s => Ring.inverse (H s))
      (-(Ring.inverse (H t) * H' * Ring.inverse (H t))) t := by
  obtain ⟨u, hu⟩ := hu
  have h1 := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at h1
  have h := h1.comp_hasDerivAt t hd
  rw [← hu, Ring.inverse_unit]
  exact h

/-- The derivative chain of the Schur scalar `s(t) = a(t) - ⟪b(t), H(t)⁻¹ b(t)⟫`
at a point `t₀` with `b(t₀) = 0` and `H(t₀)` invertible. -/
theorem cubic_schur_chain [CompleteSpace E] {a a1 a2 : ℝ → ℝ} {a3 : ℝ}
    {b b1 b2 : ℝ → E} {b3 : E} {H H1 H2 : ℝ → E →L[ℝ] E} {H3 : E →L[ℝ] E} {t₀ : ℝ}
    (ha : ∀ᶠ t in 𝓝 t₀, HasDerivAt a (a1 t) t) (ha1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt a1 (a2 t) t)
    (ha2 : HasDerivAt a2 a3 t₀)
    (hb : ∀ᶠ t in 𝓝 t₀, HasDerivAt b (b1 t) t) (hb1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt b1 (b2 t) t)
    (hb2 : HasDerivAt b2 b3 t₀)
    (hH : ∀ᶠ t in 𝓝 t₀, HasDerivAt H (H1 t) t) (hH1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt H1 (H2 t) t)
    (hH2 : HasDerivAt H2 H3 t₀) (hunit : IsUnit (H t₀)) (h0 : b t₀ = 0) :
    (∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => a t - ⟪b t, Ring.inverse (H t) (b t)⟫_ℝ)
      (deriv (fun t => a t - ⟪b t, Ring.inverse (H t) (b t)⟫_ℝ) t) t) ∧
    (∀ᶠ t in 𝓝 t₀, HasDerivAt (deriv fun t => a t - ⟪b t, Ring.inverse (H t) (b t)⟫_ℝ)
      (deriv (deriv fun t => a t - ⟪b t, Ring.inverse (H t) (b t)⟫_ℝ) t) t) ∧
    HasDerivAt (deriv (deriv fun t => a t - ⟪b t, Ring.inverse (H t) (b t)⟫_ℝ))
      (a3 - 3 * ⟪b1 t₀, Ring.inverse (H t₀) (b2 t₀)⟫_ℝ
        - 3 * ⟪b2 t₀, Ring.inverse (H t₀) (b1 t₀)⟫_ℝ
        + 6 * ⟪b1 t₀, (Ring.inverse (H t₀) * H1 t₀ * Ring.inverse (H t₀)) (b1 t₀)⟫_ℝ) t₀ := by
  set G : ℝ → E →L[ℝ] E := fun t => Ring.inverse (H t) with hGdef
  set G1 : ℝ → E →L[ℝ] E := fun t => -(G t * H1 t * G t) with hG1def
  set G2 : ℝ → E →L[ℝ] E := fun t =>
    -((G1 t * H1 t + G t * H2 t) * G t + G t * H1 t * G1 t) with hG2def
  have hU : ∀ᶠ t in 𝓝 t₀, IsUnit (H t) :=
    hH.self_of_nhds.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hunit)
  have hG : ∀ᶠ t in 𝓝 t₀, HasDerivAt G (G1 t) t := by
    filter_upwards [hU, hH] with t hu hd
    exact hasDerivAt_ringInverse_comp hu hd
  have hG1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt G1 (G2 t) t := by
    filter_upwards [hG, hH1] with t hGt hH1t
    exact ((hGt.mul hH1t).mul hGt).neg
  have hG2 : HasDerivAt G2 _ t₀ :=
    ((((hG1.self_of_nhds.mul hH1.self_of_nhds).add (hG.self_of_nhds.mul hH2)).mul
      hG.self_of_nhds).add ((hG.self_of_nhds.mul hH1.self_of_nhds).mul hG1.self_of_nhds)).neg
  obtain ⟨c1, c2, c3⟩ := schur_quadratic_chain ha ha1 ha2 hb hb1 hb2 hG hG1 hG2 h0
  refine ⟨c1, c2, c3.congr_deriv ?_⟩
  simp only [hG1def, hGdef, neg_apply, inner_neg_right]
  ring

/-- **M08 (Step 34), abstract cubic Schur formula.**  Let `a`, `b`, `H` be
`C³` near `t₀` (derivatives given explicitly), `H(t₀)` invertible with
`R = H(t₀)⁻¹`, and `b(t₀) = 0`.  The Schur scalar
`s(t) = a(t) - ⟪b(t), H(t)⁻¹ b(t)⟫` has
`s'''(t₀) = a''' - 3⟪b', R b''⟫ - 3⟪b'', R b'⟫ + 6⟪b', R H' R b'⟫`. -/
theorem cubic_schur_third_deriv [CompleteSpace E] {a a1 a2 : ℝ → ℝ} {a3 : ℝ}
    {b b1 b2 : ℝ → E} {b3 : E} {H H1 H2 : ℝ → E →L[ℝ] E} {H3 : E →L[ℝ] E} {t₀ : ℝ}
    (ha : ∀ᶠ t in 𝓝 t₀, HasDerivAt a (a1 t) t) (ha1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt a1 (a2 t) t)
    (ha2 : HasDerivAt a2 a3 t₀)
    (hb : ∀ᶠ t in 𝓝 t₀, HasDerivAt b (b1 t) t) (hb1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt b1 (b2 t) t)
    (hb2 : HasDerivAt b2 b3 t₀)
    (hH : ∀ᶠ t in 𝓝 t₀, HasDerivAt H (H1 t) t) (hH1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt H1 (H2 t) t)
    (hH2 : HasDerivAt H2 H3 t₀) (hunit : IsUnit (H t₀)) (h0 : b t₀ = 0) :
    deriv (deriv (deriv fun t => a t - ⟪b t, Ring.inverse (H t) (b t)⟫_ℝ)) t₀ =
      a3 - 3 * ⟪b1 t₀, Ring.inverse (H t₀) (b2 t₀)⟫_ℝ
        - 3 * ⟪b2 t₀, Ring.inverse (H t₀) (b1 t₀)⟫_ℝ
        + 6 * ⟪b1 t₀, (Ring.inverse (H t₀) * H1 t₀ * Ring.inverse (H t₀)) (b1 t₀)⟫_ℝ :=
  (cubic_schur_chain ha ha1 ha2 hb hb1 hb2 hH hH1 hH2 hunit h0).2.2.deriv

/-- `H⁻¹` is symmetric when `H` is. -/
theorem ringInverse_symm [CompleteSpace E] {H : E →L[ℝ] E} (hunit : IsUnit H)
    (hsym : ∀ x y, ⟪H x, y⟫_ℝ = ⟪x, H y⟫_ℝ) (x y : E) :
    ⟪Ring.inverse H x, y⟫_ℝ = ⟪x, Ring.inverse H y⟫_ℝ := by
  have hHR : ∀ z, H (Ring.inverse H z) = z := fun z => by
    rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel H hunit,
      one_apply_eq_self]
  calc ⟪Ring.inverse H x, y⟫_ℝ = ⟪Ring.inverse H x, H (Ring.inverse H y)⟫_ℝ := by rw [hHR]
    _ = ⟪H (Ring.inverse H x), Ring.inverse H y⟫_ℝ := (hsym _ _).symm
    _ = ⟪x, Ring.inverse H y⟫_ℝ := by rw [hHR]

/-- **M08, symmetric and response forms.**  If moreover `H(t₀)` is symmetric,
then with `R = H(t₀)⁻¹` and the response `w = -R b'(t₀)` (so `H w = -b'`):
`s'''(t₀) = a''' - 6⟪b', R b''⟫ + 6⟪R b', H' (R b')⟫ = a''' + 6⟪b'', w⟫ + 6⟪H' w, w⟫`. -/
theorem cubic_schur_third_deriv_response [CompleteSpace E] {a a1 a2 : ℝ → ℝ} {a3 : ℝ}
    {b b1 b2 : ℝ → E} {b3 : E} {H H1 H2 : ℝ → E →L[ℝ] E} {H3 : E →L[ℝ] E} {t₀ : ℝ}
    (ha : ∀ᶠ t in 𝓝 t₀, HasDerivAt a (a1 t) t) (ha1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt a1 (a2 t) t)
    (ha2 : HasDerivAt a2 a3 t₀)
    (hb : ∀ᶠ t in 𝓝 t₀, HasDerivAt b (b1 t) t) (hb1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt b1 (b2 t) t)
    (hb2 : HasDerivAt b2 b3 t₀)
    (hH : ∀ᶠ t in 𝓝 t₀, HasDerivAt H (H1 t) t) (hH1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt H1 (H2 t) t)
    (hH2 : HasDerivAt H2 H3 t₀) (hunit : IsUnit (H t₀))
    (hsym : ∀ x y, ⟪H t₀ x, y⟫_ℝ = ⟪x, H t₀ y⟫_ℝ) (h0 : b t₀ = 0) :
    deriv (deriv (deriv fun t => a t - ⟪b t, Ring.inverse (H t) (b t)⟫_ℝ)) t₀ =
        a3 - 6 * ⟪b1 t₀, Ring.inverse (H t₀) (b2 t₀)⟫_ℝ
          + 6 * ⟪Ring.inverse (H t₀) (b1 t₀), H1 t₀ (Ring.inverse (H t₀) (b1 t₀))⟫_ℝ ∧
      deriv (deriv (deriv fun t => a t - ⟪b t, Ring.inverse (H t) (b t)⟫_ℝ)) t₀ =
        a3 + 6 * ⟪b2 t₀, -Ring.inverse (H t₀) (b1 t₀)⟫_ℝ
          + 6 * ⟪H1 t₀ (-Ring.inverse (H t₀) (b1 t₀)), -Ring.inverse (H t₀) (b1 t₀)⟫_ℝ := by
  have h := cubic_schur_third_deriv ha ha1 ha2 hb hb1 hb2 hH hH1 hH2 hunit h0
  set R := Ring.inverse (H t₀)
  have hR := ringInverse_symm hunit hsym
  have e1 : ⟪b2 t₀, R (b1 t₀)⟫_ℝ = ⟪b1 t₀, R (b2 t₀)⟫_ℝ := by
    rw [← hR, real_inner_comm]
  have e2 : ⟪b1 t₀, (R * H1 t₀ * R) (b1 t₀)⟫_ℝ = ⟪R (b1 t₀), H1 t₀ (R (b1 t₀))⟫_ℝ := by
    rw [mul_apply_eq_comp, mul_apply_eq_comp, ← hR]
  refine ⟨?_, ?_⟩
  · rw [h, e1, e2]
    ring
  · rw [h, e1, e2, map_neg, inner_neg_right, inner_neg_left, inner_neg_right, neg_neg,
      real_inner_comm (R (b1 t₀)) (H1 t₀ (R (b1 t₀))), ← hR (b1 t₀) (b2 t₀), real_inner_comm]
    ring

/-- **M08, necessary sign.**  If `s(t₀) = s'(t₀) = s''(t₀) = 0` and `s` takes
negative values arbitrarily close to the right of `t₀`, then `s'''(t₀) ≤ 0`.
This is a necessary condition only. -/
theorem third_deriv_nonpos_of_right_negative {s s1 s2 : ℝ → ℝ} {s3 t₀ : ℝ}
    (hs : ∀ᶠ t in 𝓝 t₀, HasDerivAt s (s1 t) t) (hs1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt s1 (s2 t) t)
    (hs2 : HasDerivAt s2 s3 t₀) (h0 : s t₀ = 0) (h1 : s1 t₀ = 0) (h2 : s2 t₀ = 0)
    (hright : ∀ ε > 0, ∃ t, t₀ < t ∧ t < t₀ + ε ∧ s t < 0) : s3 ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have hslope := hasDerivAt_iff_tendsto_slope.mp hs2
  have hev : ∀ᶠ t in 𝓝[>] t₀, 0 < s2 t := by
    have h' : ∀ᶠ t in 𝓝[≠] t₀, 0 < slope s2 t₀ t := hslope.eventually (lt_mem_nhds hpos)
    filter_upwards [nhdsWithin_mono t₀ (fun t (ht : t₀ < t) => ne_of_gt ht) h',
      self_mem_nhdsWithin] with t ht htt
    rw [slope_def_field, h2, sub_zero] at ht
    exact (div_pos_iff_of_pos_right (sub_pos.mpr htt)).mp ht
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hs.and hs1)
  obtain ⟨ε, hε, hright'⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp hev)
  set η := min (δ / 2) (ε / 2) with hη
  have hη0 : 0 < η := lt_min (half_pos hδ) (half_pos hε)
  have hmem : ∀ t ∈ Icc t₀ (t₀ + η), dist t t₀ < δ ∧ dist t t₀ < ε := by
    intro t ht
    have h1' : dist t t₀ ≤ η := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [ht.1])]
      linarith [ht.2]
    exact ⟨by linarith [min_le_left (δ / 2) (ε / 2)], by linarith [min_le_right (δ / 2) (ε / 2)]⟩
  have hd : ∀ t ∈ Icc t₀ (t₀ + η), HasDerivAt s (s1 t) t ∧ HasDerivAt s1 (s2 t) t :=
    fun t ht => hball (hmem t ht).1
  have hs2pos : ∀ t ∈ Ioo t₀ (t₀ + η), 0 < s2 t := fun t ht =>
    hright' (hmem t (Ioo_subset_Icc_self ht)).2 ht.1
  have hmono1 : StrictMonoOn s1 (Icc t₀ (t₀ + η)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
    · exact fun t ht => (hd t ht).2.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd t (Ioo_subset_Icc_self ht)).2.deriv]
      exact hs2pos t ht
  have hmono : StrictMonoOn s (Icc t₀ (t₀ + η)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
    · exact fun t ht => (hd t ht).1.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd t (Ioo_subset_Icc_self ht)).1.deriv, ← h1]
      exact hmono1 (left_mem_Icc.mpr (by linarith)) (Ioo_subset_Icc_self ht) ht.1
  obtain ⟨t, ht0, htη, hneg⟩ := hright η hη0
  have := hmono (left_mem_Icc.mpr (by linarith)) ⟨ht0.le, htη.le⟩ ht0
  rw [h0] at this
  linarith


/-- **M08, stationary first-negative crossing.**  If the Schur scalar
`s(t) = a(t) - ⟪b(t), H(t)⁻¹ b(t)⟫` has a zero of order three at `t₀`
(`a(t₀) = 0`, `b(t₀) = 0`, `s'(t₀) = s''(t₀) = 0`) and is negative arbitrarily
close to the right of `t₀`, then
`a''' - 3⟪b', R b''⟫ - 3⟪b'', R b'⟫ + 6⟪b', R H' R b'⟫ ≤ 0`.  Necessary only. -/
theorem cubic_schur_third_nonpos_of_right_negative [CompleteSpace E] {a a1 a2 : ℝ → ℝ} {a3 : ℝ}
    {b b1 b2 : ℝ → E} {b3 : E} {H H1 H2 : ℝ → E →L[ℝ] E} {H3 : E →L[ℝ] E} {t₀ : ℝ}
    (ha : ∀ᶠ t in 𝓝 t₀, HasDerivAt a (a1 t) t) (ha1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt a1 (a2 t) t)
    (ha2 : HasDerivAt a2 a3 t₀)
    (hb : ∀ᶠ t in 𝓝 t₀, HasDerivAt b (b1 t) t) (hb1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt b1 (b2 t) t)
    (hb2 : HasDerivAt b2 b3 t₀)
    (hH : ∀ᶠ t in 𝓝 t₀, HasDerivAt H (H1 t) t) (hH1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt H1 (H2 t) t)
    (hH2 : HasDerivAt H2 H3 t₀) (hunit : IsUnit (H t₀)) (h0 : b t₀ = 0)
    (ha0 : a t₀ = 0)
    (hs1 : deriv (fun t => a t - ⟪b t, Ring.inverse (H t) (b t)⟫_ℝ) t₀ = 0)
    (hs2 : deriv (deriv fun t => a t - ⟪b t, Ring.inverse (H t) (b t)⟫_ℝ) t₀ = 0)
    (hright : ∀ ε > 0, ∃ t, t₀ < t ∧ t < t₀ + ε ∧
      a t - ⟪b t, Ring.inverse (H t) (b t)⟫_ℝ < 0) :
    a3 - 3 * ⟪b1 t₀, Ring.inverse (H t₀) (b2 t₀)⟫_ℝ
        - 3 * ⟪b2 t₀, Ring.inverse (H t₀) (b1 t₀)⟫_ℝ
        + 6 * ⟪b1 t₀, (Ring.inverse (H t₀) * H1 t₀ * Ring.inverse (H t₀)) (b1 t₀)⟫_ℝ ≤ 0 := by
  obtain ⟨c1, c2, c3⟩ := cubic_schur_chain ha ha1 ha2 hb hb1 hb2 hH hH1 hH2 hunit h0
  exact third_deriv_nonpos_of_right_negative c1 c2 c3 (by simp [ha0, h0]) hs1 hs2 hright

end CubicSchur

end Zeta23.CCM

#print axioms Zeta23.CCM.schur_quadratic_third_deriv
#print axioms Zeta23.CCM.cubic_schur_chain
#print axioms Zeta23.CCM.cubic_schur_third_deriv
#print axioms Zeta23.CCM.cubic_schur_third_deriv_response
#print axioms Zeta23.CCM.third_deriv_nonpos_of_right_negative
#print axioms Zeta23.CCM.cubic_schur_third_nonpos_of_right_negative
