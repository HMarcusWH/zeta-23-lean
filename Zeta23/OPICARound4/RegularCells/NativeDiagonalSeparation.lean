import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section

namespace Zeta23.OPICARound4.NativeParitySeparation

open scoped BigOperators ComplexConjugate

private theorem diagonal_mode_zero_of_sum_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (ha : Function.Injective a) (lam : ℝ) (x : ι → ℂ)
    (hs : ∑ i, x i = 0)
    (he : ∀ i, ((a i : ℂ) - (lam : ℂ)) * x i = 0) : x = 0 := by
  by_contra hx
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    simpa only [funext_iff, Pi.zero_apply, not_forall] using hx
  have hjlam : a j = lam := by
    have h := (mul_eq_zero.mp (he j)).resolve_right hj
    exact_mod_cast sub_eq_zero.mp h
  have hother : ∀ i, i ≠ j → x i = 0 := by
    intro i hij
    have hne : (a i : ℂ) - (lam : ℂ) ≠ 0 := by
      intro h
      have hai : a i = lam := by exact_mod_cast sub_eq_zero.mp h
      exact hij (ha (hai.trans hjlam.symm))
    exact (mul_eq_zero.mp (he i)).resolve_left hne
  have hsingle : (∑ i, x i) = x j := by
    apply Finset.sum_eq_single j
    · intro i hi hij
      exact hother i hij
    · simp
  exact hj (hsingle.symm.trans hs)

private theorem positive_diagonal_zero_of_energy_zero
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (w : ι → ℂ) (he : ∑ i, conj (w i) * (a i : ℂ) * w i = 0) : w = 0 := by
  have hterm (i : ι) : conj (w i) * (a i : ℂ) * w i =
      ((a i * Complex.normSq (w i) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply] <;> ring
  simp_rw [hterm] at he
  have hr : ∑ i, a i * Complex.normSq (w i) = 0 := by exact_mod_cast he
  funext i
  have hi : a i * Complex.normSq (w i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (ha j).le (Complex.normSq_nonneg _))).mp hr i (Finset.mem_univ i)
  exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (ne_of_gt (ha i)))

/-- The quotient-free compressed eigenrelations on `E = {sum x = sum a*x = 0}`
and on `sqrt(a) E` cannot share an eigenvalue. The second relation has been
pulled back through the full positive diagonal, so it retains the Gram `a`.
No restriction excluding the ambient poles `lam = a i` is imposed. -/
theorem diagonal_two_moment_compressions_disjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (hinj : Function.Injective a)
    (lam : ℝ) (x z : ι → ℂ)
    (hx : x ≠ 0) (hz : z ≠ 0)
    (hx0 : ∑ i, x i = 0) (hx1 : ∑ i, (a i : ℂ) * x i = 0)
    (hz0 : ∑ i, z i = 0) (hz1 : ∑ i, (a i : ℂ) * z i = 0)
    (c d e f : ℂ)
    (hxE : ∀ i, ((a i : ℂ) - (lam : ℂ)) * x i = c + d * (a i : ℂ))
    (hzO : ∀ i, (a i : ℂ) * ((a i : ℂ) - (lam : ℂ)) * z i =
      e + f * (a i : ℂ)) : False := by
  have hd : d ≠ 0 := by
    intro hd
    have hs : ∑ i, ((a i : ℂ) - (lam : ℂ)) * x i =
        ∑ _i : ι, c := by
      apply Finset.sum_congr rfl
      intro i _
      simpa [hd] using hxE i
    simp_rw [sub_mul] at hs
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hx1, hx0, mul_zero,
      sub_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    have hc : c = 0 := by
      have hn : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      exact (mul_eq_zero.mp hs.symm).resolve_left hn
    exact hx (diagonal_mode_zero_of_sum_zero a hinj lam x hx0
      (fun i => by simpa [hc, hd] using hxE i))
  have hpair : ∑ i, conj (x i) *
      ((a i : ℂ) * ((a i : ℂ) - (lam : ℂ)) * z i) = 0 := by
    simp_rw [hzO, mul_add, Finset.sum_add_distrib]
    have h0 : ∑ i, conj (x i) = 0 := by
      simpa only [map_sum, map_zero] using congrArg (fun t : ℂ => conj t) hx0
    have h1 : ∑ i, conj (x i) * (a i : ℂ) = 0 := by
      simpa only [map_sum, map_mul, Complex.conj_ofReal, map_zero, mul_comm] using
        congrArg (fun t : ℂ => conj t) hx1
    calc
      (∑ i, conj (x i) * e) + ∑ i, conj (x i) * (f * (a i : ℂ)) =
          (∑ i, conj (x i)) * e + (∑ i, conj (x i) * (a i : ℂ)) * f := by
            simp only [Finset.sum_mul]
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = 0 := by rw [h0, h1]; ring
  have hz2 : ∑ i, (a i : ℂ) ^ 2 * z i = 0 := by
    have hterm (i : ι) : conj (x i) *
        ((a i : ℂ) * ((a i : ℂ) - (lam : ℂ)) * z i) =
        conj c * ((a i : ℂ) * z i) + conj d * ((a i : ℂ) ^ 2 * z i) := by
      have hi := congrArg (fun t : ℂ => conj t) (hxE i)
      simp only [map_mul, map_sub, map_add, Complex.conj_ofReal] at hi
      linear_combination (a i : ℂ) * z i * hi
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hz1, mul_zero,
      zero_add] at hpair
    exact (mul_eq_zero.mp hpair).resolve_left (by simpa using hd)
  let w : ι → ℂ := fun i => ((a i : ℂ) - (lam : ℂ)) * z i
  have hw0 : ∑ i, w i = 0 := by
    simp [w, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hz0, hz1]
  have hw1 : ∑ i, (a i : ℂ) * w i = 0 := by
    have hterm (i : ι) : (a i : ℂ) * w i =
        (a i : ℂ) ^ 2 * z i - (lam : ℂ) * ((a i : ℂ) * z i) := by
      dsimp [w]; ring
    simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hz2, hz1, mul_zero, sub_zero]
  have hwE : ∀ i, (a i : ℂ) * w i = e + f * (a i : ℂ) := by
    intro i
    simpa only [w, mul_assoc] using hzO i
  have hwenergy : ∑ i, conj (w i) * (a i : ℂ) * w i = 0 := by
    have h0 : ∑ i, conj (w i) = 0 := by
      simpa only [map_sum, map_zero] using congrArg (fun t : ℂ => conj t) hw0
    have h1 : ∑ i, conj (w i) * (a i : ℂ) = 0 := by
      simpa only [map_sum, map_mul, Complex.conj_ofReal, map_zero, mul_comm] using
        congrArg (fun t : ℂ => conj t) hw1
    calc
      (∑ i, conj (w i) * (a i : ℂ) * w i) =
          (∑ i, conj (w i)) * e + (∑ i, conj (w i) * (a i : ℂ)) * f := by
        simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        linear_combination conj (w i) * hwE i
      _ = 0 := by rw [h0, h1]; ring
  have hw : w = 0 := positive_diagonal_zero_of_energy_zero a ha w hwenergy
  exact hz (diagonal_mode_zero_of_sum_zero a hinj lam z hz0
    (fun i => congrFun hw i))

/-- Literal positive-index form for the limiting native parity carriers. Even
vectors have zero zeroth and squared-index moments; odd vectors have zero
reciprocal-index and first-index moments. The residuals are the complete
orthogonal normals, not an assumed source sign or an omitted complement. -/
theorem native_squared_index_compressions_disjoint
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (x y : Fin K → ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hx0 : ∑ i, x i = 0)
    (hx2 : ∑ i, (i.val + 1 : ℂ) ^ 2 * x i = 0)
    (hyinv : ∑ i, y i / (i.val + 1 : ℂ) = 0)
    (hy1 : ∑ i, (i.val + 1 : ℂ) * y i = 0)
    (c d e f : ℂ)
    (hxE : ∀ i, ((i.val + 1 : ℂ) ^ 2 - (lam : ℂ)) * x i =
      c + d * (i.val + 1 : ℂ) ^ 2)
    (hyO : ∀ i, ((i.val + 1 : ℂ) ^ 2 - (lam : ℂ)) * y i =
      e / (i.val + 1 : ℂ) + f * (i.val + 1 : ℂ)) : False := by
  haveI : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  let a : Fin K → ℝ := fun i => ((i.val : ℝ) + 1) ^ 2
  let z : Fin K → ℂ := fun i => y i / (i.val + 1 : ℂ)
  have hn (i : Fin K) : (i.val + 1 : ℂ) ≠ 0 := by
    have hr : (0 : ℝ) < (i.val : ℝ) + 1 := by positivity
    exact_mod_cast ne_of_gt hr
  have ha (i : Fin K) : 0 < a i := by dsimp [a]; positivity
  have hinj : Function.Injective a := by
    intro i j hij
    have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    have hj : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
    have heq : (i.val : ℝ) = (j.val : ℝ) := by
      dsimp [a] at hij
      nlinarith
    exact Fin.ext (by exact_mod_cast heq)
  have hac (i : Fin K) : (a i : ℂ) = (i.val + 1 : ℂ) ^ 2 := by
    dsimp [a]; push_cast; rfl
  have hz : z ≠ 0 := by
    intro hz
    apply hy
    funext i
    have hi := congrFun hz i
    change y i / (i.val + 1 : ℂ) = 0 at hi
    exact (div_eq_zero_iff.mp hi).resolve_right (hn i)
  have hz1 : ∑ i, (a i : ℂ) * z i = 0 := by
    calc
      (∑ i, (a i : ℂ) * z i) = ∑ i, (i.val + 1 : ℂ) * y i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hac]
        dsimp [z]
        field_simp
      _ = 0 := hy1
  apply diagonal_two_moment_compressions_disjoint a ha hinj lam x z hx hz
    hx0 (by simpa only [hac] using hx2) hyinv hz1 c d e f
  · intro i
    simpa only [hac] using hxE i
  · intro i
    rw [hac]
    dsimp [z]
    have hi := hyO i
    field_simp at hi ⊢
    linear_combination hi

end Zeta23.OPICARound4.NativeParitySeparation
