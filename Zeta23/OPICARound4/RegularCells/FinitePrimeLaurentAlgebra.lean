import Zeta23.OPICARound4.RegularCells.PrimeLaurentNonidentity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Zeta23.OPICARound4.RegularCells

def formalPrimeMonomial (s : Finset ℕ) (k : s → ℤ) (X : s → ℂˣ) : ℂ :=
  ∏ p : s, (X p : ℂ) ^ k p

theorem formalPrimeMonomial_zero (s : Finset ℕ) (X : s → ℂˣ) :
    formalPrimeMonomial s 0 X = 1 := by
  simp [formalPrimeMonomial]

theorem formalPrimeMonomial_add (s : Finset ℕ) (k l : s → ℤ) (X : s → ℂˣ) :
    formalPrimeMonomial s (k + l) X =
      formalPrimeMonomial s k X * formalPrimeMonomial s l X := by
  classical
  simp only [formalPrimeMonomial, Pi.add_apply]
  simp_rw [zpow_add₀ (Units.ne_zero _)]
  exact Finset.prod_mul_distrib

def HasPrimeLaurentExpansion (s : Finset ℕ) (F : ℂ → (s → ℂˣ) → ℂ) : Prop :=
  ∃ (t : Finset (s → ℤ)) (a : (s → ℤ) → ℂ → ℂ),
    (∀ k, MeromorphicAt (a k) 0) ∧
    ∀ z X, F z X = ∑ k ∈ t, a k z * formalPrimeMonomial s k X

theorem HasPrimeLaurentExpansion.congr {s : Finset ℕ}
    {F G : ℂ → (s → ℂˣ) → ℂ} (h : HasPrimeLaurentExpansion s F)
    (he : ∀ z X, F z X = G z X) : HasPrimeLaurentExpansion s G := by
  obtain ⟨t,a,ha,hF⟩ := h
  exact ⟨t,a,ha,fun z X => (he z X).symm.trans (hF z X)⟩

theorem HasPrimeLaurentExpansion.constant {s : Finset ℕ} (a : ℂ → ℂ)
    (ha : MeromorphicAt a 0) : HasPrimeLaurentExpansion s (fun z _ => a z) := by
  classical
  refine ⟨{0},fun _ => a,fun _ => ha,?_⟩
  intro z X
  simp [formalPrimeMonomial_zero]

theorem HasPrimeLaurentExpansion.monomial (s : Finset ℕ) (k : s → ℤ) :
    HasPrimeLaurentExpansion s (fun _ X => formalPrimeMonomial s k X) := by
  classical
  refine ⟨{k},fun _ _ => 1,fun _ => (by fun_prop),?_⟩
  intro z X
  simp

theorem formalPrimeMonomial_single (s : Finset ℕ) (p : s) (n : ℤ) (X : s → ℂˣ) :
    formalPrimeMonomial s (Pi.single p n) X = (X p : ℂ)^n := by
  classical
  unfold formalPrimeMonomial
  rw [Finset.prod_eq_single p]
  · simp
  · intro q hq hne
    simp [Pi.single_eq_of_ne hne]
  · simp

theorem HasPrimeLaurentExpansion.coordinate_zpow (s : Finset ℕ) (p : s) (n : ℤ) :
    HasPrimeLaurentExpansion s (fun _ X => (X p : ℂ)^n) := by
  apply (HasPrimeLaurentExpansion.monomial s (Pi.single p n)).congr
  intro z X
  exact formalPrimeMonomial_single s p n X

theorem HasPrimeLaurentExpansion.add {s : Finset ℕ}
    {F G : ℂ → (s → ℂˣ) → ℂ} (hF : HasPrimeLaurentExpansion s F)
    (hG : HasPrimeLaurentExpansion s G) :
    HasPrimeLaurentExpansion s (fun z X => F z X + G z X) := by
  classical
  obtain ⟨t,a,ha,hF⟩ := hF
  obtain ⟨u,b,hb,hG⟩ := hG
  let c : (s → ℤ) → ℂ → ℂ := fun k z =>
    (if k ∈ t then a k z else 0) + (if k ∈ u then b k z else 0)
  refine ⟨t ∪ u,c,?_,?_⟩
  · intro k
    dsimp [c]
    split_ifs <;> fun_prop
  · intro z X
    change F z X + G z X = _
    rw [hF,hG]
    simp only [c,add_mul,Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.sum_subset (Finset.subset_union_left (s₁ := t) (s₂ := u))]
      · apply Finset.sum_congr rfl
        intro k hk
        simp [hk]
      · intro k hk hkt
        simp [hkt]
    · rw [← Finset.sum_subset (Finset.subset_union_right (s₁ := t) (s₂ := u))]
      · apply Finset.sum_congr rfl
        intro k hk
        simp [hk]
      · intro k hk hku
        simp [hku]

theorem HasPrimeLaurentExpansion.neg {s : Finset ℕ}
    {F : ℂ → (s → ℂˣ) → ℂ} (hF : HasPrimeLaurentExpansion s F) :
    HasPrimeLaurentExpansion s (fun z X => -F z X) := by
  obtain ⟨t,a,ha,hF⟩ := hF
  refine ⟨t,fun k z => -a k z,fun k => (ha k).neg,?_⟩
  intro z X
  simp only [hF,neg_mul,Finset.sum_neg_distrib]

theorem HasPrimeLaurentExpansion.sub {s : Finset ℕ}
    {F G : ℂ → (s → ℂˣ) → ℂ} (hF : HasPrimeLaurentExpansion s F)
    (hG : HasPrimeLaurentExpansion s G) :
    HasPrimeLaurentExpansion s (fun z X => F z X - G z X) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem HasPrimeLaurentExpansion.mul {s : Finset ℕ}
    {F G : ℂ → (s → ℂˣ) → ℂ} (hF : HasPrimeLaurentExpansion s F)
    (hG : HasPrimeLaurentExpansion s G) :
    HasPrimeLaurentExpansion s (fun z X => F z X * G z X) := by
  classical
  obtain ⟨t,a,ha,hF⟩ := hF
  obtain ⟨u,b,hb,hG⟩ := hG
  let e : (s → ℤ) × (s → ℤ) → s → ℤ := fun kl => kl.1 + kl.2
  let c : (s → ℤ) → ℂ → ℂ := fun k z =>
    ∑ kl ∈ (t ×ˢ u).filter (fun kl => e kl = k), a kl.1 z * b kl.2 z
  refine ⟨(t ×ˢ u).image e,c,?_,?_⟩
  · intro k
    exact MeromorphicAt.fun_sum (fun kl _ => (ha kl.1).mul (hb kl.2))
  · intro z X
    change F z X * G z X = _
    rw [hF,hG]
    calc
      _ = ∑ kl ∈ t ×ˢ u, (a kl.1 z * b kl.2 z) *
          formalPrimeMonomial s (e kl) X := by
        rw [Finset.sum_product]
        simp only [Finset.sum_mul,Finset.mul_sum,e,formalPrimeMonomial_add]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ = ∑ k ∈ (t ×ˢ u).image e, ∑ kl ∈ (t ×ˢ u).filter (fun kl => e kl = k),
          (a kl.1 z * b kl.2 z) * formalPrimeMonomial s (e kl) X :=
        (Finset.sum_fiberwise_of_maps_to (fun kl hkl => Finset.mem_image_of_mem e hkl)
          (fun kl => (a kl.1 z * b kl.2 z) * formalPrimeMonomial s (e kl) X)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [c]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro kl hkl
        rw [(Finset.mem_filter.mp hkl).2]

theorem HasPrimeLaurentExpansion.sum {s : Finset ℕ} {ι : Type*}
    (t : Finset ι) (F : ι → ℂ → (s → ℂˣ) → ℂ)
    (hF : ∀ i ∈ t, HasPrimeLaurentExpansion s (F i)) :
    HasPrimeLaurentExpansion s (fun z X => ∑ i ∈ t, F i z X) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simpa using (HasPrimeLaurentExpansion.constant (s := s) (fun _ => 0) (by fun_prop))
  | @insert i t hi ih =>
    simpa [Finset.sum_insert hi] using
      (hF i (Finset.mem_insert_self i t)).add
        (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

theorem HasPrimeLaurentExpansion.prod {s : Finset ℕ} {ι : Type*}
    (t : Finset ι) (F : ι → ℂ → (s → ℂˣ) → ℂ)
    (hF : ∀ i ∈ t, HasPrimeLaurentExpansion s (F i)) :
    HasPrimeLaurentExpansion s (fun z X => ∏ i ∈ t, F i z X) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simpa using (HasPrimeLaurentExpansion.constant (s := s) (fun _ => 1) (by fun_prop))
  | @insert i t hi ih =>
    simpa [Finset.prod_insert hi] using
      (hF i (Finset.mem_insert_self i t)).mul
        (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

theorem HasPrimeLaurentExpansion.det {s : Finset ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : ℂ → (s → ℂˣ) → Matrix ι ι ℂ)
    (hM : ∀ i j, HasPrimeLaurentExpansion s (fun z X => M z X i j)) :
    HasPrimeLaurentExpansion s (fun z X => (M z X).det) := by
  classical
  have h := HasPrimeLaurentExpansion.sum Finset.univ
    (fun σ : Equiv.Perm ι => fun z X => (Equiv.Perm.sign σ : ℂ) * ∏ i, M z X (σ i) i)
    (fun σ _ =>
      (HasPrimeLaurentExpansion.constant (fun _ => (Equiv.Perm.sign σ : ℂ))
        (by fun_prop)).mul
      (HasPrimeLaurentExpansion.prod Finset.univ (fun i z X => M z X (σ i) i)
        (fun i _ => hM (σ i) i)))
  exact h.congr (fun z X => (Matrix.det_apply' (M z X)).symm)

def primePhaseUnits (s : Finset ℕ) (z : ℂ) : s → ℂˣ :=
  fun p => Units.mk0 (primePhase p z) (Complex.exp_ne_zero _)

theorem formalPrimeMonomial_actual (s : Finset ℕ) (k : s → ℤ) (z : ℂ) :
    formalPrimeMonomial s k (primePhaseUnits s z) = primeLaurentMonomial s k z := rfl

/-- A nonzero formal specialization detects a nonzero grouped coefficient germ.
The specialization may depend on z; it is not assumed to be the arithmetic path. -/
theorem HasPrimeLaurentExpansion.exists_nonzero_coefficient {s : Finset ℕ}
    {F : ℂ → (s → ℂˣ) → ℂ} (hF : HasPrimeLaurentExpansion s F)
    (X : ℂ → s → ℂˣ)
    (hX : ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ), F z (X z) = 0) :
    ∃ (t : Finset (s → ℤ)) (a : (s → ℤ) → ℂ → ℂ),
      (∀ k, MeromorphicAt (a k) 0) ∧
      (∀ z V, F z V = ∑ k ∈ t, a k z * formalPrimeMonomial s k V) ∧
      ∃ k ∈ t, ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ), a k z = 0 := by
  classical
  obtain ⟨t,a,ha,he⟩ := hF
  refine ⟨t,a,ha,he,?_⟩
  by_contra hn
  push_neg at hn
  have hz : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ k ∈ t, a k z = 0 := by
    exact (Filter.eventually_all_finset t).mpr hn
  apply hX
  filter_upwards [hz] with z hz
  rw [he]
  apply Finset.sum_eq_zero
  intro k hk
  rw [hz k hk,zero_mul]

/-- No actual-path nonidentity is assumed: a different nonzero formal phase test
plus genuine prime arithmetic and meromorphic coefficients forces it. -/
theorem HasPrimeLaurentExpansion.actual_germ_nonzero {s : Finset ℕ}
    (hs : ∀ p ∈ s, Nat.Prime p) {F : ℂ → (s → ℂˣ) → ℂ}
    (hF : HasPrimeLaurentExpansion s F) (X : ℂ → s → ℂˣ)
    (hX : ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ), F z (X z) = 0) :
    ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ), F z (primePhaseUnits s z) = 0 := by
  classical
  obtain ⟨t,a,ha,he,hne⟩ := hF.exists_nonzero_coefficient X hX
  have hf := meromorphic_frequency_germ_nonzero t a (primeLaurentFrequency s)
    (fun k _ => ha k) (primeLaurentFrequency_injective s hs).injOn hne
  intro hz
  apply hf
  filter_upwards [hz] with z hz
  rw [he] at hz
  simpa only [formalPrimeMonomial_actual,primeLaurentMonomial_eq_exp] using hz

end Zeta23.OPICARound4.RegularCells
