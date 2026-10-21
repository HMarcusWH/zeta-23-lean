import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

namespace Zeta23.OPICA
open Finset
open scoped BigOperators

/-- The actual number of ordered positive factorizations, with zero input excluded. -/
def divisorCount (order n : ℕ) : ℕ := (Nat.finMulAntidiag order n).card

/-- A product tuple for `ab` can be split coordinatewise into a tuple for `a` and one for `b`.
The proof uses the genuine multiplicative decomposition property of the natural numbers. -/
theorem factor_tuple_split (order : ℕ) (w : Fin order → ℕ) {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hw : ∏ i, w i = a*b) :
    ∃ u v : Fin order → ℕ, (∏ i, u i) = a ∧ (∏ i, v i) = b ∧
      ∀ i, w i = u i*v i := by
  induction order generalizing a b with
  | zero =>
    have hab : a = 1 ∧ b = 1 := by simpa using hw.symm
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      by simp [hab.1], by simp [hab.2], fun i => Fin.elim0 i⟩
  | succ order ih =>
    rw [Fin.prod_univ_succ] at hw
    have hdvd : w 0 ∣ a*b := by rw [← hw]; exact dvd_mul_right _ _
    obtain ⟨u0,v0,hu0,hv0,h0⟩ := exists_dvd_and_dvd_of_dvd_mul hdvd
    obtain ⟨a',ha'⟩ := hu0
    obtain ⟨b',hb'⟩ := hv0
    have hune : u0 ≠ 0 := by intro h; apply ha; simp [ha',h]
    have hvne : v0 ≠ 0 := by intro h; apply hb; simp [hb',h]
    have hane : a' ≠ 0 := by intro h; apply ha; simp [ha',h]
    have hbne : b' ≠ 0 := by intro h; apply hb; simp [hb',h]
    have htail : ∏ i : Fin order, w i.succ = a'*b' := by
      apply mul_left_cancel₀ (mul_ne_zero hune hvne)
      calc (u0*v0)*(∏ i : Fin order, w i.succ) = a*b := by rw [← h0]; exact hw
           _ = (u0*v0)*(a'*b') := by rw [ha',hb']; ring
    obtain ⟨u,v,hu,hv,huv⟩ := ih (fun i => w i.succ) hane hbne htail
    refine ⟨Fin.cons u0 u,Fin.cons v0 v,?_,?_,?_⟩
    · simpa [Fin.prod_univ_succ,hu] using ha'.symm
    · simpa [Fin.prod_univ_succ,hv] using hb'.symm
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using h0
      · simpa using huv j

theorem divisor_count_submultiplicative (order a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    divisorCount order (a*b) ≤ divisorCount order a * divisorCount order b := by
  let source := (Nat.finMulAntidiag order a) ×ˢ (Nat.finMulAntidiag order b)
  let multiply : (Fin order → ℕ) × (Fin order → ℕ) → (Fin order → ℕ) :=
    fun uv i => uv.1 i*uv.2 i
  have hsurj : Set.SurjOn multiply source (Nat.finMulAntidiag order (a*b)) := by
    intro w hw
    obtain ⟨u,v,hu,hv,huv⟩ := factor_tuple_split order w ha.ne' hb.ne'
      (Nat.mem_finMulAntidiag.mp hw).1
    refine ⟨(u,v),?_,?_⟩
    · exact mem_product.mpr ⟨Nat.mem_finMulAntidiag.mpr ⟨hu,ha.ne'⟩,
        Nat.mem_finMulAntidiag.mpr ⟨hv,hb.ne'⟩⟩
    · funext i; exact (huv i).symm
  have hcard := Finset.card_le_card_of_surjOn multiply hsurj
  simpa [source,divisorCount] using hcard

/-- An actual positive integer array realizes every pair of product marginals. -/
theorem factor_matrix_refinement (rows cols : ℕ) (u : Fin rows → ℕ) (v : Fin cols → ℕ)
    (hu : ∀ i, u i ≠ 0) (hv : ∀ j, v j ≠ 0) (hprod : ∏ i, u i = ∏ j, v j) :
    ∃ m : Fin rows → Fin cols → ℕ,
      (∀ i, ∏ j, m i j = u i) ∧ (∀ j, ∏ i, m i j = v j) := by
  induction rows generalizing v with
  | zero =>
    have hones : ∀ j, v j = 1 := by
      have h : ∏ j, v j = 1 := by simpa using hprod.symm
      simpa using (Finset.prod_eq_one_iff.mp h)
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun j => by simp [hones j]⟩
  | succ rows ih =>
    have htail : (∏ i : Fin rows, u i.succ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hu i.succ)
    have hvprod : ∏ j, v j = u 0*(∏ i : Fin rows, u i.succ) := by
      rw [← hprod, Fin.prod_univ_succ]
    obtain ⟨x,y,hx,hy,hxy⟩ := factor_tuple_split cols v (hu 0) htail hvprod
    have hyne : ∀ j, y j ≠ 0 := by
      intro j hj
      apply hv j
      rw [hxy j,hj,mul_zero]
    obtain ⟨m,hmrows,hmcols⟩ := ih (fun i => u i.succ) y (fun i => hu i.succ) hyne hy.symm
    refine ⟨Fin.cons x m,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using hmrows j
    · intro j
      simpa [Fin.prod_univ_succ,hmcols] using (hxy j).symm

def factorRows (order : ℕ) (w : Fin (order*order) → ℕ) (i : Fin order) : ℕ :=
  ∏ j : Fin order, w (finProdFinEquiv (i,j))

def factorCols (order : ℕ) (w : Fin (order*order) → ℕ) (j : Fin order) : ℕ :=
  ∏ i : Fin order, w (finProdFinEquiv (i,j))

theorem factorRows_prod (order : ℕ) (w : Fin (order*order) → ℕ) :
    (∏ i, factorRows order w i) = ∏ k, w k := by
  unfold factorRows
  calc (∏ i,∏ j,w (finProdFinEquiv (i,j))) =
      ∏ p : Fin order × Fin order,w (finProdFinEquiv p) := by
        simpa only [Finset.univ_product_univ] using
          (Finset.prod_product' (Finset.univ : Finset (Fin order)) Finset.univ
            (fun i j => w (finProdFinEquiv (i,j)))).symm
       _ = ∏ k,w k := Fintype.prod_equiv finProdFinEquiv _ _ (fun _ => rfl)

theorem divisor_count_square_le (order n : ℕ) (hn : 0 < n) :
    divisorCount order n ^ 2 ≤ divisorCount (order*order) n := by
  let marginals := fun w : Fin (order*order) → ℕ => (factorRows order w,factorCols order w)
  let target := (Nat.finMulAntidiag order n) ×ˢ (Nat.finMulAntidiag order n)
  have hsurj : Set.SurjOn marginals (Nat.finMulAntidiag (order*order) n)
      target := by
    rintro ⟨u,v⟩ huv
    obtain ⟨hu,hv⟩ := mem_product.mp huv
    obtain ⟨m,hmrows,hmcols⟩ := factor_matrix_refinement order order u v
      (Nat.ne_zero_of_mem_finMulAntidiag hu) (Nat.ne_zero_of_mem_finMulAntidiag hv)
      ((Nat.prod_eq_of_mem_finMulAntidiag hu).trans (Nat.prod_eq_of_mem_finMulAntidiag hv).symm)
    let w : Fin (order*order) → ℕ := fun k => m (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    have hreshape : ∀ i j, w (finProdFinEquiv (i,j)) = m i j := by
      intro i j
      change m (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1
        (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2 = m i j
      rw [Equiv.symm_apply_apply]
    have hrows : factorRows order w = u := by
      funext i
      simpa only [factorRows,hreshape] using hmrows i
    have hcols : factorCols order w = v := by
      funext j
      simpa only [factorCols,hreshape] using hmcols j
    refine ⟨w,Nat.mem_finMulAntidiag.mpr ⟨?_,hn.ne'⟩,?_⟩
    · rw [← factorRows_prod order w,hrows]
      exact Nat.prod_eq_of_mem_finMulAntidiag hu
    · exact Prod.ext hrows hcols
  have hcard := Finset.card_le_card_of_surjOn marginals hsurj
  simpa [divisorCount,pow_two,target] using hcard

theorem divisor_count_inverse_sum_le (order N : ℕ) :
    (∑ n ∈ Icc 1 N, (divisorCount order n : ℝ)/(n:ℝ)) ≤
      (∑ n ∈ Icc 1 N, (n:ℝ)⁻¹)^order := by
  classical
  let source : Finset (Σ n : ℕ, Fin order → ℕ) :=
    (Icc 1 N).sigma (fun n => Nat.finMulAntidiag order n)
  let box := Fintype.piFinset (fun _ : Fin order => Icc 1 N)
  let weight : (Fin order → ℕ) → ℝ := fun f => ∏ i, (f i : ℝ)⁻¹
  have hweight {n : ℕ} {f : Fin order → ℕ} (hf : f ∈ Nat.finMulAntidiag order n) :
      weight f = (n:ℝ)⁻¹ := by
    dsimp [weight]
    rw [Finset.prod_inv_distrib]
    congr 1
    exact_mod_cast Nat.prod_eq_of_mem_finMulAntidiag hf
  have hmaps : source.image (fun p => p.2) ⊆ box := by
    intro f hf
    obtain ⟨⟨n,w⟩,hp,rfl⟩ := mem_image.mp hf
    obtain ⟨hn,hw⟩ := mem_sigma.mp hp
    apply Fintype.mem_piFinset.mpr
    intro i
    exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_finMulAntidiag hw i),
      (Nat.le_of_dvd ((mem_Icc.mp hn).1) (Nat.dvd_of_mem_finMulAntidiag hw i)).trans
        (mem_Icc.mp hn).2⟩
  have hinj : Set.InjOn (fun p : Σ n : ℕ, Fin order → ℕ => p.2) source := by
    intro x hx y hy hxy
    have hpx := Nat.prod_eq_of_mem_finMulAntidiag (mem_sigma.mp hx).2
    have hpy := Nat.prod_eq_of_mem_finMulAntidiag (mem_sigma.mp hy).2
    have hfst : x.1 = y.1 := hpx.symm.trans ((congrArg (fun f : Fin order → ℕ => ∏ i,f i) hxy).trans hpy)
    exact Sigma.ext hfst (heq_of_eq hxy)
  calc (∑ n ∈ Icc 1 N, (divisorCount order n : ℝ)/(n:ℝ)) =
      ∑ p ∈ source,weight p.2 := by
        rw [Finset.sum_sigma]
        apply sum_congr rfl
        intro n hn
        rw [show (∑ f ∈ Nat.finMulAntidiag order n,weight f) =
            ∑ f ∈ Nat.finMulAntidiag order n,(n:ℝ)⁻¹ by
              apply sum_congr rfl; intro f hf; exact hweight hf]
        simp [divisorCount,div_eq_mul_inv]
       _ = ∑ f ∈ source.image (fun p => p.2),weight f := (sum_image hinj).symm
       _ ≤ ∑ f ∈ box,weight f := sum_le_sum_of_subset_of_nonneg hmaps
         (fun f _ _ => Finset.prod_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)))
       _ = (∑ n ∈ Icc 1 N,(n:ℝ)⁻¹)^order := by
         simpa [box,weight] using (Finset.sum_pow' (Icc 1 N) (fun n : ℕ => (n:ℝ)⁻¹) order).symm

theorem divisor_count_harmonic_sum_le (order : ℕ) (X : ℝ) (hX : 1 ≤ X) :
    (∑ n ∈ Icc 1 ⌊X⌋₊, (divisorCount order n : ℝ)^2/(n:ℝ)) ≤
      (1+Real.log X)^(order*order) := by
  have hH : (∑ n ∈ Icc 1 ⌊X⌋₊,(n:ℝ)⁻¹) ≤ 1+Real.log X := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
      using harmonic_floor_le_one_add_log X hX
  calc _ ≤ ∑ n ∈ Icc 1 ⌊X⌋₊,(divisorCount (order*order) n : ℝ)/(n:ℝ) := by
         apply sum_le_sum
         intro n hn
         apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
         exact_mod_cast divisor_count_square_le order n ((mem_Icc.mp hn).1)
       _ ≤ (∑ n ∈ Icc 1 ⌊X⌋₊,(n:ℝ)⁻¹)^(order*order) := divisor_count_inverse_sum_le _ _
       _ ≤ (1+Real.log X)^(order*order) := by
         gcongr

theorem inverse_sqrt_partial_sum_le (N : ℕ) :
    (∑ n ∈ Icc 1 N, (Real.sqrt (n:ℝ))⁻¹) ≤ 2*Real.sqrt (N:ℝ) := by
  have hstep : ∀ n : ℕ, (Real.sqrt (n+1:ℝ))⁻¹ ≤
      2*(Real.sqrt (n+1:ℝ)-Real.sqrt (n:ℝ)) := by
    intro n
    have hp : 0 < Real.sqrt (n+1:ℝ) := Real.sqrt_pos.mpr (by positivity)
    rw [← one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith [sq_nonneg (Real.sqrt (n+1:ℝ)-Real.sqrt (n:ℝ)),
      Real.sq_sqrt (by positivity : (0:ℝ)≤n+1), Real.sq_sqrt (Nat.cast_nonneg n)]
  have hrange : ∀ N : ℕ, (∑ k ∈ range N,(Real.sqrt (k+1:ℝ))⁻¹) ≤ 2*Real.sqrt (N:ℝ) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ]
      have hn := hstep N
      push_cast
      nlinarith
  have heq : (∑ n ∈ Icc 1 N,(Real.sqrt (n:ℝ))⁻¹) =
      ∑ k ∈ range N,(Real.sqrt (k+1:ℝ))⁻¹ := by
    rw [range_eq_Ico]
    simpa only [Ico_add_one_right_eq_Icc,Nat.cast_add,Nat.cast_one] using
      (Finset.sum_Ico_add' (fun n : ℕ => (Real.sqrt (n:ℝ))⁻¹) 0 N 1).symm
  rw [heq]
  exact hrange N

theorem divisor_count_sqrt_sum_succ_le (order N : ℕ) :
    (∑ n ∈ Icc 1 N,(divisorCount (order+1) n : ℝ)/Real.sqrt (n:ℝ)) ≤
      2*Real.sqrt (N:ℝ)*(∑ n ∈ Icc 1 N,(n:ℝ)⁻¹)^order := by
  classical
  let source : Finset (Σ n : ℕ,Fin (order+1) → ℕ) :=
    (Icc 1 N).sigma (fun n => Nat.finMulAntidiag (order+1) n)
  let box := Fintype.piFinset (fun _ : Fin order => Icc 1 N)
  let target : Finset (Σ f : Fin order → ℕ,ℕ) :=
    box.sigma (fun f => Icc 1 (N/(∏ i,f i)))
  let split : (Σ n : ℕ,Fin (order+1) → ℕ) → (Σ f : Fin order → ℕ,ℕ) :=
    fun p => ⟨fun i => p.2 i.succ,p.2 0⟩
  let weight : (Σ f : Fin order → ℕ,ℕ) → ℝ :=
    fun p => (Real.sqrt ((∏ i,p.1 i):ℕ))⁻¹*(Real.sqrt (p.2:ℝ))⁻¹
  have hweight {n : ℕ} {f : Fin (order+1) → ℕ}
      (hf : f ∈ Nat.finMulAntidiag (order+1) n) :
      weight (split ⟨n,f⟩) = (Real.sqrt (n:ℝ))⁻¹ := by
    have hp : f 0*(∏ i : Fin order,f i.succ) = n := by
      simpa only [Fin.prod_univ_succ] using Nat.prod_eq_of_mem_finMulAntidiag hf
    dsimp [weight,split]
    rw [← mul_inv_rev,← Real.sqrt_mul (Nat.cast_nonneg (f 0)),← Nat.cast_mul,hp]
  have hmaps : source.image split ⊆ target := by
    intro q hq
    obtain ⟨⟨n,f⟩,hp,rfl⟩ := mem_image.mp hq
    obtain ⟨hn,hf⟩ := mem_sigma.mp hp
    apply mem_sigma.mpr
    refine ⟨?_,?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_finMulAntidiag hf i.succ),
        (Nat.le_of_dvd ((mem_Icc.mp hn).1) (Nat.dvd_of_mem_finMulAntidiag hf i.succ)).trans
          (mem_Icc.mp hn).2⟩
    · apply mem_Icc.mpr
      refine ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_finMulAntidiag hf 0),?_⟩
      have hP : 0 < ∏ i : Fin order,f i.succ := Nat.pos_of_ne_zero
        (Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.ne_zero_of_mem_finMulAntidiag hf i.succ))
      apply (Nat.le_div_iff_mul_le hP).mpr
      have hprod : f 0*(∏ i : Fin order,f i.succ) = n := by
        simpa only [Fin.prod_univ_succ] using Nat.prod_eq_of_mem_finMulAntidiag hf
      exact hprod.trans_le (mem_Icc.mp hn).2
  have hinj : Set.InjOn split source := by
    intro x hx y hy hxy
    have hhead : x.2 0 = y.2 0 := congrArg (fun q : Σ f : Fin order → ℕ,ℕ => q.2) hxy
    have htail : (fun i : Fin order => x.2 i.succ) = (fun i : Fin order => y.2 i.succ) :=
      congrArg (fun q : Σ f : Fin order → ℕ,ℕ => q.1) hxy
    have hf : x.2 = y.2 := by
      funext i
      exact Fin.cases hhead (fun j => congrFun htail j) i
    have hpx := Nat.prod_eq_of_mem_finMulAntidiag (mem_sigma.mp hx).2
    have hpy := Nat.prod_eq_of_mem_finMulAntidiag (mem_sigma.mp hy).2
    have hfst : x.1 = y.1 := hpx.symm.trans ((congrArg (fun f : Fin (order+1) → ℕ => ∏ i,f i) hf).trans hpy)
    exact Sigma.ext hfst (heq_of_eq hf)
  have htarget : (∑ q ∈ target,weight q) ≤
      2*Real.sqrt (N:ℝ)*(∑ n ∈ Icc 1 N,(n:ℝ)⁻¹)^order := by
    change (∑ q ∈ box.sigma (fun f => Icc 1 (N/(∏ i,f i))),weight q) ≤ _
    rw [Finset.sum_sigma]
    calc _ = ∑ f ∈ box,(Real.sqrt ((∏ i,f i):ℕ))⁻¹*
        (∑ v ∈ Icc 1 (N/(∏ i,f i)),(Real.sqrt (v:ℝ))⁻¹) := by
          apply sum_congr rfl
          intro f hf
          dsimp [weight]
          exact (Finset.mul_sum _ _ _).symm
         _ ≤ ∑ f ∈ box,2*Real.sqrt (N:ℝ)*(∏ i,(f i:ℝ)⁻¹) := by
          apply sum_le_sum
          intro f hf
          have hpos : 0 < ∏ i,f i := Finset.prod_pos
            (fun i _ => (mem_Icc.mp (Fintype.mem_piFinset.mp hf i)).1)
          have hreal : (0:ℝ)<((∏ i,f i):ℕ) := by exact_mod_cast hpos
          have hsqrt : 0<Real.sqrt ((∏ i,f i):ℕ) := Real.sqrt_pos.mpr hreal
          have hpartial := inverse_sqrt_partial_sum_le (N/(∏ i,f i))
          have hquot : Real.sqrt (((N/(∏ i,f i)):ℕ):ℝ) ≤
              Real.sqrt ((N:ℝ)/((∏ i,f i):ℕ)) := Real.sqrt_le_sqrt Nat.cast_div_le
          calc _ ≤ (Real.sqrt ((∏ i,f i):ℕ))⁻¹*
              (2*Real.sqrt (((N/(∏ i,f i)):ℕ):ℝ)) :=
                mul_le_mul_of_nonneg_left hpartial (inv_nonneg.mpr (Real.sqrt_nonneg _))
               _ ≤ (Real.sqrt ((∏ i,f i):ℕ))⁻¹*
                 (2*Real.sqrt ((N:ℝ)/((∏ i,f i):ℕ))) :=
                   mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hquot (by norm_num))
                     (inv_nonneg.mpr (Real.sqrt_nonneg _))
               _ = 2*Real.sqrt (N:ℝ)*(((∏ i,f i):ℕ):ℝ)⁻¹ := by
                 rw [Real.sqrt_div (Nat.cast_nonneg N)]
                 field_simp [hsqrt.ne',hreal.ne']
                 rw [Real.sq_sqrt hreal.le]
                 ring
               _ = 2*Real.sqrt (N:ℝ)*(∏ i,(f i:ℝ)⁻¹) := by
                 rw [Finset.prod_inv_distrib,← Nat.cast_prod]
         _ = 2*Real.sqrt (N:ℝ)*(∑ n ∈ Icc 1 N,(n:ℝ)⁻¹)^order := by
          rw [← Finset.mul_sum]
          congr 1
          exact (Finset.sum_pow' (Icc 1 N) (fun n : ℕ => (n:ℝ)⁻¹) order).symm
  calc (∑ n ∈ Icc 1 N,(divisorCount (order+1) n : ℝ)/Real.sqrt (n:ℝ)) =
      ∑ p ∈ source,weight (split p) := by
        rw [Finset.sum_sigma]
        apply sum_congr rfl
        intro n hn
        rw [show (∑ f ∈ Nat.finMulAntidiag (order+1) n,weight (split ⟨n,f⟩)) =
            ∑ f ∈ Nat.finMulAntidiag (order+1) n,(Real.sqrt (n:ℝ))⁻¹ by
              apply sum_congr rfl; intro f hf; exact hweight hf]
        simp [divisorCount,div_eq_mul_inv]
       _ = ∑ q ∈ source.image split,weight q := (sum_image hinj).symm
       _ ≤ ∑ q ∈ target,weight q := sum_le_sum_of_subset_of_nonneg hmaps
         (fun q _ _ => mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
           (inv_nonneg.mpr (Real.sqrt_nonneg _)))
       _ ≤ _ := htarget

theorem divisor_count_sqrt_sum_le (order : ℕ) (horder : 0<order) (X : ℝ) (hX : 1≤X) :
    (∑ n ∈ Icc 1 ⌊X⌋₊,(divisorCount order n : ℝ)/Real.sqrt (n:ℝ)) ≤
      2*Real.sqrt X*(1+Real.log X)^(order-1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero horder.ne'
  have hH : (∑ n ∈ Icc 1 ⌊X⌋₊,(n:ℝ)⁻¹) ≤ 1+Real.log X := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
      using harmonic_floor_le_one_add_log X hX
  calc _ ≤ 2*Real.sqrt (⌊X⌋₊:ℝ)*(∑ n ∈ Icc 1 ⌊X⌋₊,(n:ℝ)⁻¹)^k :=
         divisor_count_sqrt_sum_succ_le k _
       _ ≤ 2*Real.sqrt X*(1+Real.log X)^(k+1-1) := by
         simp only [Nat.add_sub_cancel]
         gcongr
         · exact Nat.floor_le (by linarith)

end Zeta23.OPICA
