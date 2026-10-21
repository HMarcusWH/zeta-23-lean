import Zeta23.OPICA.PrimitiveMasks
import Zeta23.OPICA.EnergyRate
import Zeta23.OPICA.DivisorBounds
import Mathlib.Tactic

/-!
# Lawful regrouping of literal pair masks

The actual gcd regrouping gives the divisor-controlled A2 bound. The two
regrouped expansions may have different indices and sources; their low-mask
costs remain separate in the A3 consumer.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace Zeta23.OPICA

open Finset
open scoped BigOperators

private theorem abs_sub_le_add_abs (a b : ℝ) : |a-b|≤|a|+|b| := by
  simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le a 0 b)

theorem translatedDrive_abs_le (U : BoundedCausalDrive) (d : ℕ) (t : ℝ) :
    |translatedDrive U d t| ≤ U.bound/Real.sqrt (d:ℝ) := by
  rw [translatedDrive,abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right (U.abs_le _) (Real.sqrt_nonneg _)

theorem translatedDrive_zero_of_exp_lt (U : BoundedCausalDrive) {T t : ℝ}
    (ht : t≤T) {d : ℕ} (hd : Real.exp T<(d:ℝ)) : translatedDrive U d t=0 := by
  have hp : (0:ℝ)<d := (Real.exp_pos T).trans hd
  have hlog : T<Real.log d := (Real.lt_log_iff_exp_lt hp).mpr hd
  rw [translatedDrive,U.zero_before _ (by linarith [U.gap_pos]),zero_div]

theorem primitiveRatio_eq_reduced_max {d e : ℕ} (hd : 0<d) (he : 0<e) :
    primitiveRatio d e = (max (d/Nat.gcd d e) (e/Nat.gcd d e):ℕ) := by
  let g := Nat.gcd d e
  have hg : 0<g := Nat.gcd_pos_of_pos_left e hd
  have hd' : g*(d/g)=d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)
  have he' : g*(e/g)=e := Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)
  have hm : max d e = g*max (d/g) (e/g) := by
    rw [mul_max,hd',he']
  rw [primitiveRatio,hm,Nat.cast_mul]
  change ((g:ℝ)*(max (d/g) (e/g):ℕ))/(g:ℝ) = _
  field_simp [show (g:ℝ)≠0 by exact_mod_cast hg.ne']
  rfl

def positiveLowPairs (N : ℕ) (B : ℝ) : Finset (ℕ×ℕ) :=
  ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun de => primitiveRatio de.1 de.2≤B)

def gcdParameters (de : ℕ×ℕ) : ℕ×(ℕ×ℕ) :=
  (Nat.gcd de.1 de.2,(de.1/Nat.gcd de.1 de.2,de.2/Nat.gcd de.1 de.2))

theorem gcdParameters_injective : Function.Injective gcdParameters := by
  intro de ef h
  apply Prod.ext
  · have h' := congrArg (fun p : ℕ×(ℕ×ℕ) => p.1*p.2.1) h
    simpa [gcdParameters,Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)] using h'
  · have h' := congrArg (fun p : ℕ×(ℕ×ℕ) => p.1*p.2.2) h
    simpa [gcdParameters,Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)] using h'

theorem gcdParameters_low_mem {N : ℕ} {B : ℝ} {de : ℕ×ℕ}
    (hde : de∈positiveLowPairs N B) :
    gcdParameters de ∈ (Finset.Icc 1 N) ×ˢ ((Finset.Icc 1 ⌊B⌋₊) ×ˢ (Finset.Icc 1 ⌊B⌋₊)) := by
  unfold positiveLowPairs at hde
  dsimp only [gcdParameters]
  obtain ⟨hpair,hmask⟩ := mem_filter.mp hde
  obtain ⟨hd,he⟩ := Finset.mem_product.mp hpair
  have hdp : 0<de.1 := (Finset.mem_Icc.mp hd).1
  have hep : 0<de.2 := (Finset.mem_Icc.mp he).1
  have hg : 0<Nat.gcd de.1 de.2 := Nat.gcd_pos_of_pos_left _ hdp
  have hgled : Nat.gcd de.1 de.2≤de.1 := Nat.le_of_dvd hdp (Nat.gcd_dvd_left _ _)
  have hglee : Nat.gcd de.1 de.2≤de.2 := Nat.le_of_dvd hep (Nat.gcd_dvd_right _ _)
  have hratio := primitiveRatio_eq_reduced_max hdp hep
  have hmax : (max (de.1/Nat.gcd de.1 de.2) (de.2/Nat.gcd de.1 de.2):ℕ)≤B := by
    rwa [hratio] at hmask
  have haB : (((de.1/Nat.gcd de.1 de.2):ℕ):ℝ)≤B := by
    have hle : (((de.1/Nat.gcd de.1 de.2):ℕ):ℝ)≤
        ((max (de.1/Nat.gcd de.1 de.2) (de.2/Nat.gcd de.1 de.2):ℕ):ℝ) := by
      exact_mod_cast le_max_left (de.1/Nat.gcd de.1 de.2) (de.2/Nat.gcd de.1 de.2)
    exact hle.trans hmax
  have hbB : (((de.2/Nat.gcd de.1 de.2):ℕ):ℝ)≤B := by
    have hle : (((de.2/Nat.gcd de.1 de.2):ℕ):ℝ)≤
        ((max (de.1/Nat.gcd de.1 de.2) (de.2/Nat.gcd de.1 de.2):ℕ):ℝ) := by
      exact_mod_cast le_max_right (de.1/Nat.gcd de.1 de.2) (de.2/Nat.gcd de.1 de.2)
    exact hle.trans hmax
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hg,hgled.trans (Finset.mem_Icc.mp hd).2⟩,
    Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.div_pos hgled hg,Nat.le_floor haB⟩,
      Finset.mem_Icc.mpr ⟨Nat.div_pos hglee hg,Nat.le_floor hbB⟩⟩⟩

def divisorPairWeight (order : ℕ) (de : ℕ×ℕ) : ℝ :=
  ((divisorCount order de.1:ℝ)/Real.sqrt (de.1:ℝ))*
    ((divisorCount order de.2:ℝ)/Real.sqrt (de.2:ℝ))

def gcdWeight (order : ℕ) (p : ℕ×(ℕ×ℕ)) : ℝ :=
  ((divisorCount order p.1:ℝ)^2/(p.1:ℝ))*
    ((divisorCount order p.2.1:ℝ)/Real.sqrt (p.2.1:ℝ))*
      ((divisorCount order p.2.2:ℝ)/Real.sqrt (p.2.2:ℝ))

theorem divisorPairWeight_le_gcdWeight (order : ℕ) {d e : ℕ} (hd : 0<d) (he : 0<e) :
    divisorPairWeight order (d,e) ≤ gcdWeight order (gcdParameters (d,e)) := by
  let g := Nat.gcd d e
  let a := d/g
  let b := e/g
  have hg : 0<g := Nat.gcd_pos_of_pos_left e hd
  have ha : 0<a := Nat.div_pos (Nat.le_of_dvd hd (Nat.gcd_dvd_left _ _)) hg
  have hb : 0<b := Nat.div_pos (Nat.le_of_dvd he (Nat.gcd_dvd_right _ _)) hg
  have hd' : g*a=d := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have he' : g*b=e := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hDd : (divisorCount order d:ℝ) ≤ (divisorCount order g:ℝ)*(divisorCount order a:ℝ) := by
    rw [← hd']
    exact_mod_cast divisor_count_submultiplicative order g a hg ha
  have hDe : (divisorCount order e:ℝ) ≤ (divisorCount order g:ℝ)*(divisorCount order b:ℝ) := by
    rw [← he']
    exact_mod_cast divisor_count_submultiplicative order g b hg hb
  have hsd : Real.sqrt (d:ℝ)=Real.sqrt (g:ℝ)*Real.sqrt (a:ℝ) := by
    rw [← hd',Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg g)]
  have hse : Real.sqrt (e:ℝ)=Real.sqrt (g:ℝ)*Real.sqrt (b:ℝ) := by
    rw [← he',Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg g)]
  have h1 : (divisorCount order d:ℝ)/Real.sqrt (d:ℝ) ≤
      ((divisorCount order g:ℝ)*(divisorCount order a:ℝ))/(Real.sqrt (g:ℝ)*Real.sqrt (a:ℝ)) := by
    rw [hsd]
    exact div_le_div_of_nonneg_right hDd (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have h2 : (divisorCount order e:ℝ)/Real.sqrt (e:ℝ) ≤
      ((divisorCount order g:ℝ)*(divisorCount order b:ℝ))/(Real.sqrt (g:ℝ)*Real.sqrt (b:ℝ)) := by
    rw [hse]
    exact div_le_div_of_nonneg_right hDe (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hp := mul_le_mul h1 h2
    (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  change divisorPairWeight order (d,e) ≤ _ at hp
  apply hp.trans_eq
  change _ = ((divisorCount order g:ℝ)^2/(g:ℝ))*
    ((divisorCount order a:ℝ)/Real.sqrt (a:ℝ))*((divisorCount order b:ℝ)/Real.sqrt (b:ℝ))
  have hsg : Real.sqrt (g:ℝ)≠0 := (Real.sqrt_pos.mpr (by exact_mod_cast hg)).ne'
  have hsa : Real.sqrt (a:ℝ)≠0 := (Real.sqrt_pos.mpr (by exact_mod_cast ha)).ne'
  have hsb : Real.sqrt (b:ℝ)≠0 := (Real.sqrt_pos.mpr (by exact_mod_cast hb)).ne'
  calc _ = ((divisorCount order g:ℝ)^2/(Real.sqrt (g:ℝ))^2)*
      ((divisorCount order a:ℝ)/Real.sqrt (a:ℝ))*((divisorCount order b:ℝ)/Real.sqrt (b:ℝ)) := by
        field_simp [hsg,hsa,hsb]
        <;> ring
       _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg g)]

theorem divisor_low_sum_le (order : ℕ) (horder : 0<order) (X B : ℝ)
    (hX : 1≤X) (hB : 1≤B) :
    (∑ de ∈ positiveLowPairs ⌊X⌋₊ B,divisorPairWeight order de) ≤
      4*B*(1+Real.log B)^(2*order-2)*(1+Real.log X)^(order*order) := by
  classical
  let source := positiveLowPairs ⌊X⌋₊ B
  let target := (Finset.Icc 1 ⌊X⌋₊) ×ˢ ((Finset.Icc 1 ⌊B⌋₊) ×ˢ (Finset.Icc 1 ⌊B⌋₊))
  have himage : source.image gcdParameters ⊆ target := by
    intro p hp
    obtain ⟨de,hde,rfl⟩ := mem_image.mp hp
    exact gcdParameters_low_mem hde
  have hweight : ∀ p,0≤gcdWeight order p := by
    intro p
    exact mul_nonneg (mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)))
      (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
  have hsum : (∑ de ∈ source,divisorPairWeight order de) ≤ ∑ p ∈ target,gcdWeight order p := by
    calc _ ≤ ∑ de ∈ source,gcdWeight order (gcdParameters de) := by
          apply sum_le_sum
          intro de hde
          change de ∈ positiveLowPairs ⌊X⌋₊ B at hde
          unfold positiveLowPairs at hde
          obtain ⟨hpair,_⟩ := mem_filter.mp hde
          obtain ⟨hd,he⟩ := Finset.mem_product.mp hpair
          exact divisorPairWeight_le_gcdWeight order (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
         _ = ∑ p ∈ source.image gcdParameters,gcdWeight order p :=
          (sum_image gcdParameters_injective.injOn).symm
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg himage (fun p _ _ => hweight p)
  have hfactor : (∑ p ∈ target,gcdWeight order p) =
      (∑ h ∈ Finset.Icc 1 ⌊X⌋₊,(divisorCount order h:ℝ)^2/(h:ℝ))*
        (∑ a ∈ Finset.Icc 1 ⌊B⌋₊,(divisorCount order a:ℝ)/Real.sqrt (a:ℝ))^2 := by
    simp only [target,gcdWeight,Finset.sum_product]
    rw [Finset.sum_mul]
    apply sum_congr rfl
    intro h hh
    simp only [pow_two]
    rw [Finset.sum_mul_sum,Finset.mul_sum]
    apply sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro b hb
    ring
  have hH := divisor_count_harmonic_sum_le order X hX
  have hS := divisor_count_sqrt_sum_le order horder B hB
  have hSnon : 0≤∑ a ∈ Finset.Icc 1 ⌊B⌋₊,(divisorCount order a:ℝ)/Real.sqrt (a:ℝ) :=
    sum_nonneg (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
  have hHnon : 0≤∑ h ∈ Finset.Icc 1 ⌊X⌋₊,(divisorCount order h:ℝ)^2/(h:ℝ) :=
    sum_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have hlog : 0≤1+Real.log X := by linarith [Real.log_nonneg hX]
  calc _ ≤ _ := hsum
       _ = _ := hfactor
       _ ≤ (1+Real.log X)^(order*order)*(2*Real.sqrt B*(1+Real.log B)^(order-1))^2 :=
         mul_le_mul hH (pow_le_pow_left₀ hSnon hS 2) (sq_nonneg _) (pow_nonneg hlog _)
       _ = _ := by
         rw [mul_pow,mul_pow,Real.sq_sqrt (by linarith : 0≤B),← pow_mul]
         have hexp : (order-1)*2=2*order-2 := by omega
         rw [hexp]
         ring

theorem finiteLowPair_positive_expansion (U : BoundedCausalDrive) (x y : ℕ→ℝ)
    (B : ℝ→ℝ) {T t : ℝ} (ht : t≤T) :
    finiteLowPair U (driveIndexBound T) x y B t =
      ∑ de ∈ positiveLowPairs ⌊Real.exp T⌋₊ (B t),
        (x de.1*translatedDrive U de.1 t)*(y de.2*translatedDrive U de.2 t) := by
  let S := Finset.Icc 1 ⌊Real.exp T⌋₊
  let R := Finset.range (driveIndexBound T+1)
  have hsub : S⊆R := by
    intro d hd
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le ((Finset.mem_Icc.mp hd).2.trans (Nat.floor_le_ceil _))
  have hzero : ∀ d∈R,d∉S→translatedDrive U d t=0 := by
    intro d hd hnot
    by_cases hz : d=0
    · simpa [hz] using translatedDrive_zero_index U t
    · have hgt : ⌊Real.exp T⌋₊<d := by
        have : ¬(1≤d ∧ d≤⌊Real.exp T⌋₊) := by simpa [S,Finset.mem_Icc] using hnot
        omega
      exact translatedDrive_zero_of_exp_lt U ht (Nat.lt_of_floor_lt hgt)
  have houter : finiteLowPair U (driveIndexBound T) x y B t =
      ∑ d∈S,∑ e∈R,lowPrimitiveMask (B t) d e*(x d*translatedDrive U d t)*
        (y e*translatedDrive U e t) := by
    unfold finiteLowPair
    exact (sum_subset hsub (fun d hd hn => by simp [hzero d hd hn])).symm
  rw [houter]
  have hinner : (∑ d∈S,∑ e∈R,lowPrimitiveMask (B t) d e*(x d*translatedDrive U d t)*
      (y e*translatedDrive U e t)) =
      ∑ d∈S,∑ e∈S,lowPrimitiveMask (B t) d e*(x d*translatedDrive U d t)*
        (y e*translatedDrive U e t) := by
    apply sum_congr rfl
    intro d hd
    exact (sum_subset hsub (fun e he hn => by simp [hzero e he hn])).symm
  rw [hinner]
  simp [positiveLowPairs,S,Finset.sum_filter,Finset.sum_product,lowPrimitiveMask,ite_mul]

theorem finiteLowPair_pointwise_bound (U : BoundedCausalDrive) (order : ℕ) (horder : 0<order)
    (x y : ℕ→ℝ) (Ax Ay Bmax : ℝ) (hAx : 0≤Ax) (hAy : 0≤Ay) (hBmax : 1≤Bmax)
    (hx : ∀ d,0<d→|x d|≤Ax*(divisorCount order d:ℝ))
    (hy : ∀ d,0<d→|y d|≤Ay*(divisorCount order d:ℝ))
    (B : ℝ→ℝ) {T t : ℝ} (hT : 0≤T) (ht : t≤T) (hB : B t≤Bmax) :
    |finiteLowPair U (driveIndexBound T) x y B t| ≤
      Ax*Ay*U.bound^2*(4*Bmax*(1+Real.log Bmax)^(2*order-2)*(1+T)^(order*order)) := by
  have hxfield {d : ℕ} (hd : 0<d) : |x d*translatedDrive U d t| ≤
      Ax*U.bound*((divisorCount order d:ℝ)/Real.sqrt (d:ℝ)) := by
    rw [abs_mul]
    have h := mul_le_mul (hx d hd) (translatedDrive_abs_le U d t)
      (abs_nonneg _) (mul_nonneg hAx (Nat.cast_nonneg _))
    exact h.trans_eq (by ring)
  have hyfield {d : ℕ} (hd : 0<d) : |y d*translatedDrive U d t| ≤
      Ay*U.bound*((divisorCount order d:ℝ)/Real.sqrt (d:ℝ)) := by
    rw [abs_mul]
    have h := mul_le_mul (hy d hd) (translatedDrive_abs_le U d t)
      (abs_nonneg _) (mul_nonneg hAy (Nat.cast_nonneg _))
    exact h.trans_eq (by ring)
  have hsub : positiveLowPairs ⌊Real.exp T⌋₊ (B t) ⊆ positiveLowPairs ⌊Real.exp T⌋₊ Bmax := by
    intro de hde
    unfold positiveLowPairs at hde ⊢
    obtain ⟨hp,hm⟩ := mem_filter.mp hde
    exact mem_filter.mpr ⟨hp,hm.trans hB⟩
  have hweight : ∀ de,0≤divisorPairWeight order de := by
    intro de
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
  rw [finiteLowPair_positive_expansion U x y B ht]
  calc _ ≤ ∑ de∈positiveLowPairs ⌊Real.exp T⌋₊ (B t),
      |(x de.1*translatedDrive U de.1 t)*(y de.2*translatedDrive U de.2 t)| := abs_sum_le_sum_abs _ _
       _ ≤ ∑ de∈positiveLowPairs ⌊Real.exp T⌋₊ (B t),
        Ax*Ay*U.bound^2*divisorPairWeight order de := by
         apply sum_le_sum
         intro de hde
         unfold positiveLowPairs at hde
         obtain ⟨hp,_⟩ := mem_filter.mp hde
         obtain ⟨hd,he⟩ := Finset.mem_product.mp hp
         rw [abs_mul]
         have h := mul_le_mul (hxfield (Finset.mem_Icc.mp hd).1) (hyfield (Finset.mem_Icc.mp he).1)
           (abs_nonneg _) (mul_nonneg (mul_nonneg hAx U.bound_nonneg)
             (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)))
         exact h.trans_eq (by dsimp [divisorPairWeight]; ring)
       _ = Ax*Ay*U.bound^2*(∑ de∈positiveLowPairs ⌊Real.exp T⌋₊ (B t),divisorPairWeight order de) :=
         (Finset.mul_sum _ _ _).symm
       _ ≤ Ax*Ay*U.bound^2*(∑ de∈positiveLowPairs ⌊Real.exp T⌋₊ Bmax,divisorPairWeight order de) :=
         mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub (fun de _ _ => hweight de))
           (mul_nonneg (mul_nonneg hAx hAy) (sq_nonneg _))
       _ ≤ _ := by
         have h := divisor_low_sum_le order horder (Real.exp T) Bmax
           (Real.one_le_exp_iff.mpr hT) hBmax
         rw [Real.log_exp] at h
         exact mul_le_mul_of_nonneg_left h (mul_nonneg (mul_nonneg hAx hAy) (sq_nonneg _))

theorem low_primitive_bilinear_bound (U : BoundedCausalDrive) (order : ℕ) (horder : 0<order)
    (x y : ℕ→ℝ) (Ax Ay Bmax H T : ℝ) (hAx : 0≤Ax) (hAy : 0≤Ay)
    (hBmax : 1≤Bmax) (hT : 0≤T) (hHT : H≤T)
    (hx : ∀ d,0<d→|x d|≤Ax*(divisorCount order d:ℝ))
    (hy : ∀ d,0<d→|y d|≤Ay*(divisorCount order d:ℝ))
    (B : ℝ→ℝ) (hB : ∀ t∈Icc H T,B t≤Bmax) :
    |∫ t in Icc H T,finiteLowPair U (driveIndexBound T) x y B t| ≤
      Ax*Ay*(4*(T-H)*U.bound^2*Bmax*(1+Real.log Bmax)^(2*order-2)*(1+T)^(order*order)) := by
  have h := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=Icc H T)
    (f:=finiteLowPair U (driveIndexBound T) x y B)
    (C:=Ax*Ay*U.bound^2*(4*Bmax*(1+Real.log Bmax)^(2*order-2)*(1+T)^(order*order)))
    isCompact_Icc.measure_lt_top (fun t ht => by
      simpa only [Real.norm_eq_abs] using
        finiteLowPair_pointwise_bound U order horder x y Ax Ay Bmax hAx hAy hBmax hx hy B hT ht.2 (hB t ht))
  have hvol : volume.real (Icc H T)=T-H := by simp [Measure.real,Real.volume_Icc,sub_nonneg.mpr hHT]
  rw [Real.norm_eq_abs,hvol] at h
  exact h.trans_eq (by ring)

theorem finiteDriveField_add (U : BoundedCausalDrive) (N : ℕ) (x y : ℕ→ℝ) (t : ℝ) :
    finiteDriveField U N (x+y) t = finiteDriveField U N x t+finiteDriveField U N y t := by
  simp [finiteDriveField,add_mul,Finset.sum_add_distrib]

theorem finiteDriveField_continuous (U : BoundedCausalDrive) (N : ℕ) (x : ℕ→ℝ) :
    Continuous (finiteDriveField U N x) := by
  apply continuous_finsetSum
  intro d hd
  exact continuous_const.mul ((U.continuous.comp (continuous_id.sub continuous_const)).div_const _)

theorem finiteLowPair_measurable (U : BoundedCausalDrive) (N : ℕ) (x y : ℕ→ℝ)
    (B : ℝ→ℝ) (hB : Measurable B) : Measurable (finiteLowPair U N x y B) := by
  unfold finiteLowPair
  apply Finset.measurable_sum
  intro d hd
  apply Finset.measurable_sum
  intro e he
  have hxd : Continuous (fun t =>x d*translatedDrive U d t) :=
    continuous_const.mul ((U.continuous.comp (continuous_id.sub continuous_const)).div_const _)
  have hye : Continuous (fun t =>y e*translatedDrive U e t) :=
    continuous_const.mul ((U.continuous.comp (continuous_id.sub continuous_const)).div_const _)
  exact ((lowPrimitiveMask_measurable hB d e).mul hxd.measurable).mul hye.measurable

theorem finiteLowPair_integrableOn (U : BoundedCausalDrive) (order : ℕ) (horder : 0<order)
    (x y : ℕ→ℝ) (Ax Ay Bmax H T : ℝ) (hAx : 0≤Ax) (hAy : 0≤Ay)
    (hBmax : 1≤Bmax) (hT : 0≤T)
    (hx : ∀ d,0<d→|x d|≤Ax*(divisorCount order d:ℝ))
    (hy : ∀ d,0<d→|y d|≤Ay*(divisorCount order d:ℝ))
    (B : ℝ→ℝ) (hBm : Measurable B) (hB : ∀ t∈Icc H T,B t≤Bmax) :
    IntegrableOn (finiteLowPair U (driveIndexBound T) x y B) (Icc H T) := by
  apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top
    (finiteLowPair_measurable U (driveIndexBound T) x y B hBm).aestronglyMeasurable
    (Ax*Ay*U.bound^2*(4*Bmax*(1+Real.log Bmax)^(2*order-2)*(1+T)^(order*order)))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simpa only [Real.norm_eq_abs] using
    finiteLowPair_pointwise_bound U order horder x y Ax Ay Bmax hAx hAy hBmax hx hy B hT ht.2 (hB t ht)

theorem finiteHighPair_integrableOn (U : BoundedCausalDrive) (N : ℕ) (x y : ℕ→ℝ)
    (B : ℝ→ℝ) (H T : ℝ)
    (hL : IntegrableOn (finiteLowPair U N x y B) (Icc H T)) :
    IntegrableOn (finiteHighPair U N x y B) (Icc H T) := by
  have htotal : IntegrableOn (fun t =>finiteDriveField U N x t*finiteDriveField U N y t) (Icc H T) :=
    ((finiteDriveField_continuous U N x).mul (finiteDriveField_continuous U N y)).integrableOn_Icc
  have heq : finiteHighPair U N x y B =
      (fun t =>finiteDriveField U N x t*finiteDriveField U N y t)-finiteLowPair U N x y B := by
    funext t
    have h := finite_pair_partition U N x y B t
    dsimp
    linarith
  rw [heq]
  exact htotal.sub hL

theorem finiteDriveField_positive_expansion (U : BoundedCausalDrive) (x : ℕ→ℝ)
    {T t : ℝ} (ht : t≤T) :
    finiteDriveField U (driveIndexBound T) x t =
      ∑ d∈Finset.Icc 1 ⌊Real.exp T⌋₊,x d*translatedDrive U d t := by
  have hsub : Finset.Icc 1 ⌊Real.exp T⌋₊⊆Finset.range (driveIndexBound T+1) := by
    intro d hd
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Finset.mem_Icc.mp hd).2.trans (Nat.floor_le_ceil _)))
  unfold finiteDriveField
  apply (sum_subset hsub _).symm
  intro d hd hnot
  by_cases hz : d=0
  · simp [hz,translatedDrive_zero_index]
  · have hgt : ⌊Real.exp T⌋₊<d := by
      have : ¬(1≤d ∧ d≤⌊Real.exp T⌋₊) := by simpa [Finset.mem_Icc] using hnot
      omega
    rw [translatedDrive_zero_of_exp_lt U ht (Nat.lt_of_floor_lt hgt),mul_zero]

theorem finiteDriveField_unit_coefficient_bound (U : BoundedCausalDrive) (v : ℕ→ℝ)
    (hv : ∀ d,0<d→|v d|≤1) {T t : ℝ} (ht : t≤T) :
    |finiteDriveField U (driveIndexBound T) v t| ≤ 2*U.bound*Real.exp (T/2) := by
  have hV := U.bound_nonneg
  have hsqrt : Real.sqrt (Real.exp T)=Real.exp (T/2) := by
    rw [show Real.exp T=(Real.exp (T/2))^2 by rw [pow_two,← Real.exp_add]; congr 1 <;> ring,
      Real.sqrt_sq (Real.exp_pos _).le]
  rw [finiteDriveField_positive_expansion U v ht]
  calc _ ≤ ∑ d∈Finset.Icc 1 ⌊Real.exp T⌋₊,|v d*translatedDrive U d t| := abs_sum_le_sum_abs _ _
       _ ≤ ∑ d∈Finset.Icc 1 ⌊Real.exp T⌋₊,U.bound*(Real.sqrt (d:ℝ))⁻¹ := by
         apply sum_le_sum
         intro d hd
         rw [abs_mul]
         have h := mul_le_mul (hv d (Finset.mem_Icc.mp hd).1) (translatedDrive_abs_le U d t)
           (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
         simpa [div_eq_mul_inv] using h
       _ = U.bound*(∑ d∈Finset.Icc 1 ⌊Real.exp T⌋₊,(Real.sqrt (d:ℝ))⁻¹) := (Finset.mul_sum _ _ _).symm
       _ ≤ U.bound*(2*Real.sqrt (⌊Real.exp T⌋₊:ℝ)) :=
         mul_le_mul_of_nonneg_left (inverse_sqrt_partial_sum_le _) U.bound_nonneg
       _ ≤ U.bound*(2*Real.sqrt (Real.exp T)) := by
         gcongr
         exact Nat.floor_le (Real.exp_pos _).le
       _ = _ := by rw [hsqrt]; ring

theorem window_integral_abs_le {f : ℝ→ℝ} (H T : ℝ) (hHT : H≤T) (C : ℝ)
    (hf : ∀ t∈Icc H T,|f t|≤C) : |∫ t in Icc H T,f t|≤(T-H)*C := by
  have h := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=Icc H T) (f:=f) (C:=C)
    isCompact_Icc.measure_lt_top (fun t ht => by simpa only [Real.norm_eq_abs] using hf t ht)
  have hvol : volume.real (Icc H T)=T-H := by simp [Measure.real,Real.volume_Icc,sub_nonneg.mpr hHT]
  rw [Real.norm_eq_abs,hvol] at h
  simpa only [mul_comm] using h

def lowMaskCost (U : BoundedCausalDrive) (order : ℕ) (Bmax H T : ℝ) : ℝ :=
  4*(T-H)*U.bound^2*Bmax*(1+Real.log Bmax)^(2*order-2)*(1+T)^(order*order)

theorem masked_typeI_mixed_bound (U : BoundedCausalDrive) (order : ℕ) (horder : 0<order)
    (s c : ℕ→ℝ) (A eI Bmax H T : ℝ) (hA : 0≤A) (heI : 0≤eI)
    (hBmax : 1≤Bmax) (hT : 0≤T) (hHT : H≤T)
    (hs : ∀ d,0<d→|s d|≤A*(divisorCount order d:ℝ))
    (hc : ∀ d,0<d→|c d|≤(divisorCount order d:ℝ))
    (hfull : ∀ d,0<d→|s d+c d|≤1)
    (herror : ∀ t∈Icc H T,|finiteDriveField U (driveIndexBound T) s t|≤eI)
    (B : ℝ→ℝ) (hB : ∀ t∈Icc H T,B t≤Bmax)
    (hL : IntegrableOn (finiteLowPair U (driveIndexBound T) s c B) (Icc H T))
    (hQ : IntegrableOn (finiteHighPair U (driveIndexBound T) s c B) (Icc H T)) :
    |∫ t in Icc H T,finiteHighPair U (driveIndexBound T) s c B t| ≤
      (T-H)*eI*(2*U.bound*Real.exp (T/2)+eI)+A*lowMaskCost U order Bmax H T := by
  have hF : ∀ t∈Icc H T,|finiteDriveField U (driveIndexBound T) (s+c) t|≤2*U.bound*Real.exp (T/2) := by
    intro t ht
    exact finiteDriveField_unit_coefficient_bound U (s+c) hfull ht.2
  have hC : ∀ t∈Icc H T,|finiteDriveField U (driveIndexBound T) c t|≤2*U.bound*Real.exp (T/2)+eI := by
    intro t ht
    have heq : finiteDriveField U (driveIndexBound T) c t =
        finiteDriveField U (driveIndexBound T) (s+c) t-finiteDriveField U (driveIndexBound T) s t := by
      rw [finiteDriveField_add]; ring
    rw [heq]
    exact (abs_sub_le_add_abs _ _).trans (add_le_add (hF t ht) (herror t ht))
  have hraw := window_integral_abs_le H T hHT (eI*(2*U.bound*Real.exp (T/2)+eI))
    (f:=fun t => finiteDriveField U (driveIndexBound T) s t*finiteDriveField U (driveIndexBound T) c t)
    (fun t ht => by
      rw [abs_mul]
      exact mul_le_mul (herror t ht) (hC t ht) (abs_nonneg _) heI)
  have hlow := low_primitive_bilinear_bound U order horder s c A 1 Bmax H T hA (by norm_num)
    hBmax hT hHT hs (by simpa using hc) B hB
  rw [integral_pair_partition U (driveIndexBound T) s c B (Icc H T) hL hQ]
  exact (abs_sub_le_add_abs _ _).trans ((add_le_add hraw hlow).trans_eq (by dsimp [lowMaskCost]; ring))

theorem masked_typeI_square_bound (U : BoundedCausalDrive) (order : ℕ) (horder : 0<order)
    (s : ℕ→ℝ) (A eI Bmax H T : ℝ) (hA : 0≤A) (heI : 0≤eI)
    (hBmax : 1≤Bmax) (hT : 0≤T) (hHT : H≤T)
    (hs : ∀ d,0<d→|s d|≤A*(divisorCount order d:ℝ))
    (herror : ∀ t∈Icc H T,|finiteDriveField U (driveIndexBound T) s t|≤eI)
    (B : ℝ→ℝ) (hB : ∀ t∈Icc H T,B t≤Bmax)
    (hL : IntegrableOn (finiteLowPair U (driveIndexBound T) s s B) (Icc H T))
    (hQ : IntegrableOn (finiteHighPair U (driveIndexBound T) s s B) (Icc H T)) :
    |∫ t in Icc H T,finiteHighPair U (driveIndexBound T) s s B t| ≤
      (T-H)*eI^2+A^2*lowMaskCost U order Bmax H T := by
  have hraw := window_integral_abs_le H T hHT (eI^2)
    (f:=fun t => finiteDriveField U (driveIndexBound T) s t*finiteDriveField U (driveIndexBound T) s t) (fun t ht => by
    rw [abs_mul,← pow_two]
    exact pow_le_pow_left₀ (abs_nonneg _) (herror t ht) 2)
  have hlow := low_primitive_bilinear_bound U order horder s s A A Bmax H T hA hA
    hBmax hT hHT hs hs B hB
  rw [integral_pair_partition U (driveIndexBound T) s s B (Icc H T) hL hQ]
  exact (abs_sub_le_add_abs _ _).trans ((add_le_add hraw hlow).trans_eq (by dsimp [lowMaskCost]; ring))

theorem balanced_energy_comparison (U : BoundedCausalDrive) (order : ℕ) (horder : 0<order)
    (s c : ℕ→ℝ) (eI Bmax H T : ℝ) (heI : 0≤eI)
    (hBmax : 1≤Bmax) (hT : 0≤T) (hHT : H≤T)
    (hc : ∀ d,0<d→|c d|≤(divisorCount order d:ℝ))
    (hfull : ∀ d,0<d→|s d+c d|≤1)
    (herror : ∀ t∈Icc H T,|finiteDriveField U (driveIndexBound T) s t|≤eI)
    (B : ℝ→ℝ) (hB : ∀ t∈Icc H T,B t≤Bmax)
    (hL : IntegrableOn (finiteLowPair U (driveIndexBound T) c c B) (Icc H T))
    (hQ : IntegrableOn (finiteHighPair U (driveIndexBound T) c c B) (Icc H T)) :
    |(∫ t in Icc H T,(finiteDriveField U (driveIndexBound T) (s+c) t)^2)-
      (∫ t in Icc H T,finiteHighPair U (driveIndexBound T) c c B t)| ≤
      lowMaskCost U order Bmax H T+4*(T-H)*eI*U.bound*Real.exp (T/2)+(T-H)*eI^2 := by
  have hV := U.bound_nonneg
  let F := finiteDriveField U (driveIndexBound T) (s+c)
  let E := finiteDriveField U (driveIndexBound T) s
  let C := finiteDriveField U (driveIndexBound T) c
  have hid : ∀ t,F t^2-C t^2=2*F t*E t-E t^2 := by
    intro t
    have h := finiteDriveField_add U (driveIndexBound T) s c t
    dsimp [F,E,C] at *
    rw [h]
    ring
  have hraw := window_integral_abs_le H T hHT (4*eI*U.bound*Real.exp (T/2)+eI^2)
    (f:=fun t => F t^2-C t^2) (fun t ht => by
      rw [hid t]
      have hF := finiteDriveField_unit_coefficient_bound U (s+c) hfull ht.2
      have he := herror t ht
      change |F t|≤2*U.bound*Real.exp (T/2) at hF
      change |E t|≤eI at he
      calc |2*F t*E t-E t^2| ≤ |2*F t*E t|+|E t^2| := abs_sub_le_add_abs _ _
           _ = 2 * |F t| * |E t| + |E t|^2 := by
             rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),abs_pow]
           _ ≤ 2*(2*U.bound*Real.exp (T/2))*eI+eI^2 := by
             gcongr
           _ = _ := by ring)
  have hlow := low_primitive_bilinear_bound U order horder c c 1 1 Bmax H T (by norm_num) (by norm_num)
    hBmax hT hHT (by simpa using hc) (by simpa using hc) B hB
  have hFint : IntegrableOn (fun t =>F t^2) (Icc H T) :=
    ((finiteDriveField_continuous U (driveIndexBound T) (s+c)).pow 2).integrableOn_Icc
  have hCint : IntegrableOn (fun t =>C t^2) (Icc H T) :=
    ((finiteDriveField_continuous U (driveIndexBound T) c).pow 2).integrableOn_Icc
  have hpart := integral_pair_partition U (driveIndexBound T) c c B (Icc H T) hL hQ
  have heq : (∫ t in Icc H T,F t^2)-(∫ t in Icc H T,finiteHighPair U (driveIndexBound T) c c B t) =
      (∫ t in Icc H T,(F t^2-C t^2))+(∫ t in Icc H T,finiteLowPair U (driveIndexBound T) c c B t) := by
    rw [integral_sub hFint hCint,hpart]
    dsimp [C]
    simp only [pow_two]
    ring
  change |(∫ t in Icc H T,F t^2)-_|≤_
  rw [heq]
  exact (abs_add_le _ _).trans ((add_le_add hraw hlow).trans_eq (by dsimp [lowMaskCost]; ring))

def lowPairObservation (U : BoundedCausalDrive) (N : ℕ) (x : ℕ → ℝ)
    (B : ℝ → ℝ) (I : Set ℝ) : ℝ := ∫ t in I, finiteLowPair U N x x B t

def highPairObservation (U : BoundedCausalDrive) (N : ℕ) (x : ℕ → ℝ)
    (B : ℝ → ℝ) (I : Set ℝ) : ℝ := ∫ t in I, finiteHighPair U N x x B t

theorem mask_regrouping_difference
    (U V : BoundedCausalDrive) (N M : ℕ) (x y : ℕ → ℝ) (B C : ℝ → ℝ)
    (I : Set ℝ) (hI : MeasurableSet I)
    (hfield : ∀ t ∈ I, finiteDriveField U N x t = finiteDriveField V M y t)
    (hUL : IntegrableOn (finiteLowPair U N x x B) I)
    (hUH : IntegrableOn (finiteHighPair U N x x B) I)
    (hVL : IntegrableOn (finiteLowPair V M y y C) I)
    (hVH : IntegrableOn (finiteHighPair V M y y C) I) :
    highPairObservation U N x B I - highPairObservation V M y C I =
      lowPairObservation V M y C I - lowPairObservation U N x B I := by
  have htotal : (∫ t in I, finiteDriveField U N x t * finiteDriveField U N x t) =
      ∫ t in I, finiteDriveField V M y t * finiteDriveField V M y t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hI] with t ht
    rw [hfield t ht]
  unfold highPairObservation lowPairObservation
  rw [integral_pair_partition U N x x B I hUL hUH,
      integral_pair_partition V M y y C I hVL hVH, htotal]
  ring

theorem regrouped_mask_rate_congr
    (T : HorizonSchedule) (U V : BoundedCausalDrive) (N M : ℕ → ℕ)
    (x y : ℕ → ℕ → ℝ) (B C : ℕ → ℝ → ℝ) (H : ℕ → ℝ)
    (hfield : ∀ n t, t ∈ Icc (H n) (T.time n) →
      finiteDriveField U (N n) (x n) t = finiteDriveField V (M n) (y n) t)
    (hUL : ∀ n, IntegrableOn (finiteLowPair U (N n) (x n) (x n) (B n))
      (Icc (H n) (T.time n)))
    (hUH : ∀ n, IntegrableOn (finiteHighPair U (N n) (x n) (x n) (B n))
      (Icc (H n) (T.time n)))
    (hVL : ∀ n, IntegrableOn (finiteLowPair V (M n) (y n) (y n) (C n))
      (Icc (H n) (T.time n)))
    (hVH : ∀ n, IntegrableOn (finiteHighPair V (M n) (y n) (y n) (C n))
      (Icc (H n) (T.time n)))
    (hUbudget : SubexpAlong T (fun n =>
      lowPairObservation U (N n) (x n) (B n) (Icc (H n) (T.time n))))
    (hVbudget : SubexpAlong T (fun n =>
      lowPairObservation V (M n) (y n) (C n) (Icc (H n) (T.time n)))) :
    Tendsto (fun n =>
      magnitudeRate T (fun k => highPairObservation U (N k) (x k) (B k)
        (Icc (H k) (T.time k))) n -
      magnitudeRate T (fun k => highPairObservation V (M k) (y k) (C k)
        (Icc (H k) (T.time k))) n) atTop (𝓝 0) ∧
    Tendsto (fun n =>
      positiveRate T (fun k => highPairObservation U (N k) (x k) (B k)
        (Icc (H k) (T.time k))) n -
      positiveRate T (fun k => highPairObservation V (M k) (y k) (C k)
        (Icc (H k) (T.time k))) n) atTop (𝓝 0) := by
  have hneg := subexpAlong_const_smul T (-1 : ℝ) hUbudget
  have hsum := subexpAlong_add T hVbudget hneg
  have heq : (fun n =>
      highPairObservation U (N n) (x n) (B n) (Icc (H n) (T.time n)) -
      highPairObservation V (M n) (y n) (C n) (Icc (H n) (T.time n))) =
      (fun n => lowPairObservation V (M n) (y n) (C n) (Icc (H n) (T.time n))) +
      (-1 : ℝ) • (fun n => lowPairObservation U (N n) (x n) (B n)
        (Icc (H n) (T.time n))) := by
    funext n
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_one_mul, sub_eq_add_neg] using
      mask_regrouping_difference U V (N n) (M n) (x n) (y n) (B n) (C n)
        (Icc (H n) (T.time n)) measurableSet_Icc (hfield n)
        (hUL n) (hUH n) (hVL n) (hVH n)
  rw [← heq] at hsum
  exact ⟨rate_congr_of_subexp_error T _ _ hsum, posRate_congr_of_subexp_error T _ _ hsum⟩

end Zeta23.OPICA
