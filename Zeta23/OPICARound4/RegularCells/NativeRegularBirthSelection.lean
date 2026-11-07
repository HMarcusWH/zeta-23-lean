import Zeta23.OPICARound4.RegularCells.NativeZeroRegularity
import Zeta23.OPICARound4.CommonQuarticGround
import Mathlib.Topology.Algebra.Module.Cardinality

noncomputable section

namespace Zeta23.OPICARound4.RegularCells

open CCM OPICARound3 ExceptionalZero Complex Matrix Set Filter
open scoped BigOperators Topology

/-- A positive open aperture set contains a nonempty open piece of one actual source cell. -/
theorem exists_open_fixedCell_subset_positive {J : Set ℝ} (hJo : IsOpen J)
    (hJn : J.Nonempty) (hJp : J ⊆ Ioi 0) :
    ∃ (Q : ℕ) (U : Set ℝ), 1 ≤ Q ∧ IsOpen U ∧ U.Nonempty ∧ U ⊆ J ∧
      U ⊆ fixedCanonicalCutoffCell Q := by
  have hd : Dense ((Set.range (fun n : ℕ => Real.log (n : ℝ)))ᶜ) :=
    (Set.countable_range (fun n : ℕ => Real.log (n : ℝ))).dense_compl (𝕜 := ℝ)
  obtain ⟨L, hLJ, hLn⟩ := hd.inter_open_nonempty J hJo hJn
  have hLp : 0 < L := hJp hLJ
  let Q := ⌊Real.exp L⌋₊
  have hQ : 1 ≤ Q := by
    exact (Nat.le_floor_iff (Real.exp_nonneg L)).mpr (by simpa using Real.one_le_exp hLp.le)
  have hQp : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hQle : (Q : ℝ) ≤ Real.exp L := Nat.floor_le (Real.exp_nonneg L)
  have hQne : (Q : ℝ) ≠ Real.exp L := by
    intro he
    apply hLn
    refine ⟨Q, ?_⟩
    change Real.log (Q : ℝ) = L
    rw [he, Real.log_exp]
  have hLc : L ∈ fixedCanonicalCutoffCell Q := by
    constructor
    · exact (Real.log_lt_iff_lt_exp hQp).mpr (lt_of_le_of_ne hQle hQne)
    · apply (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < (Q + 1 : ℕ))).mpr
      exact_mod_cast Nat.lt_floor_add_one (Real.exp L)
  refine ⟨Q, J ∩ fixedCanonicalCutoffCell Q, hQ,
    hJo.inter (isOpen_fixedCanonicalCutoffCell Q), ⟨L,hLJ,hLc⟩,
    fun _ h => h.1, fun _ h => h.2⟩

/-- The finite native family is fixed before the aperture is selected. -/
theorem exists_finite_native_regular_in_open_positive
    (s : Finset (ReversalParity × ℕ)) {J : Set ℝ} (hJo : IsOpen J) (hJn : J.Nonempty)
    (hJp : J ⊆ Ioi 0) :
    ∃ L ∈ J, ∀ i ∈ s, Function.Bijective (nativePoleNeutralParityCanonical i.1 L i.2) := by
  obtain ⟨Q,U,hQ,hUo,hUn,hUJ,hUc⟩ := exists_open_fixedCell_subset_positive hJo hJn hJp
  obtain ⟨L,hLU,hLreg⟩ := exists_finite_native_regular_in_open_fixedCell hQ s hUo hUn hUc
  exact ⟨L,hUJ hLU,hLreg⟩

theorem exists_bounded_native_regular_in_open_positive (N : ℕ)
    {J : Set ℝ} (hJo : IsOpen J) (hJn : J.Nonempty) (hJp : J ⊆ Ioi 0) :
    ∃ L ∈ J, ∀ (p : ReversalParity) (K : ℕ), K ≤ N →
      Function.Bijective (nativePoleNeutralParityCanonical p L K) := by
  classical
  let s := ({ReversalParity.even, ReversalParity.odd} : Finset ReversalParity).product (Finset.range (N+1))
  obtain ⟨L,hLJ,hLreg⟩ := exists_finite_native_regular_in_open_positive s hJo hJn hJp
  refine ⟨L,hLJ,?_⟩
  intro p K hK
  apply hLreg (p,K)
  change (p,K) ∈ ({ReversalParity.even, ReversalParity.odd} : Finset ReversalParity).product
    (Finset.range (N+1))
  exact Finset.mem_product.mpr ⟨by cases p <;> simp, Finset.mem_range.mpr (by omega)⟩

/-- Under an off-line zero, actual both-parity negativity and all finite
zero-shift regularity up to the mandated detector coexist at arbitrarily late
apertures. This does not transfer a previously selected packet's depth. -/
theorem cofinally_both_negative_and_native_regular (ρ : zetaZeroConfig.carrier)
    (hoff : (ρ : ℂ).re ≠ 1/2) (R : ℝ) :
    ∃ L : ℝ, R < L ∧ 2 ≤ L ∧
      BothNeutralNegative L (originalDetectorQuarticCutoff L) ∧
      ∀ (p : ReversalParity) (K : ℕ), K ≤ originalDetectorQuarticCutoff L →
        Function.Bijective (nativePoleNeutralParityCanonical p L K) := by
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp (eventually_both_negative_at_original_quartic ρ hoff)
  let B := max (max R R0) 2
  let N := Nat.ceil ((B+1)^4)
  have hB : 2 ≤ B := le_max_right _ _
  have hJp : Ioo B (B+1) ⊆ Ioi 0 := by
    intro L hL
    change 0 < L
    linarith [hL.1]
  obtain ⟨L,hLJ,hLreg⟩ := exists_bounded_native_regular_in_open_positive N
    isOpen_Ioo (Set.nonempty_Ioo.mpr (by linarith)) hJp
  have hR : R < L := (le_max_left R R0 |>.trans (le_max_left _ _)).trans_lt hLJ.1
  have hR0L : R0 ≤ L := (le_max_right R R0 |>.trans (le_max_left _ _)).trans hLJ.1.le
  obtain ⟨hL2,hboth⟩ := hR0 L hR0L
  have hcap : originalDetectorQuarticCutoff L ≤ N := by
    apply Nat.ceil_mono
    exact pow_le_pow_left₀ (by linarith) hLJ.2.le 4
  exact ⟨L,hR,hL2,hboth,fun p K hK => hLreg p K (hK.trans hcap)⟩

theorem cofinally_regular_first_common_births (ρ : zetaZeroConfig.carrier)
    (hoff : (ρ : ℂ).re ≠ 1/2) (R : ℝ) :
    ∃ (L : ℝ) (Ke Ko : ℕ), R < L ∧ 2 ≤ L ∧ 3 ≤ Ke ∧ 3 ≤ Ko ∧
      EvenNeutralNegative L Ke ∧ OddNeutralNegative L Ko ∧
      BothNeutralNegative L (max Ke Ko) ∧ max Ke Ko ≤ originalDetectorQuarticCutoff L ∧
      PoleNeutralParityPSD .even L (Ke-1) ∧ PoleNeutralParityPSD .odd L (Ko-1) ∧
      NeutralNewbornSchur .even L Ke ∧ NeutralNewbornSchur .odd L Ko ∧
      Function.Bijective (nativePoleNeutralParityCanonical .even L (Ke-1)) ∧
      Function.Bijective (nativePoleNeutralParityCanonical .odd L (Ko-1)) := by
  obtain ⟨L,hRL,hL,hboth,hreg⟩ := cofinally_both_negative_and_native_regular ρ hoff R
  obtain ⟨Ke,Ko,hKe,hKo,he,ho,hcommon,hcap,hpe,hpo,hse,hso⟩ :=
    first_common_cutoff_le_original_quartic hL hboth
  exact ⟨L,Ke,Ko,hRL,hL,hKe,hKo,he,ho,hcommon,hcap,hpe,hpo,hse,hso,
    hreg .even (Ke-1) (by omega), hreg .odd (Ko-1) (by omega)⟩

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  nativePoleNeutralParitySpace_normedAddCommGroup
  nativePoleNeutralParitySpace_innerProductSpace

/-- At a selected regular predecessor, the actual produced newborn witness
has the regular Schur realization. The resonant alternative is impossible
because its full predecessor kernel is zero. No parity tie is excluded. -/
theorem native_newborn_realization_regular_of_bijective
    {p : ReversalParity} {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness p L K hL)
    (hreg : Function.Bijective (nativePoleNeutralParityCanonical p L (K-1))) :
    let J := newbornCutoffInclusion p L K
    let T := nativePoleNeutralParityCanonical p L K
    ∃ hb : J.toLinearMap.adjoint (T s.e.val) ∈ (predecessorBlock J T).range,
      oneShellSchurScalar J T s.e hb < 0 ∧
      s.w = regularSchurWitness J T s.e hb ∧
      (inner ℂ (T s.w) s.w).re = oneShellSchurScalar J T s.e hb := by
  let J := newbornCutoffInclusion p L K
  let T := nativePoleNeutralParityCanonical p L K
  have hcomp : predecessorBlock J T = nativePoleNeutralParityCanonical p L (K-1) :=
    nativePoleNeutralParity_predecessor_compression_eq p hL (show K-1 ≤ K by omega)
  have hk : (predecessorBlock J T).ker = ⊥ := by
    rw [hcomp]
    exact LinearMap.ker_eq_bot.mpr hreg.1
  have hreal := s.realization
  change ((predecessorBlock J T).ker.starProjection (J.toLinearMap.adjoint (T s.e.val)) ≠ 0 ∧
    s.w = resonantSchurWitness J T s.e ∧ (inner ℂ (T s.w) s.w).re = -1) ∨
    (∃ hb : J.toLinearMap.adjoint (T s.e.val) ∈ (predecessorBlock J T).range,
      oneShellSchurScalar J T s.e hb < 0 ∧ s.w = regularSchurWitness J T s.e hb ∧
      (inner ℂ (T s.w) s.w).re = oneShellSchurScalar J T s.e hb) at hreal
  rcases hreal with hres | hregular
  · have hz : (predecessorBlock J T).ker.starProjection
        (J.toLinearMap.adjoint (T s.e.val)) = 0 := by simp [hk]
    exact False.elim (hres.1 hz)
  · exact hregular

end Zeta23.OPICARound4.RegularCells
