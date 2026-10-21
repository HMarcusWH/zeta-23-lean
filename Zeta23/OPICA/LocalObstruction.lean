import Zeta23.OPICA.LocalData

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Zeta23.OPICA

theorem simplePole_residue_limit {Source : Type*} (p : SimplePoleData Source) :
    Tendsto (fun z => (z - p.center) * p.field z) (𝓝[≠] p.center) (𝓝 p.residue) := by
  have heq : (fun z => (z - p.center) * p.field z) =ᶠ[𝓝[≠] p.center]
      fun z => p.residue + (z - p.center) * p.remainder z := by
    filter_upwards [p.field_eq, self_mem_nhdsWithin] with z hz hzc
    rw [hz]
    have hx : z - p.center ≠ 0 := sub_ne_zero.mpr hzc
    field_simp
  apply Tendsto.congr' heq.symm
  have hc : ContinuousAt
      (fun z : ℂ => p.residue + (z - p.center) * p.remainder z) p.center :=
    continuousAt_const.add
      ((continuousAt_id.sub continuousAt_const).mul p.remainder_analytic.continuousAt)
  simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

theorem unit_mul_simplePole_residue {Source : Type*}
    (p : SimplePoleData Source) (m : MultiplierOrderData p.center) (hk : m.order = 0) :
    Tendsto (fun z => (z - p.center) * (m.multiplier z * p.field z))
      (𝓝[≠] p.center) (𝓝 (m.unit p.center * p.residue)) := by
  have hm : Tendsto m.multiplier (𝓝[≠] p.center) (𝓝 (m.unit p.center)) := by
    have hv := multiplier_center_value m
    simp only [hk, pow_zero, one_mul] at hv
    simpa only [hv] using (multiplier_analytic m).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  convert hm.mul (simplePole_residue_limit p) using 1
  ext z
  ring

private theorem iteratedDeriv_mul_leading {g h : ℂ → ℂ} {z : ℂ} (k : ℕ)
    (hg : AnalyticAt ℂ g z) (hh : AnalyticAt ℂ h z)
    (hzero : ∀ j < k, iteratedDeriv j h z = 0) :
    iteratedDeriv k (fun q => g q * h q) z = g z * iteratedDeriv k h z := by
  rw [iteratedDeriv_fun_mul hg.contDiffAt hh.contDiffAt, Finset.sum_eq_single 0]
  · simp only [Nat.choose_zero_right, Nat.cast_one, iteratedDeriv_zero, one_mul, tsub_zero]
  · intro j hj hjne
    have hjle := Finset.mem_range.mp hj
    rw [hzero (k - j) (by omega), mul_zero]
  · simp

theorem completion_regularRepresentative_analytic {Source : Type*}
    (p : SimplePoleData Source) (m : MultiplierOrderData p.center) :
    AnalyticAt ℂ (p.regularRepresentative m) p.center := by
  exact ((analyticAt_id.sub analyticAt_const).pow (m.order - 1)).mul
    (m.unit_analytic.mul (analyticAt_const.add
      ((analyticAt_id.sub analyticAt_const).mul p.remainder_analytic)))

theorem completion_order {Source : Type*}
    (p : SimplePoleData Source) (m : MultiplierOrderData p.center) :
    analyticOrderAt (p.regularRepresentative m) p.center = (m.order - 1 : ℕ) := by
  apply (completion_regularRepresentative_analytic p m).analyticOrderAt_eq_natCast.mpr
  refine ⟨fun z => m.unit z * (p.residue + (z - p.center) * p.remainder z),
    m.unit_analytic.mul (analyticAt_const.add
      ((analyticAt_id.sub analyticAt_const).mul p.remainder_analytic)), ?_, ?_⟩
  · simpa using mul_ne_zero m.unit_ne_zero p.residue_ne_zero
  · exact Filter.Eventually.of_forall (fun _ => rfl)

theorem completion_lower_derivatives {Source : Type*}
    (p : SimplePoleData Source) (m : MultiplierOrderData p.center)
    (j : ℕ) (hj : j < m.order - 1) :
    iteratedDeriv j (p.regularRepresentative m) p.center = 0 :=
  ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (completion_regularRepresentative_analytic p m)).mp (completion_order p m)).1 j hj

theorem completion_leading_jet {Source : Type*}
    (p : SimplePoleData Source) (m : MultiplierOrderData p.center) :
    iteratedDeriv (m.order - 1) (p.regularRepresentative m) p.center =
      (m.order - 1).factorial * m.unit p.center * p.residue := by
  let h : ℂ → ℂ := fun z => (z - p.center) ^ (m.order - 1)
  let g : ℂ → ℂ := fun z => m.unit z *
    (p.residue + (z - p.center) * p.remainder z)
  have hh : AnalyticAt ℂ h p.center := by fun_prop
  have hg : AnalyticAt ℂ g p.center := m.unit_analytic.mul
    (analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul p.remainder_analytic))
  have hd (n : ℕ) : iteratedDeriv n h p.center =
      if n = m.order - 1 then ((m.order - 1).factorial : ℂ) else 0 := by
    simpa [h] using congrFun
      (iteratedDeriv_comp_sub_const n (fun z : ℂ => z ^ (m.order - 1)) p.center) p.center
      |>.trans (by simpa using (iteratedDeriv_fun_pow_zero
        (𝕜 := ℂ) (n := n) (m := m.order - 1)))
  have heq : p.regularRepresentative m = fun z => g z * h z := by
    funext z
    exact mul_comm _ _
  rw [heq, iteratedDeriv_mul_leading _ hg hh]
  · rw [hd]
    simp [g]
    ring
  · intro j hj
    rw [hd, if_neg (Nat.ne_of_lt hj)]

theorem completion_leading_jet_ne_zero {Source : Type*}
    (p : SimplePoleData Source) (m : MultiplierOrderData p.center) :
    iteratedDeriv (m.order - 1) (p.regularRepresentative m) p.center ≠ 0 :=
  ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (completion_regularRepresentative_analytic p m)).mp (completion_order p m)).2

theorem completion_taylor_coefficient {Source : Type*}
    (p : SimplePoleData Source) (m : MultiplierOrderData p.center) :
    normalizedTaylorObservation (m.order - 1) (p.regularRepresentative m) p.center =
      m.unit p.center * p.residue := by
  have hfac : ((m.order - 1).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  dsimp only [normalizedTaylorObservation]
  apply (div_eq_iff hfac).mpr
  rw [completion_leading_jet]
  ring

theorem multiplier_residue_coordinate_ne_zero {Source : Type*}
    (p : SimplePoleData Source) (m : MultiplierOrderData p.center) :
    m.unit p.center * p.residue ≠ 0 := mul_ne_zero m.unit_ne_zero p.residue_ne_zero

theorem completion_agrees_punctured {Source : Type*}
    (p : SimplePoleData Source) (m : MultiplierOrderData p.center) (hk : 0 < m.order) :
    (fun z => m.multiplier z * p.field z) =ᶠ[𝓝[≠] p.center]
      p.regularRepresentative m := by
  have hne : ∀ᶠ z in 𝓝[≠] p.center, z ≠ p.center :=
    self_mem_nhdsWithin
  filter_upwards [p.field_eq, m.multiplier_eq.filter_mono nhdsWithin_le_nhds, hne]
    with z hz hm hzc
  rw [hz, hm]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simp only [SimplePoleData.regularRepresentative, hn, Nat.succ_sub_one, pow_succ]
  have hx : z - p.center ≠ 0 := sub_ne_zero.mpr hzc
  field_simp

def MultiplierOrderData.pow {center : ℂ} (m : MultiplierOrderData center) (p : ℕ) :
    MultiplierOrderData center where
  multiplier := fun z => m.multiplier z ^ p
  order := p * m.order
  unit := fun z => m.unit z ^ p
  unit_analytic := m.unit_analytic.pow p
  unit_ne_zero := pow_ne_zero _ m.unit_ne_zero
  multiplier_eq := by
    filter_upwards [m.multiplier_eq] with z hz
    simp only [hz, mul_pow, ← pow_mul]
    rw [Nat.mul_comm]

theorem iterated_completion_leading_jet {Source : Type*}
    (s : SimplePoleData Source) (m : MultiplierOrderData s.center)
    (p : ℕ) (_hp : 0 < p) (_hm : 0 < m.order) :
    analyticOrderAt (s.regularRepresentative (m.pow p)) s.center =
        (p * m.order - 1 : ℕ) ∧
      iteratedDeriv (p * m.order - 1) (s.regularRepresentative (m.pow p)) s.center =
        (p * m.order - 1).factorial * m.unit s.center ^ p * s.residue :=
  ⟨completion_order s (m.pow p), completion_leading_jet s (m.pow p)⟩

theorem double_completion_leibniz_factor {Source : Type*}
    (s : SimplePoleData Source) (m A : MultiplierOrderData s.center)
    (hm : 0 < m.order) (hA : A.order = m.order) :
    iteratedDeriv (2 * m.order - 1)
        (fun z => A.multiplier z * s.regularRepresentative m z) s.center =
      ((2 * m.order - 1).choose m.order : ℂ) *
        iteratedDeriv m.order A.multiplier s.center *
        iteratedDeriv (m.order - 1) (s.regularRepresentative m) s.center := by
  have hAzero := ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (multiplier_analytic A)).mp (multiplier_order A)).1
  rw [iteratedDeriv_fun_mul (multiplier_analytic A).contDiffAt
    (completion_regularRepresentative_analytic s m).contDiffAt,
    Finset.sum_eq_single m.order]
  · congr 2
    omega
  · intro j hj hjne
    by_cases hjlt : j < m.order
    · rw [hAzero j (by omega), mul_zero, zero_mul]
    · have hjle := Finset.mem_range.mp hj
      rw [completion_lower_derivatives s m (2 * m.order - 1 - j) (by omega), mul_zero]
  · intro hnot
    exfalso
    apply hnot
    simp only [Finset.mem_range]
    omega

theorem residual_congr_preserves_residue {Source : Type*}
    (s : SimplePoleData Source) (Z : MultiplierOrderData s.center)
    (hm : 0 < Z.order) (b : ℂ → ℂ) (hb : AnalyticAt ℂ b s.center) :
    Tendsto (fun z => (z - s.center) * ((1 + Z.multiplier z * b z) * s.field z))
      (𝓝[≠] s.center) (𝓝 s.residue) ∧
    (fun z => ((1 + Z.multiplier z * b z) * s.field z) - s.field z) =ᶠ[𝓝[≠] s.center]
      (fun z => b z * s.regularRepresentative Z z) := by
  have hz0 : Z.multiplier s.center = 0 := by
    rw [multiplier_center_value, zero_pow (Nat.ne_of_gt hm), zero_mul]
  constructor
  · have hc : ContinuousAt (fun z : ℂ => 1 + Z.multiplier z * b z) s.center :=
      continuousAt_const.add ((multiplier_analytic Z).continuousAt.mul hb.continuousAt)
    have ht' : Tendsto (fun z => 1 + Z.multiplier z * b z)
        (𝓝[≠] s.center) (𝓝 (1 : ℂ)) := by
      simpa [hz0] using hc.tendsto.mono_left nhdsWithin_le_nhds
    convert ht'.mul (simplePole_residue_limit s) using 1
    · ext z
      ring
    · simp
  · filter_upwards [completion_agrees_punctured s Z hm] with z hz
    rw [← hz]
    ring

theorem residual_correction_lower_derivatives {Source : Type*}
    (s : SimplePoleData Source) (Z : MultiplierOrderData s.center)
    (b : ℂ → ℂ) (hb : AnalyticAt ℂ b s.center) :
    AnalyticAt ℂ (fun z => b z * s.regularRepresentative Z z) s.center ∧
      ∀ j < Z.order - 1,
        iteratedDeriv j (fun z => b z * s.regularRepresentative Z z) s.center = 0 := by
  have ha := hb.mul (completion_regularRepresentative_analytic s Z)
  refine ⟨ha, ?_⟩
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha).mp
  apply (natCast_le_analyticOrderAt ha).mpr
  refine ⟨fun z => b z * (Z.unit z * (s.residue + (z - s.center) * s.remainder z)),
    hb.mul (Z.unit_analytic.mul (analyticAt_const.add
      ((analyticAt_id.sub analyticAt_const).mul s.remainder_analytic))), ?_⟩
  exact Filter.Eventually.of_forall (fun z => by
    dsimp [SimplePoleData.regularRepresentative]
    ring)

def finiteResidualCofactor (Z : ℂ → ℂ) (b : ℕ → ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => fun _ => 0
  | n + 1 => fun z => finiteResidualCofactor Z b n z + b n z +
      Z z * b n z * finiteResidualCofactor Z b n z

theorem finite_residual_products_congr_one (Z : ℂ → ℂ) (b : ℕ → ℂ → ℂ)
    (n : ℕ) (z : ℂ) :
    (∏ i ∈ Finset.range n, (1 + Z z * b i z)) = 1 + Z z * finiteResidualCofactor Z b n z := by
  induction n with
  | zero => simp [finiteResidualCofactor]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    dsimp [finiteResidualCofactor]
    ring

theorem finiteResidualCofactor_analytic (center : ℂ) (Z : ℂ → ℂ)
    (hZ : AnalyticAt ℂ Z center) (b : ℕ → ℂ → ℂ)
    (hb : ∀ i, AnalyticAt ℂ (b i) center) (n : ℕ) :
    AnalyticAt ℂ (finiteResidualCofactor Z b n) center := by
  induction n with
  | zero => exact analyticAt_const
  | succ n ih => exact (ih.add (hb n)).add ((hZ.mul (hb n)).mul ih)

theorem finite_residual_products_preserve_residue {Source : Type*}
    (s : SimplePoleData Source) (Z : MultiplierOrderData s.center)
    (hm : 0 < Z.order) (b : ℕ → ℂ → ℂ) (hb : ∀ i, AnalyticAt ℂ (b i) s.center)
    (n : ℕ) :
    Tendsto (fun z => (z - s.center) *
      ((∏ i ∈ Finset.range n, (1 + Z.multiplier z * b i z)) * s.field z))
      (𝓝[≠] s.center) (𝓝 s.residue) := by
  have hz0 : Z.multiplier s.center = 0 := by
    rw [multiplier_center_value, zero_pow (Nat.ne_of_gt hm), zero_mul]
  have hp : ContinuousAt (fun z => ∏ i ∈ Finset.range n, (1 + Z.multiplier z * b i z))
      s.center := by
    induction n with
    | zero => simpa using (continuousAt_const : ContinuousAt (fun _ : ℂ => (1 : ℂ)) s.center)
    | succ n ih =>
      simp only [Finset.prod_range_succ]
      exact ih.mul (continuousAt_const.add
        ((multiplier_analytic Z).continuousAt.mul (hb n).continuousAt))
  have ht : Tendsto (fun z => ∏ i ∈ Finset.range n, (1 + Z.multiplier z * b i z))
      (𝓝[≠] s.center) (𝓝 (1 : ℂ)) := by
    simpa [hz0] using hp.tendsto.mono_left nhdsWithin_le_nhds
  convert ht.mul (simplePole_residue_limit s) using 1
  · ext z
    ring
  · simp

theorem finite_residual_products_difference {Source : Type*}
    (s : SimplePoleData Source) (Z : MultiplierOrderData s.center)
    (hm : 0 < Z.order) (b : ℕ → ℂ → ℂ) (hb : ∀ i, AnalyticAt ℂ (b i) s.center)
    (n : ℕ) :
    (fun z => ((∏ i ∈ Finset.range n, (1 + Z.multiplier z * b i z)) * s.field z) -
        s.field z) =ᶠ[𝓝[≠] s.center]
      (fun z => finiteResidualCofactor Z.multiplier b n z * s.regularRepresentative Z z) ∧
      AnalyticAt ℂ
        (fun z => finiteResidualCofactor Z.multiplier b n z * s.regularRepresentative Z z)
        s.center ∧
      ∀ j < Z.order - 1, iteratedDeriv j
        (fun z => finiteResidualCofactor Z.multiplier b n z * s.regularRepresentative Z z)
        s.center = 0 := by
  have hc := finiteResidualCofactor_analytic s.center Z.multiplier (multiplier_analytic Z) b hb n
  refine ⟨?_, residual_correction_lower_derivatives s Z _ hc⟩
  simpa only [finite_residual_products_congr_one] using
    (residual_congr_preserves_residue s Z hm _ hc).2

theorem residual_power_preserves_residue {Source : Type*}
    (s : SimplePoleData Source) (Z : MultiplierOrderData s.center)
    (hm : 0 < Z.order) (b : ℂ → ℂ) (hb : AnalyticAt ℂ b s.center) (n : ℕ) :
    Tendsto (fun z => (z - s.center) * ((1 - Z.multiplier z * b z) ^ n * s.field z))
      (𝓝[≠] s.center) (𝓝 s.residue) := by
  simpa only [Finset.prod_const, Finset.card_range, mul_neg, ← sub_eq_add_neg] using
    finite_residual_products_preserve_residue s Z hm (fun _ z => -b z)
      (fun _ => hb.neg) n

end Zeta23.OPICA
