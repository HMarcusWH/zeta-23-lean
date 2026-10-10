import Zeta23.CCM.SourceParityExactInertia
import Zeta23.CCM.SourceFourierConvolution
import Zeta23.CCM.FiniteDictionary
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

namespace Zeta23.CCM

open Matrix Finset Module
open scoped BigOperators ComplexConjugate

/-!
# POST285 M72 (Step 110): source spectral flow on `(1/2, 1)`

At `ω = 1/2` the parity source forms are indefinite (exact inertia,
`SourceParityExactInertia.lean`), while `S_K(1) = 2I` is positive definite.  For
any subspace `V` of the centered coefficient space on which the half-aperture
source form has a negative vector, the minimum of the source form over the unit
sphere of `V` is continuous in `ω`, negative at `1/2` and positive at `1`.  Hence
there is `ω* ∈ (1/2, 1)` at which the source form is positive semidefinite on `V`
and **degenerate** on `V`: some nonzero `v ∈ V` is `sourceSesq ω*`-orthogonal to
all of `V`.

Instantiated on the even boundary-flat carrier (`K ≥ 3`) and on the odd
boundary-flat carrier (`K ≥ 2`).

Scope.  These are zeros of the elementary **source compression**, not zeta zeros,
and not zeros of the canonical operator.  Only the first passage is proved; the
count "at least as many passages as negative eigenvalues at `1/2`" is DERIVED
(continuous eigenvalue branches) and not formalized here.
-/

/-! ## Hermitian sesquilinear algebra of the source form -/

theorem conj_sourceEntry (ω : ℝ) (n m : ℤ) : conj (sourceEntry ω n m) = sourceEntry ω n m := by
  rw [sourceEntry_eq_cos_integral, Complex.conj_ofReal]

theorem sourceSesq_conj_symm (ω : ℝ) (N : ℕ) (u v : Fin (2 * N + 1) → ℂ) :
    conj (sourceSesq ω N u v) = sourceSesq ω N v u := by
  unfold sourceSesq
  rw [map_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [map_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [map_mul, map_mul, Complex.conj_conj, sourceMatrix_apply, sourceMatrix_apply,
    conj_sourceEntry, sourceEntry_symmetric]
  ring

theorem sourceSesq_smul_left (ω : ℝ) (N : ℕ) (c : ℂ) (u v : Fin (2 * N + 1) → ℂ) :
    sourceSesq ω N (c • u) v = conj c * sourceSesq ω N u v := by
  unfold sourceSesq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem sourceSesq_smul_right (ω : ℝ) (N : ℕ) (c : ℂ) (u v : Fin (2 * N + 1) → ℂ) :
    sourceSesq ω N u (c • v) = c * sourceSesq ω N u v := by
  unfold sourceSesq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [Pi.smul_apply, smul_eq_mul]
  ring

theorem re_quadraticForm_sourceMatrix_smul (ω : ℝ) (N : ℕ) (c : ℂ) (u : Fin (2 * N + 1) → ℂ) :
    (quadraticForm (sourceMatrix ω N) (c • u)).re =
      Complex.normSq c * (quadraticForm (sourceMatrix ω N) u).re := by
  rw [← sourceSesq_self, ← sourceSesq_self, sourceSesq_smul_left, sourceSesq_smul_right,
    ← mul_assoc, mul_comm (conj c) c, Complex.mul_conj, Complex.re_ofReal_mul]

/-- **Semidefinite kernel lemma.**  If the source form is positive semidefinite on
`V` and `Re B(v,v) = 0` for `v ∈ V`, then `v` is `B`-orthogonal to all of `V`. -/
theorem sourceSesq_eq_zero_of_psd {ω : ℝ} {N : ℕ} {V : Submodule ℂ (Fin (2 * N + 1) → ℂ)}
    (hpsd : ∀ x ∈ V, 0 ≤ (quadraticForm (sourceMatrix ω N) x).re)
    {v : Fin (2 * N + 1) → ℂ} (hv : v ∈ V) (hv0 : (quadraticForm (sourceMatrix ω N) v).re = 0)
    {w : Fin (2 * N + 1) → ℂ} (hw : w ∈ V) :
    sourceSesq ω N v w = 0 := by
  set b := sourceSesq ω N v w with hb
  set R := (sourceSesq ω N w w).re with hR
  have hexp : ∀ t : ℂ, sourceSesq ω N (v + t • w) (v + t • w) =
      sourceSesq ω N v v + t * b + conj t * conj b + (conj t * t) * sourceSesq ω N w w := by
    intro t
    rw [sourceSesq_add_left, sourceSesq_add_right, sourceSesq_add_right, sourceSesq_smul_left,
      sourceSesq_smul_left, sourceSesq_smul_right, sourceSesq_smul_right,
      sourceSesq_conj_symm ω N v w]
    ring
  -- test along `t = -s · conj b`
  have hkey : ∀ s : ℝ, 0 < s → Complex.normSq b * (s * R - 2) * s ≥ 0 := by
    intro s hs
    have hpos := hpsd (v + ((-(s : ℂ)) * conj b) • w) (V.add_mem hv (V.smul_mem _ hw))
    rw [← sourceSesq_self, hexp] at hpos
    have h1 : (-(s : ℂ)) * conj b * b = -((s * Complex.normSq b : ℝ) : ℂ) := by
      rw [mul_assoc, mul_comm (conj b) b, Complex.mul_conj]; push_cast; ring
    have h2 : conj ((-(s : ℂ)) * conj b) * conj b = -((s * Complex.normSq b : ℝ) : ℂ) := by
      rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj, mul_assoc, Complex.mul_conj]
      push_cast; ring
    have h3 : conj ((-(s : ℂ)) * conj b) * ((-(s : ℂ)) * conj b) =
        ((s ^ 2 * Complex.normSq b : ℝ) : ℂ) := by
      rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj]
      have : -(s : ℂ) * b * (-(s : ℂ) * conj b) = (s : ℂ) ^ 2 * (b * conj b) := by ring
      rw [this, Complex.mul_conj]; push_cast; ring
    rw [h1, h2, h3] at hpos
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.re_ofReal_mul] at hpos
    rw [sourceSesq_self, hv0, ← hR] at hpos
    nlinarith
  have hnb : Complex.normSq b = 0 := by
    by_contra hne
    have hnbpos : 0 < Complex.normSq b := lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hne)
    set s : ℝ := 1 / (|R| + 1) with hs
    have hspos : 0 < s := by positivity
    have hsR : s * R < 2 := by
      have h1 : s * R ≤ s * |R| := mul_le_mul_of_nonneg_left (le_abs_self R) hspos.le
      have h2 : s * |R| < 1 := by
        rw [hs, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
        linarith
      linarith
    have := hkey s hspos
    have : Complex.normSq b * (s * R - 2) * s < 0 := by
      have : Complex.normSq b * (s * R - 2) < 0 := mul_neg_of_pos_of_neg hnbpos (by linarith)
      exact mul_neg_of_neg_of_pos this hspos
    linarith
  exact Complex.normSq_eq_zero.mp hnb

/-! ## Joint continuity and the minimum over the unit sphere -/

theorem continuous_sourceEnergy_joint (N : ℕ) :
    Continuous (fun p : ℝ × (Fin (2 * N + 1) → ℂ) =>
      (quadraticForm (sourceMatrix p.1 N) p.2).re) := by
  unfold quadraticForm
  have hS : ∀ i j : Fin (2 * N + 1),
      Continuous (fun p : ℝ × (Fin (2 * N + 1) → ℂ) => sourceMatrix p.1 N i j) :=
    fun i j => (continuous_sourceMatrix_apply N i j).comp continuous_fst
  have hv : ∀ i : Fin (2 * N + 1),
      Continuous (fun p : ℝ × (Fin (2 * N + 1) → ℂ) => p.2 i) :=
    fun i => (continuous_apply i).comp continuous_snd
  apply Complex.continuous_re.comp
  apply continuous_finsetSum; intro i _
  apply continuous_finsetSum; intro j _
  exact ((Complex.continuous_conj.comp (hv i)).mul (hS i j)).mul (hv j)

theorem re_quadraticForm_sourceMatrix_one_pos (N : ℕ) {u : Fin (2 * N + 1) → ℂ} (hu : u ≠ 0) :
    0 < (quadraticForm (sourceMatrix 1 N) u).re := by
  rw [sourceMatrix_one]
  unfold quadraticForm
  have hdiag : ∀ i, (∑ j, conj (u i) *
      ((2 : ℂ) • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ)) i j * u j) =
      ((2 * Complex.normSq (u i) : ℝ) : ℂ) := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul]
      have h : conj (u i) * u i = (Complex.normSq (u i) : ℂ) := by
        rw [mul_comm, Complex.mul_conj]
      push_cast
      linear_combination 2 * h
    · intro j _ hji
      simp [Matrix.one_apply_ne (Ne.symm hji)]
    · intro h; exact absurd (Finset.mem_univ i) h
  simp only [hdiag, Complex.re_sum, Complex.ofReal_re]
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h; push Not at h; exact hu (funext h)
  apply Finset.sum_pos' (fun j _ => by have := Complex.normSq_nonneg (u j); positivity)
  exact ⟨i, Finset.mem_univ i, by have := Complex.normSq_pos.mpr hi; positivity⟩

/-- **M72 / Step 110 (first passage).**  If the half-aperture source form has a
negative vector in `V`, there is `ω* ∈ (1/2, 1)` at which the source form is positive
semidefinite on `V` and has a nonzero `V`-radical vector. -/
theorem exists_sourceDegenerate_of_half_neg (N : ℕ) (V : Submodule ℂ (Fin (2 * N + 1) → ℂ))
    {u₀ : Fin (2 * N + 1) → ℂ} (hu₀ : u₀ ∈ V)
    (hneg : (quadraticForm (sourceMatrix (1 / 2) N) u₀).re < 0) :
    ∃ ω ∈ Set.Ioo (1 / 2 : ℝ) 1,
      (∀ x ∈ V, 0 ≤ (quadraticForm (sourceMatrix ω N) x).re) ∧
      ∃ v ∈ V, v ≠ 0 ∧ ∀ w ∈ V, sourceSesq ω N v w = 0 := by
  obtain ⟨F, hF⟩ : ∃ F : ℝ → (Fin (2 * N + 1) → ℂ) → ℝ,
      F = fun ω x => (quadraticForm (sourceMatrix ω N) x).re := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : Set (Fin (2 * N + 1) → ℂ),
      S = (V : Set (Fin (2 * N + 1) → ℂ)) ∩ Metric.sphere 0 1 := ⟨_, rfl⟩
  have hFapp : ∀ ω x, F ω x = (quadraticForm (sourceMatrix ω N) x).re := by
    intro ω x; rw [hF]
  have hScpt : IsCompact S := by
    rw [hSdef]
    exact (isCompact_sphere 0 1).inter_left (Submodule.closed_of_finiteDimensional V)
  have hSmem : ∀ x, x ∈ S ↔ x ∈ V ∧ ‖x‖ = 1 := by
    intro x; rw [hSdef, Set.mem_inter_iff, mem_sphere_zero_iff_norm]; rfl
  have hu₀0 : u₀ ≠ 0 := by
    rintro rfl
    simp [quadraticForm] at hneg
  have hnorm0 : 0 < ‖u₀‖ := norm_pos_iff.mpr hu₀0
  set e₀ := ((‖u₀‖⁻¹ : ℝ) : ℂ) • u₀ with he₀
  have he₀S : e₀ ∈ S := by
    refine (hSmem _).mpr ⟨V.smul_mem _ hu₀, ?_⟩
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hnorm0), inv_mul_cancel₀ hnorm0.ne']
  have hSne : S.Nonempty := ⟨e₀, he₀S⟩
  have hFcont : Continuous (Function.uncurry F) := by
    rw [hF]; exact continuous_sourceEnergy_joint N
  have hFω : ∀ ω, Continuous (F ω) := fun ω =>
    hFcont.comp (Continuous.prodMk continuous_const continuous_id)
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun ω => sInf (F ω '' S) := ⟨_, rfl⟩
  have hgcont : Continuous g := by
    rw [hg]; exact hScpt.continuous_sInf hFcont
  have hbdd : ∀ ω, BddBelow (F ω '' S) := fun ω =>
    (hScpt.image (hFω ω)).bddBelow
  have hmem : ∀ ω, g ω ∈ F ω '' S := fun ω => by
    rw [hg]; exact (hScpt.image (hFω ω)).sInf_mem (hSne.image _)
  have hle : ∀ ω, ∀ x ∈ S, g ω ≤ F ω x := fun ω x hx => by
    rw [hg]; exact csInf_le (hbdd ω) (Set.mem_image_of_mem _ hx)
  -- sign at the endpoints
  have hg_half : g (1 / 2) < 0 := by
    refine lt_of_le_of_lt (hle _ e₀ he₀S) ?_
    rw [hFapp, he₀, re_quadraticForm_sourceMatrix_smul, Complex.normSq_ofReal]
    have : 0 < ‖u₀‖⁻¹ * ‖u₀‖⁻¹ := by positivity
    exact mul_neg_of_pos_of_neg this hneg
  have hg_one : 0 < g 1 := by
    obtain ⟨x, hxS, hx⟩ := hmem 1
    rw [← hx, hFapp]
    have hx0 : x ≠ 0 := by
      intro h
      have := ((hSmem x).mp hxS).2
      rw [h, norm_zero] at this
      exact zero_ne_one this
    exact re_quadraticForm_sourceMatrix_one_pos N hx0
  -- intermediate value
  obtain ⟨ω, hω, hgω⟩ : ∃ ω ∈ Set.Ioo (1 / 2 : ℝ) 1, g ω = 0 := by
    have := intermediate_value_Ioo (by norm_num : (1 / 2 : ℝ) ≤ 1) hgcont.continuousOn
    exact this ⟨hg_half, hg_one⟩
  refine ⟨ω, hω, ?_, ?_⟩
  · -- positive semidefinite
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0; simp [quadraticForm]
    have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hxS : ((‖x‖⁻¹ : ℝ) : ℂ) • x ∈ S := by
      refine (hSmem _).mpr ⟨V.smul_mem _ hx, ?_⟩
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hxn), inv_mul_cancel₀ hxn.ne']
    have h := hle ω _ hxS
    rw [hgω, hFapp, re_quadraticForm_sourceMatrix_smul, Complex.normSq_ofReal] at h
    have hpos : 0 < ‖x‖⁻¹ * ‖x‖⁻¹ := by positivity
    exact nonneg_of_mul_nonneg_right (by linarith) hpos
  · obtain ⟨v, hvS, hv⟩ := hmem ω
    rw [hgω, hFapp] at hv
    obtain ⟨hvV, hvn⟩ := (hSmem v).mp hvS
    have hv0 : v ≠ 0 := by
      intro h
      rw [h, norm_zero] at hvn
      exact zero_ne_one hvn
    refine ⟨v, hvV, hv0, fun w hw => ?_⟩
    have hpsd : ∀ x ∈ V, 0 ≤ (quadraticForm (sourceMatrix ω N) x).re := by
      intro x hx
      by_cases hx0 : x = 0
      · subst hx0; simp [quadraticForm]
      have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hxS : ((‖x‖⁻¹ : ℝ) : ℂ) • x ∈ S := by
        refine (hSmem _).mpr ⟨V.smul_mem _ hx, ?_⟩
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hxn), inv_mul_cancel₀ hxn.ne']
      have h := hle ω _ hxS
      rw [hgω, hFapp, re_quadraticForm_sourceMatrix_smul, Complex.normSq_ofReal] at h
      have hpos : 0 < ‖x‖⁻¹ * ‖x‖⁻¹ := by positivity
      exact nonneg_of_mul_nonneg_right (by linarith) hpos
    exact sourceSesq_eq_zero_of_psd hpsd hvV hv hw

/-- **M72 on the parity carriers.**  The odd boundary-flat source form degenerates
at some `ω ∈ (1/2, 1)` for every `K ≥ 2`; the even one for every `K ≥ 3`. -/
theorem parityBoundaryFlat_sourceDegenerate (K : ℕ) :
    (2 ≤ K → ∃ ω ∈ Set.Ioo (1 / 2 : ℝ) 1,
      (∀ x ∈ oddBoundaryFlatSubspace K, 0 ≤ (quadraticForm (sourceMatrix ω K) x).re) ∧
      ∃ v ∈ oddBoundaryFlatSubspace K, v ≠ 0 ∧
        ∀ w ∈ oddBoundaryFlatSubspace K, sourceSesq ω K v w = 0) ∧
    (3 ≤ K → ∃ ω ∈ Set.Ioo (1 / 2 : ℝ) 1,
      (∀ x ∈ evenBoundaryFlatSubspace K, 0 ≤ (quadraticForm (sourceMatrix ω K) x).re) ∧
      ∃ v ∈ evenBoundaryFlatSubspace K, v ≠ 0 ∧
        ∀ w ∈ evenBoundaryFlatSubspace K, sourceSesq ω K v w = 0) := by
  refine ⟨fun hK => ?_, fun hK => ?_⟩
  · obtain ⟨P, Nn, hsup, -, hNn, -, -, hneg, -⟩ := oddBoundaryFlat_sourceHalf_exactInertia K hK
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Submodule.one_le_finrank_iff.mp (by rw [hNn]; omega))
    exact exists_sourceDegenerate_of_half_neg K _ (hsup ▸ Submodule.mem_sup_right hu)
      (hneg u hu hu0)
  · obtain ⟨-, ⟨u, hu, hneg⟩, -⟩ := parityBoundaryFlat_sourceHalf_indefinite K hK
    exact exists_sourceDegenerate_of_half_neg K _ hu hneg

end Zeta23.CCM

#print axioms Zeta23.CCM.sourceSesq_conj_symm
#print axioms Zeta23.CCM.sourceSesq_eq_zero_of_psd
#print axioms Zeta23.CCM.continuous_sourceEnergy_joint
#print axioms Zeta23.CCM.exists_sourceDegenerate_of_half_neg
#print axioms Zeta23.CCM.parityBoundaryFlat_sourceDegenerate
