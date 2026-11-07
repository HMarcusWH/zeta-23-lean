import Zeta23.OPICARound4.RegularCells.FixedSeed
import Zeta23.CCM.LiftedPredecessorRegularity
import Zeta23.CCM.NativeDetectorSchur
import Zeta23.OPICARound4.RegularCells.AnalyticFiniteSelector

noncomputable section

namespace Zeta23.OPICARound4.RegularCells

open CCM Complex Matrix Set Filter
open scoped BigOperators ComplexConjugate Topology

/-- Polynomial fixed-seed diagonal, normalized only at the positive base aperture one. -/
def normalizedSeedEntry (K : ℕ) (w : ℂ) (i : Fin (2 * K + 1)) : ℂ :=
  ((w / (4 * (Real.pi : ℂ))) ^ 2 + (centeredIndex K i : ℂ) ^ 2) /
    (fixedSeedDiagonalEntry 1 K i : ℂ)

theorem normalizedSeedEntry_ofReal (K : ℕ) (L : ℝ) (i : Fin (2 * K + 1)) :
    normalizedSeedEntry K (L : ℂ) i =
      (fixedSeedDiagonalEntry L K i : ℂ) / (fixedSeedDiagonalEntry 1 K i : ℂ) := by
  simp [normalizedSeedEntry, fixedSeedDiagonalEntry, fixedSeedParameter]

@[simp] theorem normalizedSeedEntry_one (K : ℕ) (i : Fin (2 * K + 1)) :
    normalizedSeedEntry K 1 i = 1 := by
  have hi : (fixedSeedDiagonalEntry 1 K i : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (fixedSeedDiagonalEntry_pos (by norm_num) K i))
  simpa only [Complex.ofReal_one, div_self hi] using normalizedSeedEntry_ofReal K 1 i

/-- This is a holomorphic congruence frame, not a conjugated-variable adjoint. -/
def normalizedSeedMatrix (K : ℕ) (w : ℂ) : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  Matrix.diagonal (normalizedSeedEntry K w)

@[simp] theorem normalizedSeedMatrix_one (K : ℕ) : normalizedSeedMatrix K 1 = 1 := by
  ext i j
  simp [normalizedSeedMatrix, Matrix.diagonal_apply, Matrix.one_apply]

def liftedFullSource (Q K : ℕ) (z : ℂ) : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  (-z) • 1 + complexFrozenCanonicalSourceRemainder Q (Complex.exp z) K

def normalizedFrameSource (Q K : ℕ) (z : ℂ) : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  normalizedSeedMatrix K (Complex.exp z) * liftedFullSource Q K z *
    normalizedSeedMatrix K (Complex.exp z)

theorem normalizedFrameSource_apply (Q K : ℕ) (z : ℂ) (i j : Fin (2 * K + 1)) :
    normalizedFrameSource Q K z i j =
      normalizedSeedEntry K (Complex.exp z) i * liftedFullSource Q K z i j *
        normalizedSeedEntry K (Complex.exp z) j := by
  simp [normalizedFrameSource, normalizedSeedMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem analyticOnNhd_normalizedFrameSource_apply (Q K : ℕ) (i j : Fin (2 * K + 1)) :
    AnalyticOnNhd ℂ (fun z => normalizedFrameSource Q K z i j) liftedFrozenPredecessorDomain := by
  intro z hz
  have hentry (k : Fin (2 * K + 1)) :
      AnalyticAt ℂ (fun w => normalizedSeedEntry K (Complex.exp w) k) z := by
    unfold normalizedSeedEntry
    fun_prop
  have hsource : AnalyticAt ℂ (fun w => liftedFullSource Q K w i j) z := by
    have hrem := (analyticOnNhd_complexFrozenCanonicalSourceRemainder_apply_sourceDomain
      Q K i j (Complex.exp z) hz).comp analyticAt_cexp
    exact (analyticAt_id.neg.mul analyticAt_const).add hrem
  simpa [normalizedFrameSource_apply] using ((hentry i).fun_mul hsource).fun_mul (hentry j)

section Compression
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (K : ℕ) (J : E →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (2 * K + 1)))

/-- The complete moving physical Gram is retained in this congruence compression. -/
def liftedNativeFrame (Q : ℕ) (z : ℂ) : E →ₗ[ℂ] E :=
  J.toLinearMap.adjoint.comp ((normalizedFrameSource Q K z).toEuclideanLin.comp J.toLinearMap)

theorem analyticOnNhd_liftedNativeFrame_coord (Q : ℕ) (φ : E →ₗ[ℂ] ℂ) (x : E) :
    AnalyticOnNhd ℂ (fun z => φ (liftedNativeFrame K J Q z x)) liftedFrozenPredecessorDomain := by
  let c := φ.comp J.toLinearMap.adjoint
  have hsum (z : ℂ) : φ (liftedNativeFrame K J Q z x) =
      ∑ i : Fin (2 * K + 1), (∑ j : Fin (2 * K + 1),
        normalizedFrameSource Q K z i j * J x j) * c (EuclideanSpace.single i 1) := by
    have hvec : (normalizedFrameSource Q K z).toEuclideanLin (J x) =
        ∑ i : Fin (2 * K + 1), (∑ j : Fin (2 * K + 1),
          normalizedFrameSource Q K z i j * J x j) • EuclideanSpace.single i 1 := by
      rw [Matrix.toLpLin_apply]
      ext k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    change c ((normalizedFrameSource Q K z).toEuclideanLin (J x)) = _
    rw [hvec, map_sum]
    simp only [map_smul, smul_eq_mul]
  simp_rw [hsum]
  apply Finset.analyticOnNhd_fun_sum
  intro i _
  apply AnalyticOnNhd.mul _ analyticOnNhd_const
  apply Finset.analyticOnNhd_fun_sum
  intro j _
  exact (analyticOnNhd_normalizedFrameSource_apply Q K i j).mul analyticOnNhd_const

theorem liftedNativeFrame_deck_base (Q k : ℕ) :
    liftedNativeFrame K J Q ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) =
      liftedNativeFrame K J Q 0 -
        ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) • LinearMap.id := by
  have he : Complex.exp ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    rw [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
  have hf : normalizedFrameSource Q K ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) =
      normalizedFrameSource Q K 0 -
        ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) • 1 := by
    simp [normalizedFrameSource, liftedFullSource, he, sub_eq_add_neg, add_comm]
  unfold liftedNativeFrame
  rw [hf, map_sub, map_smul, Matrix.toLpLin_one]
  simp only [LinearMap.sub_comp, LinearMap.smul_comp, LinearMap.id_comp,
    LinearMap.comp_sub, LinearMap.comp_smul, J.adjoint_comp_self']

def liftedNativeFrameDet (Q : ℕ) (z : ℂ) : ℂ := LinearMap.det (liftedNativeFrame K J Q z)

theorem analyticOnNhd_liftedNativeFrameDet (Q : ℕ) :
    AnalyticOnNhd ℂ (liftedNativeFrameDet K J Q) liftedFrozenPredecessorDomain := by
  change AnalyticOnNhd ℂ (fun z => LinearMap.det (liftedNativeFrame K J Q z))
    liftedFrozenPredecessorDomain
  let b := Module.finBasis ℂ E
  have hm : AnalyticOnNhd ℂ
      (fun z => Matrix.det (LinearMap.toMatrix b b (liftedNativeFrame K J Q z)))
      liftedFrozenPredecessorDomain := by
    intro z hz
    simp_rw [Matrix.det_apply']
    apply Finset.analyticAt_fun_sum
    intro σ _
    apply analyticAt_const.mul
    apply Finset.analyticAt_fun_prod
    intro i _
    simpa [LinearMap.toMatrix_apply] using
      analyticOnNhd_liftedNativeFrame_coord K J Q (b.coord (σ i)) (b i) z hz
  simpa only [LinearMap.det_toMatrix] using hm

theorem exists_mem_corridor_liftedNativeFrameDet_ne_zero (Q : ℕ) :
    ∃ z ∈ liftedFrozenRigidityDomain, liftedNativeFrameDet K J Q z ≠ 0 := by
  have hc : (2 * (Real.pi : ℂ) * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  obtain ⟨k, hk⟩ := exists_nat_det_sub_smul_id_ne_zero (liftedNativeFrame K J Q 0) hc
  refine ⟨(k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I),
    nat_two_pi_I_mem_liftedFrozenRigidityDomain k, ?_⟩
  simpa only [liftedNativeFrameDet, liftedNativeFrame_deck_base] using hk

end Compression

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  nativePoleNeutralParitySpace_innerProductSpace nativePoleNeutralParitySpace_normedAddCommGroup

def nativeSeedAmbientIsometry (p : ReversalParity) (L : ℝ) (K : ℕ) :
    nativePoleNeutralParitySpace p L K →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (2 * K + 1)) := by
  cases p
  · exact (euclideanEvenBoundaryFlatSubspace K).subtypeₗᵢ.comp
      (poleNeutralEvenSubspace L K).subtypeₗᵢ
  · exact (euclideanOddBoundaryFlatSubspace K).subtypeₗᵢ.comp
      (poleNeutralOddSubspace L K).subtypeₗᵢ

def nativeSeedPhysicalTransport (p : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ) :
    nativePoleNeutralParitySpace p 1 K ≃ₗ[ℂ] nativePoleNeutralParitySpace p L K := by
  cases p
  · exact (fixedEvenSeedPhysicalEquiv (by norm_num) K).symm.trans
      (fixedEvenSeedPhysicalEquiv hL K)
  · exact (fixedOddSeedPhysicalEquiv (by norm_num) K).symm.trans
      (fixedOddSeedPhysicalEquiv hL K)

theorem normalizedSeedMatrix_physical_transport (p : ReversalParity) {L : ℝ}
    (hL : 0 < L) (K : ℕ) (u : nativePoleNeutralParitySpace p 1 K) :
    (normalizedSeedMatrix K (L : ℂ)).toEuclideanLin (nativeSeedAmbientIsometry p 1 K u) =
      nativeSeedAmbientIsometry p L K (nativeSeedPhysicalTransport p hL K u) := by
  cases p
  · let v := (fixedEvenSeedPhysicalEquiv (L := 1) (by norm_num) K).symm u
    have hv := (fixedEvenSeedPhysicalEquiv (L := 1) (by norm_num) K).apply_symm_apply u
    have hi (i : Fin (2 * K + 1)) :
        (fixedSeedDiagonalEntry 1 K i : ℂ) * (v : Fin (2 * K + 1) → ℂ) i = u.val.val i :=
      congrArg (fun w : poleNeutralEvenSubspace 1 K => w.val.val i) hv
    ext i
    simp only [normalizedSeedMatrix, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
    change normalizedSeedEntry K (L : ℂ) i * u.val.val i =
      (fixedSeedDiagonalEntry L K i : ℂ) * (v : Fin (2 * K + 1) → ℂ) i
    rw [normalizedSeedEntry_ofReal, ← hi i]
    have hd : (fixedSeedDiagonalEntry 1 K i : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (fixedSeedDiagonalEntry_pos (by norm_num) K i))
    field_simp
  · let v := (fixedOddSeedPhysicalEquiv (L := 1) (by norm_num) K).symm u
    have hv := (fixedOddSeedPhysicalEquiv (L := 1) (by norm_num) K).apply_symm_apply u
    have hi (i : Fin (2 * K + 1)) :
        (fixedSeedDiagonalEntry 1 K i : ℂ) * (v : Fin (2 * K + 1) → ℂ) i = u.val.val i :=
      congrArg (fun w : poleNeutralOddSubspace 1 K => w.val.val i) hv
    ext i
    simp only [normalizedSeedMatrix, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
    change normalizedSeedEntry K (L : ℂ) i * u.val.val i =
      (fixedSeedDiagonalEntry L K i : ℂ) * (v : Fin (2 * K + 1) → ℂ) i
    rw [normalizedSeedEntry_ofReal, ← hi i]
    have hd : (fixedSeedDiagonalEntry 1 K i : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (fixedSeedDiagonalEntry_pos (by norm_num) K i))
    field_simp

theorem nativeSeedAmbientIsometry_inner_canonical (p : ReversalParity) (L : ℝ) (K : ℕ)
    (u v : nativePoleNeutralParitySpace p L K) :
    inner ℂ (nativePoleNeutralParityCanonical p L K u) v =
      inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin (nativeSeedAmbientIsometry p L K u))
        (nativeSeedAmbientIsometry p L K v) := by
  cases p
  · calc
      _ = inner ℂ (evenCompressedCanonical L K u.val) v.val :=
        Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
          (𝕜 := ℂ) (E := euclideanEvenBoundaryFlatSubspace K)
          (K := poleNeutralEvenSubspace L K) v (evenCompressedCanonical L K u.val)
      _ = _ := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
        (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin (2 * K + 1)))
        (K := euclideanEvenBoundaryFlatSubspace K) v.val
        ((canonicalSourceMatrix L K).toEuclideanLin u.val.val)
  · calc
      _ = inner ℂ (oddCompressedCanonical L K u.val) v.val :=
        Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
          (𝕜 := ℂ) (E := euclideanOddBoundaryFlatSubspace K)
          (K := poleNeutralOddSubspace L K) v (oddCompressedCanonical L K u.val)
      _ = _ := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
        (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin (2 * K + 1)))
        (K := euclideanOddBoundaryFlatSubspace K) v.val
        ((canonicalSourceMatrix L K).toEuclideanLin u.val.val)

theorem liftedFullSource_log_fixedCell {Q : ℕ} (hQ : 1 ≤ Q) {L : ℝ}
    (hLc : L ∈ fixedCanonicalCutoffCell Q) (K : ℕ) :
    liftedFullSource Q K (Real.log L : ℂ) = canonicalSourceMatrix L K := by
  have hL : 0 < L := fixedCanonicalCutoffCell_subset_Ioi hQ hLc
  rw [liftedFullSource, ← Complex.ofReal_exp, Real.exp_log hL,
    complexFrozenCanonicalSourceRemainder_ofReal Q hL]
  exact (frozenCanonicalSourceMatrix_eq_neg_log_identity_add_remainder Q K hL).symm.trans
    (frozenCanonicalSourceMatrix_eq_canonicalSourceMatrix_fixedCell hQ hLc K)

theorem normalizedSeedMatrix_real_isSymmetric (L : ℝ) (K : ℕ) :
    (normalizedSeedMatrix K (L : ℂ)).toEuclideanLin.IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  simp [normalizedSeedEntry_ofReal, isSelfAdjoint_iff]

/-- Exact physical congruence, including the full nonunitary frame on both sides. -/
theorem liftedNativeFrame_log_fixedCell {Q : ℕ} (hQ : 1 ≤ Q) {L : ℝ}
    (hLc : L ∈ fixedCanonicalCutoffCell Q) (p : ReversalParity) (K : ℕ)
    (hL : 0 < L) :
    liftedNativeFrame K (nativeSeedAmbientIsometry p 1 K) Q (Real.log L : ℂ) =
      (nativeSeedPhysicalTransport p hL K).toLinearMap.adjoint.comp
        ((nativePoleNeutralParityCanonical p L K).comp
          (nativeSeedPhysicalTransport p hL K).toLinearMap) := by
  ext x
  apply ext_inner_right ℂ
  intro y
  simp only [liftedNativeFrame, LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  rw [normalizedFrameSource, ← Complex.ofReal_exp, Real.exp_log hL,
    liftedFullSource_log_fixedCell hQ hLc, Matrix.toLpLin_mul_same,
    Matrix.toLpLin_mul_same]
  simp only [LinearMap.comp_apply]
  rw [normalizedSeedMatrix_real_isSymmetric L K]
  change inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin
    ((normalizedSeedMatrix K (L : ℂ)).toEuclideanLin (nativeSeedAmbientIsometry p 1 K x)))
    ((normalizedSeedMatrix K (L : ℂ)).toEuclideanLin (nativeSeedAmbientIsometry p 1 K y)) = _
  rw [normalizedSeedMatrix_physical_transport p hL K x,
    normalizedSeedMatrix_physical_transport p hL K y]
  exact (nativeSeedAmbientIsometry_inner_canonical p L K _ _).symm

theorem nativeCanonical_bijective_of_frameDet_ne_zero {Q : ℕ} (hQ : 1 ≤ Q)
    {L : ℝ} (hLc : L ∈ fixedCanonicalCutoffCell Q) (p : ReversalParity) (K : ℕ)
    (hd : liftedNativeFrameDet K (nativeSeedAmbientIsometry p 1 K) Q (Real.log L : ℂ) ≠ 0) :
    Function.Bijective (nativePoleNeutralParityCanonical p L K) := by
  have hL := fixedCanonicalCutoffCell_subset_Ioi hQ hLc
  let T := nativeSeedPhysicalTransport p hL K
  let H := liftedNativeFrame K (nativeSeedAmbientIsometry p 1 K) Q (Real.log L : ℂ)
  have hker : H.ker = ⊥ := by
    by_contra hn
    exact hd (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hn)
  have hinj : Function.Injective H := LinearMap.ker_eq_bot.mp hker
  have hA : Function.Injective (nativePoleNeutralParityCanonical p L K) := by
    intro u v huv
    apply T.symm.injective
    apply hinj
    dsimp only [H]
    rw [liftedNativeFrame_log_fixedCell hQ hLc p K hL]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, T, LinearEquiv.apply_symm_apply, huv]
  exact ⟨hA, (LinearMap.injective_iff_surjective).mp hA⟩

/-- One aperture simultaneously regularizes every member of a preselected finite native family. -/
theorem exists_finite_native_regular_in_open_fixedCell {Q : ℕ} (hQ : 1 ≤ Q)
    (s : Finset (ReversalParity × ℕ)) {J : Set ℝ} (hJo : IsOpen J) (hJn : J.Nonempty)
    (hJc : J ⊆ fixedCanonicalCutoffCell Q) :
    ∃ L ∈ J, ∀ i ∈ s, Function.Bijective (nativePoleNeutralParityCanonical i.1 L i.2) := by
  let f : ReversalParity × ℕ → ℂ → ℂ := fun i =>
    liftedNativeFrameDet i.2 (nativeSeedAmbientIsometry i.1 1 i.2) Q
  have ha (i : ReversalParity × ℕ) : AnalyticOnNhd ℂ (f i) liftedFrozenRigidityDomain :=
    fun z hz => analyticOnNhd_liftedNativeFrameDet i.2 (nativeSeedAmbientIsometry i.1 1 i.2) Q z
      (liftedFrozenRigidityDomain_subset_liftedFrozenPredecessorDomain hz)
  have hn (i : ReversalParity × ℕ) : ∃ z ∈ liftedFrozenRigidityDomain, f i z ≠ 0 :=
    exists_mem_corridor_liftedNativeFrameDet_ne_zero i.2 (nativeSeedAmbientIsometry i.1 1 i.2) Q
  obtain ⟨L, hLJ, hLf⟩ := exists_finite_log_nonzero_in_open_positive s f
    (fun i _ => ha i) (fun i _ => hn i) hJo hJn
      (fun L hL => fixedCanonicalCutoffCell_subset_Ioi hQ (hJc hL))
  exact ⟨L, hLJ, fun i hi => nativeCanonical_bijective_of_frameDet_ne_zero hQ (hJc hLJ)
    i.1 i.2 (hLf i hi)⟩

end Zeta23.OPICARound4.RegularCells
