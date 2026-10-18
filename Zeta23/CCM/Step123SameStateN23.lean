import Zeta23.CCM.Step123SameStateN21

/-!
# N23 `retained.tie`: singular-safe tie completion on the stored selected ground

This module proves contract field N23 for the ACTUAL stored packet
`out : Step123NativeOutput β σ a`, in the tie case of the actual native
pole-neutral bottoms `E = O` at the stored aperture
`L = fixedOriginalSincTrialAperture a` and the stored selected cutoff
`K = out.retained.state.selection.cutoff`.  The tie is the only extra
hypothesis; it is a genuine case of the N21 trichotomy, not a bridge.  At
the stored value `lam = out.retained.state.selection.lam` and the STORED
selected ground `out.selectedGround`, in whichever parity was stored, it
proves (`Step123NativeOutput.n23_retained_tie`):

* `lam = E = O`; both actual shifted operators `A0 - lam` (even) and
  `B0 - lam` (odd) are positive and strictly positive on the orthogonal
  complements of their actual kernels, and BOTH actual kernels are
  nontrivial, so neither shifted operator is inverted on its whole space;
* for a stored even `u`: the transformed source equation
  `(B0 - lam) D0 u = S0(u) • g0`; kernel compatibility in the projected
  form `P_ker(B0 - lam) (S0(u) • g0) = 0`, in the factored form
  `S0(u) • P_ker(B0 - lam) g0 = 0` and as the dichotomy
  `S0(u) = 0 ∨ P_ker(B0 - lam) g0 = 0`; the cross-pairing
  `S0(u) = 0 ∨ <g0, w> = 0` for every actual odd eigenvector `w` at `lam`;
  and the positive-complement inverse of `B0 - lam` (built only on
  `ker(B0 - lam)ᗮ`, never on the singular map) applied to `S0(u) • g0`,
  with the full kernel component of `D0 u` retained:
  `D0 u = P_ker(D0 u) + (B0 - lam)|_{kerᗮ}⁻¹ (S0(u) • g0)`, the response
  being `D0 u - P_ker(D0 u)`, lying in `kerᗮ`, solving the equation and
  being the unique solution there; the retained term is the existing
  `poleNeutralEvenEigen_indexKernelComponent` and the response the
  existing `poleNeutralEvenEigen_indexComplementComponent`;
* for a stored odd `w`: the same with the negative adjoint source,
  `(A0 - lam) D0* w = -<g0,w> • S0*`, its kernel compatibility in the
  projected, factored and dichotomy forms, the cross-pairing with every
  actual even eigenvector at `lam`, and the positive-complement inverse of
  `A0 - lam` with the full kernel component of `D0* w` retained.  No even
  ground is chosen for a stored odd vector.

The range condition used by every inverse is the PROVED one, obtained from
the actual rank-one identity (resp. adjoint competitor equation) on the
stored ground; the generic certificate
`NativeRetainedKernelComplementInverse.of_apply` needs nothing beyond the
equation `T x = f` and positivity of `T`.  Everything is built on the N21
tie record of the same stored ground (`PoleNeutralTiedStoredGroundFacts`)
and the existing generic adapters `nativeKernelComplementResponse`,
`nativeKernelComplement_positive` and `nativeKernelComplement_decomposition`.

What is NOT proved here: `S0(u) ≠ 0` (or `<g0,w> ≠ 0`) is NOT asserted at a
tie, and neither is `P_ker g0 ≠ 0`; no bound on the complementary inverse
is given; no Step 4 law, no A-X/B-Y/C-Schur estimate, no claim that the
producer or the 44-field release is complete, no D2 statement, and nothing
about the Riemann hypothesis.
-/

noncomputable section

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

/-! ## Generic positive-complement inverse with retained kernel term -/

section RetainedKernelInverse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Retained-kernel positive-complement inverse certificate for ONE
transformed vector `x` and ONE source `f`, relative to a symmetric operator
`T`: the equation `T x = f`, kernel compatibility of `f`, positivity of `T`
and strict positivity on `(ker T)ᗮ`, the existing complement inverse
`nativeKernelComplementResponse` as a two-sided inverse there, its unique
solution of `T y = f` in `(ker T)ᗮ`, and the decomposition of `x` that
retains its full kernel component `P_ker x`.  The singular map `T` itself
is never inverted. -/
structure NativeRetainedKernelComplementInverse (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (x f : E) : Prop where
  source_eq : T x = f
  range_mem : f ∈ LinearMap.range T
  source_kernelProjection_eq_zero : (LinearMap.ker T).orthogonalProjectionOnto f = 0
  source_orthogonal_kernel : ∀ k ∈ LinearMap.ker T, inner ℂ k f = 0
  positive : T.IsPositive
  complement_positive : ∀ y ∈ (LinearMap.ker T)ᗮ, y ≠ 0 → 0 < (inner ℂ (T y) y).re
  complement_left_inverse : ∀ y ∈ (LinearMap.ker T)ᗮ,
    nativeKernelComplementResponse T hT (T y) (LinearMap.mem_range_self T y) = y
  complement_right_inverse : ∀ (g : E) (hg : g ∈ LinearMap.range T),
    T (nativeKernelComplementResponse T hT g hg) = g
  response_mem_complement :
    nativeKernelComplementResponse T hT f range_mem ∈ (LinearMap.ker T)ᗮ
  response_apply : T (nativeKernelComplementResponse T hT f range_mem) = f
  response_unique : ∀ y ∈ (LinearMap.ker T)ᗮ, T y = f →
    y = nativeKernelComplementResponse T hT f range_mem
  response_eq_sub_kernelTerm : nativeKernelComplementResponse T hT f range_mem =
    x - (LinearMap.ker T).starProjection x
  kernelTerm_mem : (LinearMap.ker T).starProjection x ∈ LinearMap.ker T
  decomposition : x = (LinearMap.ker T).starProjection x +
    nativeKernelComplementResponse T hT f range_mem
  solution_decomposition : ∀ y : E, T y = f →
    y = (LinearMap.ker T).starProjection y + nativeKernelComplementResponse T hT f range_mem

/-- The complement inverse solves the equation for every range element. -/
theorem nativeKernelComplementResponse_apply_eq (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (g : E) (hg : g ∈ LinearMap.range T) :
    T (nativeKernelComplementResponse T hT g hg) = g := by
  obtain ⟨z, hz⟩ := id hg
  rw [nativeKernelComplementResponse_eq T hT z g hg hz, map_sub,
    LinearMap.mem_ker.mp ((LinearMap.ker T).starProjection_apply_mem z), sub_zero, hz]

/-- The complement inverse takes values in the kernel complement. -/
theorem nativeKernelComplementResponse_mem_kernelOrthogonal (T : E →ₗ[ℂ] E)
    (hT : T.IsSymmetric) (g : E) (hg : g ∈ LinearMap.range T) :
    nativeKernelComplementResponse T hT g hg ∈ (LinearMap.ker T)ᗮ :=
  ((nativeKernelComplementEquiv T hT).symm _).property

/-- The certificate holds for every actual solution `T x = f` of a positive
operator; nothing about `f` beyond that equation is used. -/
theorem NativeRetainedKernelComplementInverse.of_apply (T : E →ₗ[ℂ] E)
    (hT : T.IsSymmetric) (hpos : T.IsPositive) (x f : E) (hx : T x = f) :
    NativeRetainedKernelComplementInverse T hT x f := by
  have hr : f ∈ LinearMap.range T := ⟨x, hx⟩
  exact {
    source_eq := hx
    range_mem := hr
    source_kernelProjection_eq_zero := by
      rw [← hx]
      exact nativeSymmetric_kernelProjection_output_eq_zero T hT x
    source_orthogonal_kernel := fun k hk => by
      rw [← hx]
      exact nativeSymmetric_output_mem_kernelOrthogonal T hT x k hk
    positive := hpos
    complement_positive := fun y hy hy0 =>
      nativeKernelComplement_positive T hpos ⟨y, hy⟩ (fun h => hy0 (congrArg Subtype.val h))
    complement_left_inverse := fun y hy =>
      nativeKernelComplementResponse_eq_of_mem T hT y (T y) _ hy rfl
    complement_right_inverse := nativeKernelComplementResponse_apply_eq T hT
    response_mem_complement := nativeKernelComplementResponse_mem_kernelOrthogonal T hT f hr
    response_apply := nativeKernelComplementResponse_apply_eq T hT f hr
    response_unique := fun y hy hyf =>
      (nativeKernelComplementResponse_eq_of_mem T hT y f hr hy hyf).symm
    response_eq_sub_kernelTerm := nativeKernelComplementResponse_eq T hT x f hr hx
    kernelTerm_mem := (LinearMap.ker T).starProjection_apply_mem x
    decomposition := nativeKernelComplement_decomposition T hT x f hr hx
    solution_decomposition := fun y hy => nativeKernelComplement_decomposition T hT y f hr hy }

end RetainedKernelInverse

/-! ## Cross-parity pairing at a common value -/

/-- For an actual even eigenvector `u` and an actual odd eigenvector `w` at
the same real value `lam`, the corrected source of `u` or the cubic pairing
of `w` vanishes.  Neither factor is claimed nonzero. -/
theorem poleNeutral_eigen_pair_source_pairing_eq_zero {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u)
    (w : poleNeutralOddSubspace L K)
    (hw : poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w) :
    poleNeutralCorrectedCubicSource L K u = 0 ∨ poleNeutralCubicPairingFunctional L K w = 0 := by
  have hsym := poleNeutralOddShiftedCanonical_isSymmetric L K lam
  have hsrc : poleNeutralOddShiftedCanonical L K lam (poleNeutralIndexLinearMap hL K u) =
      poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K := by
    have h := poleNeutral_shifted_rankOneIntertwining hL K hK lam u
    have ha : poleNeutralEvenShiftedCanonical L K lam u = 0 := by
      simp only [poleNeutralEvenShiftedCanonical, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, hu, sub_self]
    rw [ha, map_zero, sub_zero] at h
    exact h
  have hw0 : poleNeutralOddShiftedCanonical L K lam w = 0 := by
    simp only [poleNeutralOddShiftedCanonical, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, hw, sub_self]
  have hi : inner ℂ w
      (poleNeutralOddShiftedCanonical L K lam (poleNeutralIndexLinearMap hL K u)) = 0 := by
    rw [← hsym w, hw0]
    exact @inner_zero_left ℂ (poleNeutralOddSubspace L K) _ _
      (poleNeutralOdd_innerProductSpace L K) _
  have hm : poleNeutralCorrectedCubicSource L K u *
      inner ℂ w (poleNeutralCubicCompressionVector L K) = 0 := by
    rw [← hi, hsrc]
    exact (@inner_smul_right ℂ (poleNeutralOddSubspace L K) _ _
      (poleNeutralOdd_innerProductSpace L K) _ _ _).symm
  rcases mul_eq_zero.mp hm with h | h
  · exact Or.inl h
  · right
    have hc : (starRingEnd ℂ) (inner ℂ w (poleNeutralCubicCompressionVector L K)) =
        inner ℂ (poleNeutralCubicCompressionVector L K) w :=
      @inner_conj_symm ℂ (poleNeutralOddSubspace L K) _ _
        (poleNeutralOdd_innerProductSpace L K) _ _
    change inner ℂ (poleNeutralCubicCompressionVector L K) w = 0
    rw [← hc, h, map_zero]

/-! ## Both shifted kernels are nontrivial at a tie -/

/-- When `lam` equals both actual neutral bottoms, both actual shifted
operators have a nonzero kernel vector (an actual eigenmode at the
bottom).  So at a tie neither shifted operator is invertible, and only its
kernel complement is inverted. -/
theorem poleNeutral_shiftedKernels_nontrivial_of_eq_bottoms {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hE : lam = poleNeutralEvenRayleighBottom L K hL hK)
    (hO : lam = poleNeutralOddRayleighBottom L K hL hK) :
    (∃ v : poleNeutralEvenSubspace L K, v ≠ 0 ∧
        poleNeutralEvenShiftedCanonical L K lam v = 0) ∧
      (∃ v : poleNeutralOddSubspace L K, v ≠ 0 ∧
        poleNeutralOddShiftedCanonical L K lam v = 0) := by
  obtain ⟨u, hu0, hu⟩ := exists_eigenmode_at_poleNeutralEvenRayleighBottom hL K hK
  obtain ⟨w, hw0, hw⟩ := exists_eigenmode_at_poleNeutralOddRayleighBottom hL K hK
  refine ⟨⟨u, hu0, ?_⟩, ⟨w, hw0, ?_⟩⟩
  · rw [hE]
    simp only [poleNeutralEvenShiftedCanonical, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, hu, sub_self]
  · rw [hO]
    simp only [poleNeutralOddShiftedCanonical, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, hw, sub_self]

/-! ## Tie records: retained kernel term and positive-complement inverse -/

/-- N23 consequences for ONE actual even vector `u` at `lam`, extending the
N21 tie record: the transformed source equation, kernel compatibility in
both the projected-source and the factored form, the cross-pairing with
every odd eigenvector at `lam`, and the positive-complement inverse of the
actual shifted odd operator with the full kernel component of `D0 u`
retained.  No nonvanishing of `S0(u)` is asserted. -/
structure PoleNeutralTiedEvenRetainedInverseFacts {L : ℝ} (hL : 0 < L) (K : ℕ)
    (hK : 3 ≤ K) (lam : ℝ) (u : poleNeutralEvenSubspace L K) : Prop where
  tied : PoleNeutralTiedEvenGroundFacts hL K hK lam u
  source_eq : poleNeutralOddShiftedCanonical L K lam (poleNeutralIndexLinearMap hL K u) =
    poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K
  kernelProjection_source_eq_zero :
    poleNeutralOddShiftedKernelProjection L K lam
      (poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K) = 0
  kernel_compatibility_cases : poleNeutralCorrectedCubicSource L K u = 0 ∨
    poleNeutralOddShiftedKernelProjection L K lam (poleNeutralCubicCompressionVector L K) = 0
  odd_eigen_pairing : ∀ w : poleNeutralOddSubspace L K,
    poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w →
    poleNeutralCorrectedCubicSource L K u = 0 ∨ poleNeutralCubicPairingFunctional L K w = 0
  inverse : NativeRetainedKernelComplementInverse (poleNeutralOddShiftedCanonical L K lam)
    (poleNeutralOddShiftedCanonical_isSymmetric L K lam) (poleNeutralIndexLinearMap hL K u)
    (poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K)
  kernelTerm_eq_indexKernelComponent :
    (LinearMap.ker (poleNeutralOddShiftedCanonical L K lam)).starProjection
        (poleNeutralIndexLinearMap hL K u) =
      (poleNeutralEvenEigen_indexKernelComponent hL K lam u).val
  response_eq_indexComplementComponent :
    poleNeutralOddKernelComplementResponse L K lam
        (poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K)
        tied.range_mem =
      poleNeutralEvenEigen_indexComplementComponent hL K lam u

/-- N23 consequences for ONE actual odd vector `w` at `lam`, extending the
N21 tie record: kernel compatibility of the negative adjoint source in the
projected and factored forms, the cross-pairing with every even
eigenvector at `lam`, and the positive-complement inverse of the actual
shifted even operator with the full kernel component of `D0* w` retained.
No nonvanishing of the cubic pairing or of any `S0` value is asserted. -/
structure PoleNeutralTiedOddRetainedInverseFacts {L : ℝ} (hL : 0 < L) (K : ℕ)
    (hK : 3 ≤ K) (lam : ℝ) (w : poleNeutralOddSubspace L K) : Prop where
  tied : PoleNeutralTiedOddGroundFacts hL K hK lam w
  kernelProjection_source_eq_zero :
    poleNeutralEvenShiftedKernelProjection L K lam
      (-poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K) = 0
  kernel_compatibility_cases : poleNeutralCubicPairingFunctional L K w = 0 ∨
    poleNeutralEvenShiftedKernelProjection L K lam (poleNeutralCorrectedCubicRieszVector L K) = 0
  even_eigen_pairing : ∀ v : poleNeutralEvenSubspace L K,
    poleNeutralEvenCompressedCanonical L K v = (lam : ℂ) • v →
    poleNeutralCorrectedCubicSource L K v = 0 ∨ poleNeutralCubicPairingFunctional L K w = 0
  inverse : NativeRetainedKernelComplementInverse (poleNeutralEvenShiftedCanonical L K lam)
    (poleNeutralEvenShiftedCanonical_isSymmetric L K lam)
    ((LinearMap.adjoint (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
      (F := poleNeutralOddSubspace L K) (poleNeutralIndexLinearMap hL K)) w)
    (-poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K)

/-- N23 consequences for a stored parity-tagged vector, in its own stored
parity. -/
def PoleNeutralTiedStoredRetainedInverseFacts {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (lam : ℝ) : (γ : ReversalParity) → nativePoleNeutralParitySpace γ L K → Prop
  | .even, u => PoleNeutralTiedEvenRetainedInverseFacts hL K hK lam u
  | .odd, w => PoleNeutralTiedOddRetainedInverseFacts hL K hK lam w

/-- From the N21 even tie record and the positivity range `lam ≤ O` of the
opposite shift (all-vector statement). -/
theorem PoleNeutralTiedEvenRetainedInverseFacts.of_tied {L : ℝ} {hL : 0 < L} {K : ℕ}
    {hK : 3 ≤ K} {lam : ℝ} {u : poleNeutralEvenSubspace L K}
    (hlamO : lam ≤ poleNeutralOddRayleighBottom L K hL hK)
    (h : PoleNeutralTiedEvenGroundFacts hL K hK lam u) :
    PoleNeutralTiedEvenRetainedInverseFacts hL K hK lam u := by
  have hsrc : poleNeutralOddShiftedCanonical L K lam (poleNeutralIndexLinearMap hL K u) =
      poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K := by
    have hr := poleNeutral_shifted_rankOneIntertwining hL K hK lam u
    have ha : poleNeutralEvenShiftedCanonical L K lam u = 0 := by
      simp only [poleNeutralEvenShiftedCanonical, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, h.eigen, sub_self]
    rw [ha, map_zero, sub_zero] at hr
    exact hr
  have hpos : LinearMap.IsPositive (𝕜 := ℂ) (E := poleNeutralOddSubspace L K)
      (poleNeutralOddShiftedCanonical L K lam) :=
    poleNeutralOddShifted_isPositive_of_le_bottom hL K hK lam hlamO
  have hinv := @NativeRetainedKernelComplementInverse.of_apply (poleNeutralOddSubspace L K)
    (poleNeutralOddSubspace L K).normedAddCommGroup (poleNeutralOdd_innerProductSpace L K)
    inferInstance (poleNeutralOddShiftedCanonical L K lam)
    (poleNeutralOddShiftedCanonical_isSymmetric L K lam) hpos
    (poleNeutralIndexLinearMap hL K u)
    (poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K) hsrc
  have hproj : poleNeutralOddShiftedKernelProjection L K lam
      (poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K) = 0 := by
    rw [map_smul]
    exact h.kernel_compatibility
  have hcomp := @nativeKernelComplementResponse_eq_of_mem (poleNeutralOddSubspace L K)
    (poleNeutralOddSubspace L K).normedAddCommGroup
    (poleNeutralOdd_innerProductSpace L K) inferInstance
    (poleNeutralOddShiftedCanonical L K lam)
    (poleNeutralOddShiftedCanonical_isSymmetric L K lam)
    (poleNeutralEvenEigen_indexComplementComponent hL K lam u)
    (poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K) h.range_mem
    (poleNeutralEvenEigen_indexComplement_mem_kernel_orthogonal hL K lam u)
    (poleNeutral_even_eigen_complement_source_eq hL K hK lam u h.eigen)
  exact {
    tied := h
    source_eq := hsrc
    kernelProjection_source_eq_zero := hproj
    kernel_compatibility_cases := smul_eq_zero.mp h.kernel_compatibility
    odd_eigen_pairing := fun w hw =>
      poleNeutral_eigen_pair_source_pairing_eq_zero hL K hK lam u h.eigen w hw
    inverse := hinv
    kernelTerm_eq_indexKernelComponent := by
      simp only [poleNeutralEvenEigen_indexKernelComponent,
        poleNeutralOddShiftedKernelProjection, Submodule.coe_orthogonalProjectionOnto_apply]
    response_eq_indexComplementComponent := hcomp }

/-- From the N21 odd tie record and the positivity range `lam ≤ E` of the
opposite shift (all-vector statement). -/
theorem PoleNeutralTiedOddRetainedInverseFacts.of_tied {L : ℝ} {hL : 0 < L} {K : ℕ}
    {hK : 3 ≤ K} {lam : ℝ} {w : poleNeutralOddSubspace L K}
    (hlamE : lam ≤ poleNeutralEvenRayleighBottom L K hL hK)
    (h : PoleNeutralTiedOddGroundFacts hL K hK lam w) :
    PoleNeutralTiedOddRetainedInverseFacts hL K hK lam w := by
  have hpos : LinearMap.IsPositive (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
      (poleNeutralEvenShiftedCanonical L K lam) :=
    poleNeutralEvenShifted_isPositive_of_le_bottom hL K hK lam hlamE
  have hinv := @NativeRetainedKernelComplementInverse.of_apply (poleNeutralEvenSubspace L K)
    (poleNeutralEvenSubspace L K).normedAddCommGroup (poleNeutralEven_innerProductSpace L K)
    inferInstance (poleNeutralEvenShiftedCanonical L K lam)
    (poleNeutralEvenShiftedCanonical_isSymmetric L K lam) hpos
    ((LinearMap.adjoint (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
      (F := poleNeutralOddSubspace L K) (poleNeutralIndexLinearMap hL K)) w)
    (-poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K)
    h.adjoint_competitor
  have hproj : poleNeutralEvenShiftedKernelProjection L K lam
      (-poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K) =
        0 := by
    rw [map_smul]
    exact h.kernel_compatibility
  have hcases : poleNeutralCubicPairingFunctional L K w = 0 ∨
      poleNeutralEvenShiftedKernelProjection L K lam
        (poleNeutralCorrectedCubicRieszVector L K) = 0 := by
    rcases smul_eq_zero.mp h.kernel_compatibility with hc | hc
    · exact Or.inl (neg_eq_zero.mp hc)
    · exact Or.inr hc
  exact {
    tied := h
    kernelProjection_source_eq_zero := hproj
    kernel_compatibility_cases := hcases
    even_eigen_pairing := fun v hv =>
      poleNeutral_eigen_pair_source_pairing_eq_zero hL K hK lam v hv w h.eigen
    inverse := hinv }

/-- Stored-parity version (all-vector statement). -/
theorem PoleNeutralTiedStoredRetainedInverseFacts.of_tied {L : ℝ} {hL : 0 < L} {K : ℕ}
    {hK : 3 ≤ K} {lam : ℝ}
    (hlamE : lam ≤ poleNeutralEvenRayleighBottom L K hL hK)
    (hlamO : lam ≤ poleNeutralOddRayleighBottom L K hL hK)
    (γ : ReversalParity) (g : nativePoleNeutralParitySpace γ L K)
    (h : PoleNeutralTiedStoredGroundFacts hL K hK lam γ g) :
    PoleNeutralTiedStoredRetainedInverseFacts hL K hK lam γ g := by
  cases γ with
  | even => exact PoleNeutralTiedEvenRetainedInverseFacts.of_tied hlamO h
  | odd => exact PoleNeutralTiedOddRetainedInverseFacts.of_tied hlamE h

/-- Reading stored N23 facts through the even view. -/
theorem PoleNeutralTiedStoredRetainedInverseFacts.even_view {L : ℝ} {hL : 0 < L} {K : ℕ}
    {hK : 3 ≤ K} {lam : ℝ} {γ : ReversalParity} {g : nativePoleNeutralParitySpace γ L K}
    (h : PoleNeutralTiedStoredRetainedInverseFacts hL K hK lam γ g) (hγ : γ = .even) :
    PoleNeutralTiedEvenRetainedInverseFacts hL K hK lam (nativeParityEvenView γ hγ g) := by
  subst hγ
  exact h

/-- Reading stored N23 facts through the odd view. -/
theorem PoleNeutralTiedStoredRetainedInverseFacts.odd_view {L : ℝ} {hL : 0 < L} {K : ℕ}
    {hK : 3 ≤ K} {lam : ℝ} {γ : ReversalParity} {g : nativePoleNeutralParitySpace γ L K}
    (h : PoleNeutralTiedStoredRetainedInverseFacts hL K hK lam γ g) (hγ : γ = .odd) :
    PoleNeutralTiedOddRetainedInverseFacts hL K hK lam (nativeParityOddView γ hγ g) := by
  subst hγ
  exact h

/-! ## N23 on the actual stored output packet -/

/-- Singular-safe tie completion for a parity-tagged vector `g` at `lam`:
`lam` is both actual bottoms, both shifted operators are positive (strictly
on their kernel complements), both actual shifted kernels are nontrivial,
and `g`, in its own parity, carries the N23 retained-kernel inverse
record.  No nonvanishing of any source scalar is asserted. -/
structure PoleNeutralTieRetainedCompletion {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (lam : ℝ) (γ : ReversalParity) (g : nativePoleNeutralParitySpace γ L K) : Prop where
  lam_eq_even_bottom : lam = poleNeutralEvenRayleighBottom L K hL hK
  lam_eq_odd_bottom : lam = poleNeutralOddRayleighBottom L K hL hK
  positivity : PoleNeutralShiftedPositivity L K lam
  even_kernel_nontrivial : ∃ v : poleNeutralEvenSubspace L K, v ≠ 0 ∧
    poleNeutralEvenShiftedCanonical L K lam v = 0
  odd_kernel_nontrivial : ∃ v : poleNeutralOddSubspace L K, v ≠ 0 ∧
    poleNeutralOddShiftedCanonical L K lam v = 0
  stored : PoleNeutralTiedStoredRetainedInverseFacts hL K hK lam γ g

/-- N23 for the actual stored packet, in the tie case of the actual
neutral bottoms at the stored aperture and stored selected cutoff (a
genuine case split, not a bridge).  At the stored value `lam`, the STORED
selected ground, in its stored parity, carries kernel compatibility and the
positive-complement inverse of the opposite actual shifted operator with
its full kernel component retained; both shifted kernels are nontrivial.
Built on the N21 tie facts of the same stored ground; no `S0 ≠ 0` claim. -/
theorem Step123NativeOutput.n23_retained_tie {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (htie : poleNeutralEvenRayleighBottom (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty =
      poleNeutralOddRayleighBottom (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty) :
    PoleNeutralTieRetainedCompletion out.aperture_pos
      out.retained.state.selection.cutoff out.retained.state.selection.cutoff_nonempty
      out.retained.state.selection.lam out.retained.state.selectedParity
      out.selectedGround := by
  obtain ⟨hE, hO, hpos, hf⟩ := out.n21_tie_selectedGround htie
  obtain ⟨hkE, hkO⟩ := poleNeutral_shiftedKernels_nontrivial_of_eq_bottoms out.aperture_pos
    out.retained.state.selection.cutoff out.retained.state.selection.cutoff_nonempty
    out.retained.state.selection.lam hE hO
  exact {
    lam_eq_even_bottom := hE
    lam_eq_odd_bottom := hO
    positivity := hpos
    even_kernel_nontrivial := hkE
    odd_kernel_nontrivial := hkO
    stored := PoleNeutralTiedStoredRetainedInverseFacts.of_tied hE.le hO.le _ _ hf }

/-- N23 tie output on the actual stored packet when the stored parity is
even (a stored field, read through the definitional even view). -/
theorem Step123NativeOutput.n23_retained_tie_even {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (htie : poleNeutralEvenRayleighBottom (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty =
      poleNeutralOddRayleighBottom (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty)
    (hpar : out.retained.state.selectedParity = .even) :
    PoleNeutralTiedEvenRetainedInverseFacts out.aperture_pos
      out.retained.state.selection.cutoff out.retained.state.selection.cutoff_nonempty
      out.retained.state.selection.lam
      (nativeParityEvenView out.retained.state.selectedParity hpar out.selectedGround) :=
  (out.n23_retained_tie htie).stored.even_view hpar

/-- N23 tie output on the actual stored packet when the stored parity is
odd: the stored odd ground itself is used, no even ground is chosen. -/
theorem Step123NativeOutput.n23_retained_tie_odd {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (htie : poleNeutralEvenRayleighBottom (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty =
      poleNeutralOddRayleighBottom (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty)
    (hpar : out.retained.state.selectedParity = .odd) :
    PoleNeutralTiedOddRetainedInverseFacts out.aperture_pos
      out.retained.state.selection.cutoff out.retained.state.selection.cutoff_nonempty
      out.retained.state.selection.lam
      (nativeParityOddView out.retained.state.selectedParity hpar out.selectedGround) :=
  (out.n23_retained_tie htie).stored.odd_view hpar

/-- Literal readout of N23 for a stored EVEN ground `u` at a tie:
(a) kernel compatibility `P_ker(B0 - lam) (S0(u) g0) = 0`, also in the
factored form `S0(u) • P_ker g0 = 0`; (b) the transformed vector
`D0 u` equals its retained kernel component plus the positive-complement
inverse of `B0 - lam` applied to `S0(u) g0`, with that inverse lying in the
strictly positive kernel complement, solving the equation there, being
the unique solution there and equal to `D0 u - P_ker(D0 u)`.  The range
condition is the proved one from the actual rank-one identity.  No
`S0(u) ≠ 0` claim. -/
theorem Step123NativeOutput.n23_tie_even_readout {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (htie : poleNeutralEvenRayleighBottom (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty =
      poleNeutralOddRayleighBottom (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty)
    (hpar : out.retained.state.selectedParity = .even) :
    let L := fixedOriginalSincTrialAperture a
    let K := out.retained.state.selection.cutoff
    let lam := out.retained.state.selection.lam
    let u := nativeParityEvenView out.retained.state.selectedParity hpar out.selectedGround
    let T := poleNeutralOddShiftedCanonical L K lam
    let f := poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K
    T (poleNeutralIndexLinearMap out.aperture_pos K u) = f ∧
      poleNeutralOddShiftedKernelProjection L K lam f = 0 ∧
      poleNeutralCorrectedCubicSource L K u •
        poleNeutralOddShiftedKernelProjection L K lam
          (poleNeutralCubicCompressionVector L K) = 0 ∧
      ∃ hr : f ∈ LinearMap.range T,
        poleNeutralOddKernelComplementResponse L K lam f hr ∈
          Submodule.orthogonal (𝕜 := ℂ) (E := poleNeutralOddSubspace L K)
            (LinearMap.ker T) ∧
        T (poleNeutralOddKernelComplementResponse L K lam f hr) = f ∧
        (∀ y : poleNeutralOddSubspace L K,
          y ∈ Submodule.orthogonal (𝕜 := ℂ) (E := poleNeutralOddSubspace L K)
            (LinearMap.ker T) → T y = f →
          y = poleNeutralOddKernelComplementResponse L K lam f hr) ∧
        (∀ y : poleNeutralOddSubspace L K,
          y ∈ Submodule.orthogonal (𝕜 := ℂ) (E := poleNeutralOddSubspace L K)
            (LinearMap.ker T) → y ≠ 0 →
          0 < (inner ℂ (T y) y).re) ∧
        poleNeutralOddKernelComplementResponse L K lam f hr =
          poleNeutralIndexLinearMap out.aperture_pos K u -
            (LinearMap.ker T).starProjection (poleNeutralIndexLinearMap out.aperture_pos K u) ∧
        (LinearMap.ker T).starProjection (poleNeutralIndexLinearMap out.aperture_pos K u) ∈
          LinearMap.ker T ∧
        poleNeutralIndexLinearMap out.aperture_pos K u =
          (LinearMap.ker T).starProjection (poleNeutralIndexLinearMap out.aperture_pos K u) +
            poleNeutralOddKernelComplementResponse L K lam f hr := by
  dsimp only
  have h := out.n23_retained_tie_even htie hpar
  exact ⟨h.source_eq, h.kernelProjection_source_eq_zero, h.tied.kernel_compatibility,
    h.tied.range_mem, h.inverse.response_mem_complement, h.inverse.response_apply,
    h.inverse.response_unique, h.inverse.complement_positive,
    h.inverse.response_eq_sub_kernelTerm, h.inverse.kernelTerm_mem,
    h.inverse.decomposition⟩

/-- Literal readout of N23 for a stored ODD ground `w` at a tie, with the
negative adjoint source `-<g0,w> S0*`: (a) kernel compatibility
`P_ker(A0 - lam) (-<g0,w> S0*) = 0`, also factored; (b) `D0* w` equals its
retained kernel component plus the positive-complement inverse of
`A0 - lam` applied to that source, the unique solution in the strictly
positive kernel complement, equal to `D0* w - P_ker(D0* w)`.  No
`<g0,w> ≠ 0` claim. -/
theorem Step123NativeOutput.n23_tie_odd_readout {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (htie : poleNeutralEvenRayleighBottom (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty =
      poleNeutralOddRayleighBottom (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty)
    (hpar : out.retained.state.selectedParity = .odd) :
    let L := fixedOriginalSincTrialAperture a
    let K := out.retained.state.selection.cutoff
    let lam := out.retained.state.selection.lam
    let w := nativeParityOddView out.retained.state.selectedParity hpar out.selectedGround
    let T := poleNeutralEvenShiftedCanonical L K lam
    let x := (LinearMap.adjoint (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
      (F := poleNeutralOddSubspace L K) (poleNeutralIndexLinearMap out.aperture_pos K)) w
    let f := -poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K
    T x = f ∧
      poleNeutralEvenShiftedKernelProjection L K lam f = 0 ∧
      -poleNeutralCubicPairingFunctional L K w •
        poleNeutralEvenShiftedKernelProjection L K lam
          (poleNeutralCorrectedCubicRieszVector L K) = 0 ∧
      ∃ hr : f ∈ LinearMap.range T,
        poleNeutralEvenKernelComplementResponse L K lam f hr ∈
          Submodule.orthogonal (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
            (LinearMap.ker T) ∧
        T (poleNeutralEvenKernelComplementResponse L K lam f hr) = f ∧
        (∀ y : poleNeutralEvenSubspace L K,
          y ∈ Submodule.orthogonal (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
            (LinearMap.ker T) → T y = f →
          y = poleNeutralEvenKernelComplementResponse L K lam f hr) ∧
        (∀ y : poleNeutralEvenSubspace L K,
          y ∈ Submodule.orthogonal (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
            (LinearMap.ker T) → y ≠ 0 →
          0 < (inner ℂ (T y) y).re) ∧
        poleNeutralEvenKernelComplementResponse L K lam f hr =
          x - (LinearMap.ker T).starProjection x ∧
        (LinearMap.ker T).starProjection x ∈ LinearMap.ker T ∧
        x = (LinearMap.ker T).starProjection x +
          poleNeutralEvenKernelComplementResponse L K lam f hr := by
  dsimp only
  have h := out.n23_retained_tie_odd htie hpar
  refine ⟨h.tied.adjoint_competitor, h.kernelProjection_source_eq_zero,
    h.tied.kernel_compatibility, h.tied.range_mem, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.inverse.response_mem_complement
  · exact h.inverse.response_apply
  · exact h.inverse.response_unique
  · exact h.inverse.complement_positive
  · exact h.inverse.response_eq_sub_kernelTerm
  · exact h.inverse.kernelTerm_mem
  · exact h.tied.complementary_response

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeKernelComplementResponse_apply_eq
#print axioms Zeta23.CCM.nativeKernelComplementResponse_mem_kernelOrthogonal
#print axioms Zeta23.CCM.NativeRetainedKernelComplementInverse.of_apply
#print axioms Zeta23.CCM.poleNeutral_eigen_pair_source_pairing_eq_zero
#print axioms Zeta23.CCM.poleNeutral_shiftedKernels_nontrivial_of_eq_bottoms
#print axioms Zeta23.CCM.PoleNeutralTiedEvenRetainedInverseFacts.of_tied
#print axioms Zeta23.CCM.PoleNeutralTiedOddRetainedInverseFacts.of_tied
#print axioms Zeta23.CCM.PoleNeutralTiedStoredRetainedInverseFacts.of_tied
#print axioms Zeta23.CCM.PoleNeutralTiedStoredRetainedInverseFacts.even_view
#print axioms Zeta23.CCM.PoleNeutralTiedStoredRetainedInverseFacts.odd_view
#print axioms Zeta23.CCM.Step123NativeOutput.n23_retained_tie
#print axioms Zeta23.CCM.Step123NativeOutput.n23_retained_tie_even
#print axioms Zeta23.CCM.Step123NativeOutput.n23_retained_tie_odd
#print axioms Zeta23.CCM.Step123NativeOutput.n23_tie_even_readout
#print axioms Zeta23.CCM.Step123NativeOutput.n23_tie_odd_readout
