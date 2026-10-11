import Zeta23.CCM.CanonicalSecularResolvent
import Zeta23.CCM.CanonicalCompressedApertureC2

noncomputable section

namespace Zeta23.CCM

attribute [local instance] realContinuousSMulComplexCLM

/-!
# POST284 follow-up M29: source–resolvent derivatives (Steps 61, 62)

Let `A_L`, `B_L` be the legal even and odd canonical compressions, `D` the centered
index map, `g` the compressed cubic vector and

`H_L(z) = ⟪g, (B_L D - D A_L) z⟫ / ⟪g, g⟫`

the cubic defect functional, recovered from `A` and `B` by the rank-one factorization
(M74).  Where `λ_odd(L) > 0`, put `R = B_L⁻¹`, `r = R g`, `x = D⁻¹ r` and
`T(L) = H_L(x_L)`, the secular scalar with `1 - T(L) = det A_L / det B_L`.

* (Step 61) For fixed `z`, `L ↦ H_L(z)` is `C²` on `(0, ∞)`, seams included, and its
  derivative is the defect scalar of the production first jets
  (`cubicDefectFunctional_contDiffOn`, `cubicDefectFunctional_hasDerivAt`).
* (Steps 61, 62) At every `L > 0` with `λ_odd(L) > 0`,
  `T' = H'(x) + H(x')` and `T'' = H''(x) + 2 H'(x') + H(x'')`, with
  `x' = -D⁻¹ R B' r` and `x'' = D⁻¹ (2 R B' R B' r - R B'' r)`
  (`canonicalSecularScalar_hasDerivAt`).
* At a point with `T' = 0` (and `T'' = 0`), `H'(x) = -H(x')` (and
  `H''(x) = -2 H'(x') - H(x'')`) (`canonicalSecularScalar_stationary`).

Only the merged compressed `C²` jets and the derivative of the ring inverse are used;
there is no F04 hypothesis.  The third derivative of `T` (Step 63) needs `C³`, which is
proved only inside fixed cells, and its sign at a contact stays OPEN.  Nothing here
assumes or excludes a contact.
-/

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Product rule for a real-parameter family of complex-linear maps applied to a
moving vector. -/
theorem hasDerivAt_complexCLM_apply_real {f : ℝ → (E →L[ℂ] F)} {f' : E →L[ℂ] F}
    {u : ℝ → E} {u' : E} {L : ℝ} (hf : HasDerivAt f f' L) (hu : HasDerivAt u u' L) :
    HasDerivAt (fun s => f s (u s)) (f' (u L) + f L u') L := by
  let R : (E →L[ℂ] F) →L[ℝ] (E →L[ℝ] F) :=
    ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ
  have hR : HasDerivAt (fun s => R (f s)) (R f') L := R.hasFDerivAt.comp_hasDerivAt L hf
  have := hR.clm_apply hu
  simpa [R] using this

/-- Derivative of the inverse of a real-parameter operator family at an invertible
point: `(B⁻¹)' = -B⁻¹ B' B⁻¹`. -/
theorem hasDerivAt_ringInverse_complexCLM [CompleteSpace E] {B : ℝ → (E →L[ℂ] E)}
    {B' : E →L[ℂ] E} {L : ℝ} (hB : HasDerivAt B B' L) (hu : IsUnit (B L)) :
    HasDerivAt (fun s => Ring.inverse (B s))
      (-(Ring.inverse (B L) * B' * Ring.inverse (B L))) L := by
  obtain ⟨u, hu⟩ := hu
  have h := (hasFDerivAt_ringInverse (𝕜 := ℝ) u)
  rw [hu] at h
  have := h.comp_hasDerivAt L hB
  rw [← hu, Ring.inverse_unit]
  exact this

end Calculus

section Abstract

variable {E O : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup O] [InnerProductSpace ℂ O]
  (D : E ≃L[ℂ] O) (g : O)

/-- `Φ(b, a, z) = ⟪g, b (D z) - D (a z)⟫ / ⟪g, g⟫`; at `(B_L, A_L)` it is `H_L(z)`, at the
first and second jets it is `H'_L(z)` and `H''_L(z)`. -/
def secularDefectScalar (b : O →L[ℂ] O) (a : E →L[ℂ] E) (z : E) : ℂ :=
  inner ℂ g (b (D z) - D (a z)) / inner ℂ g g

/-- Product rule for `Φ` along operator families and a moving vector. -/
theorem hasDerivAt_secularDefectScalar {b : ℝ → (O →L[ℂ] O)} {a : ℝ → (E →L[ℂ] E)}
    {x : ℝ → E} {b' : O →L[ℂ] O} {a' : E →L[ℂ] E} {x' : E} {L : ℝ}
    (hb : HasDerivAt b b' L) (ha : HasDerivAt a a' L) (hx : HasDerivAt x x' L) :
    HasDerivAt (fun s => secularDefectScalar D g (b s) (a s) (x s))
      (secularDefectScalar D g b' a' (x L) + secularDefectScalar D g (b L) (a L) x') L := by
  let Dr : E →L[ℝ] O := (D : E →L[ℂ] O).restrictScalars ℝ
  have hDx : HasDerivAt (fun s => D (x s)) (D x') L := Dr.hasFDerivAt.comp_hasDerivAt L hx
  have h1 := hasDerivAt_complexCLM_apply_real hb hDx
  have h2 := hasDerivAt_complexCLM_apply_real ha hx
  have h2' : HasDerivAt (fun s => D (a s (x s))) (D (a' (x L) + a L x')) L :=
    Dr.hasFDerivAt.comp_hasDerivAt L h2
  have h3 := h1.sub h2'
  let I : O →L[ℝ] ℂ := (innerSL ℂ g).restrictScalars ℝ
  have h4 := I.hasFDerivAt.comp_hasDerivAt L h3
  have h5 := h4.div_const (inner ℂ g g)
  unfold secularDefectScalar
  refine h5.congr_deriv ?_
  simp only [I, ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply, map_add,
    inner_add_right, inner_sub_right]
  rw [← add_div]
  congr 1
  ring

@[simp] theorem secularDefectScalar_zero (b : O →L[ℂ] O) (a : E →L[ℂ] E) :
    secularDefectScalar D g b a 0 = 0 := by
  simp [secularDefectScalar]

theorem hasDerivAt_secularDefectScalar_const
    {b : ℝ → (O →L[ℂ] O)} {a : ℝ → (E →L[ℂ] E)}
    {b' : O →L[ℂ] O} {a' : E →L[ℂ] E} {L : ℝ}
    (hb : HasDerivAt b b' L) (ha : HasDerivAt a a' L) (z : E) :
    HasDerivAt (fun s => secularDefectScalar D g (b s) (a s) z)
      (secularDefectScalar D g b' a' z) L := by
  have h := hasDerivAt_secularDefectScalar D g hb ha (hasDerivAt_const L z)
  rwa [secularDefectScalar_zero, add_zero] at h

/-- `x(s) = D⁻¹ B(s)⁻¹ g` (ring inverse). -/
def secularRayFamily (B : ℝ → (O →L[ℂ] O)) (s : ℝ) : E :=
  D.symm (Ring.inverse (B s) g)

/-- `x' = -D⁻¹ R B' r`. -/
def secularRayFirst (B B1 : ℝ → (O →L[ℂ] O)) (s : ℝ) : E :=
  D.symm (-(Ring.inverse (B s) (B1 s (Ring.inverse (B s) g))))

/-- `x'' = D⁻¹ (2 R B' R B' r - R B'' r)`. -/
def secularRaySecond (B B1 B2 : ℝ → (O →L[ℂ] O)) (s : ℝ) : E :=
  D.symm ((2 : ℂ) •
      Ring.inverse (B s) (B1 s (Ring.inverse (B s) (B1 s (Ring.inverse (B s) g)))) -
    Ring.inverse (B s) (B2 s (Ring.inverse (B s) g)))

theorem hasDerivAt_ringInverse_apply_const [CompleteSpace O] {B : ℝ → (O →L[ℂ] O)}
    {B' : O →L[ℂ] O} {L : ℝ}
    (hB : HasDerivAt B B' L) (hu : IsUnit (B L)) (y : O) :
    HasDerivAt (fun s => Ring.inverse (B s) y)
      (-(Ring.inverse (B L) (B' (Ring.inverse (B L) y)))) L := by
  have h := hasDerivAt_complexCLM_apply_const_real (hasDerivAt_ringInverse_complexCLM hB hu) y
  have hm : ∀ (f k : O →L[ℂ] O) (z : O), (f * k) z = f (k z) := fun _ _ _ => rfl
  simpa [hm] using h

theorem hasDerivAt_secularRayFamily [CompleteSpace O] {B B1 : ℝ → (O →L[ℂ] O)} {L : ℝ}
    (hB : HasDerivAt B (B1 L) L) (hu : IsUnit (B L)) :
    HasDerivAt (secularRayFamily D g B) (secularRayFirst D g B B1 L) L := by
  let Dr : O →L[ℝ] E := (D.symm : O →L[ℂ] E).restrictScalars ℝ
  exact Dr.hasFDerivAt.comp_hasDerivAt L (hasDerivAt_ringInverse_apply_const hB hu g)

theorem hasDerivAt_secularRayFirst [CompleteSpace O] {B B1 B2 : ℝ → (O →L[ℂ] O)} {L : ℝ}
    (hB : HasDerivAt B (B1 L) L) (hB1 : HasDerivAt B1 (B2 L) L) (hu : IsUnit (B L)) :
    HasDerivAt (secularRayFirst D g B B1) (secularRaySecond D g B B1 B2 L) L := by
  have hr := hasDerivAt_ringInverse_apply_const hB hu g
  have hu1 := hasDerivAt_complexCLM_apply_real hB1 hr
  have hR := hasDerivAt_ringInverse_complexCLM hB hu
  have hin := hasDerivAt_complexCLM_apply_real hR hu1
  let Dr : O →L[ℝ] E := (D.symm : O →L[ℂ] E).restrictScalars ℝ
  have h := Dr.hasFDerivAt.comp_hasDerivAt L hin.neg
  unfold secularRayFirst secularRaySecond
  refine h.congr_deriv ?_
  have hm : ∀ (f k : O →L[ℂ] O) (y : O), (f * k) y = f (k y) := fun _ _ _ => rfl
  simp only [Dr, ContinuousLinearMap.coe_restrictScalars', hm, neg_apply,
    map_neg, map_add, map_sub, map_smul, ContinuousLinearEquiv.coe_coe]
  module


/-- `T(s) = H_s(x(s))`. -/
def secularScalarFamily (A : ℝ → (E →L[ℂ] E)) (B : ℝ → (O →L[ℂ] O))
    (s : ℝ) : ℂ :=
  secularDefectScalar D g (B s) (A s) (secularRayFamily D g B s)

/-- `T' = H'(x) + H(x')`. -/
def secularScalarFirst (A A1 : ℝ → (E →L[ℂ] E)) (B B1 : ℝ → (O →L[ℂ] O))
    (s : ℝ) : ℂ :=
  secularDefectScalar D g (B1 s) (A1 s) (secularRayFamily D g B s) +
    secularDefectScalar D g (B s) (A s) (secularRayFirst D g B B1 s)

/-- `T'' = H''(x) + 2 H'(x') + H(x'')`. -/
def secularScalarSecond (A A1 A2 : ℝ → (E →L[ℂ] E)) (B B1 B2 : ℝ → (O →L[ℂ] O))
    (s : ℝ) : ℂ :=
  secularDefectScalar D g (B2 s) (A2 s) (secularRayFamily D g B s) +
    2 * secularDefectScalar D g (B1 s) (A1 s) (secularRayFirst D g B B1 s) +
    secularDefectScalar D g (B s) (A s) (secularRaySecond D g B B1 B2 s)

theorem hasDerivAt_secularScalarFamily [CompleteSpace O] {A A1 : ℝ → (E →L[ℂ] E)}
    {B B1 : ℝ → (O →L[ℂ] O)} {L : ℝ}
    (hA : HasDerivAt A (A1 L) L) (hB : HasDerivAt B (B1 L) L) (hu : IsUnit (B L)) :
    HasDerivAt (secularScalarFamily D g A B) (secularScalarFirst D g A A1 B B1 L) L :=
  hasDerivAt_secularDefectScalar D g hB hA (hasDerivAt_secularRayFamily D g hB hu)

theorem hasDerivAt_secularScalarFirst [CompleteSpace O] {A A1 A2 : ℝ → (E →L[ℂ] E)}
    {B B1 B2 : ℝ → (O →L[ℂ] O)} {L : ℝ}
    (hA : HasDerivAt A (A1 L) L) (hA1 : HasDerivAt A1 (A2 L) L)
    (hB : HasDerivAt B (B1 L) L) (hB1 : HasDerivAt B1 (B2 L) L) (hu : IsUnit (B L)) :
    HasDerivAt (secularScalarFirst D g A A1 B B1)
      (secularScalarSecond D g A A1 A2 B B1 B2 L) L := by
  have h1 := hasDerivAt_secularDefectScalar D g hB1 hA1 (hasDerivAt_secularRayFamily D g hB hu)
  have h2 := hasDerivAt_secularDefectScalar D g hB hA (hasDerivAt_secularRayFirst D g hB hB1 hu)
  refine (h1.add h2).congr_deriv ?_
  unfold secularScalarSecond
  ring

/-- **Stationary identities.**  If `T'(L) = 0` then `H'(x) = H(D⁻¹ R B' r)`; if also
`T''(L) = 0` then `H''(x) = 2 H'(D⁻¹ R B' r) - H(D⁻¹(2 R B' R B' r - R B'' r))`. -/
theorem secularScalar_stationary
    {A A1 A2 : ℝ → (E →L[ℂ] E)} {B B1 B2 : ℝ → (O →L[ℂ] O)}
    {L : ℝ} (h1 : secularScalarFirst D g A A1 B B1 L = 0) :
    secularDefectScalar D g (B1 L) (A1 L) (secularRayFamily D g B L) =
        -secularDefectScalar D g (B L) (A L) (secularRayFirst D g B B1 L) ∧
      (secularScalarSecond D g A A1 A2 B B1 B2 L = 0 →
        secularDefectScalar D g (B2 L) (A2 L) (secularRayFamily D g B L) =
          -2 * secularDefectScalar D g (B1 L) (A1 L) (secularRayFirst D g B B1 L) -
            secularDefectScalar D g (B L) (A L) (secularRaySecond D g B B1 B2 L)) := by
  unfold secularScalarFirst at h1
  refine ⟨by linear_combination h1, fun h2 => ?_⟩
  unfold secularScalarSecond at h2
  linear_combination h2

end Abstract

section Canonical

variable (K : ℕ) (hK : 2 ≤ K)

/-- `A_s` as a real-parameter family of continuous operators. -/
abbrev canonicalEvenFamily (s : ℝ) :
    euclideanEvenBoundaryFlatSubspace K →L[ℂ] euclideanEvenBoundaryFlatSubspace K :=
  parityCompressedCanonicalCLM .even s K

abbrev canonicalEvenFirst (s : ℝ) :
    euclideanEvenBoundaryFlatSubspace K →L[ℂ] euclideanEvenBoundaryFlatSubspace K :=
  productionParityFirstJetCLM .even K s

abbrev canonicalEvenSecond (s : ℝ) :
    euclideanEvenBoundaryFlatSubspace K →L[ℂ] euclideanEvenBoundaryFlatSubspace K :=
  productionParitySecondJetCLM .even K s

/-- `B_s` as a real-parameter family of continuous operators. -/
abbrev canonicalOddFamily (s : ℝ) :
    euclideanOddBoundaryFlatSubspace K →L[ℂ] euclideanOddBoundaryFlatSubspace K :=
  parityCompressedCanonicalCLM .odd s K

abbrev canonicalOddFirst (s : ℝ) :
    euclideanOddBoundaryFlatSubspace K →L[ℂ] euclideanOddBoundaryFlatSubspace K :=
  productionParityFirstJetCLM .odd K s

abbrev canonicalOddSecond (s : ℝ) :
    euclideanOddBoundaryFlatSubspace K →L[ℂ] euclideanOddBoundaryFlatSubspace K :=
  productionParitySecondJetCLM .odd K s

/-- The centered-index map `D` as a continuous linear equivalence. -/
def canonicalIndexEquiv :
    euclideanEvenBoundaryFlatSubspace K ≃L[ℂ] euclideanOddBoundaryFlatSubspace K :=
  (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)).toContinuousLinearEquiv

/-- `H_L` is the defect scalar at `(B_L, A_L)`. -/
theorem secularDefectScalar_canonical (L : ℝ) (v : euclideanEvenBoundaryFlatSubspace K) :
    secularDefectScalar (canonicalIndexEquiv K hK) (oddCubicCompressionVector K)
        (canonicalOddFamily K L) (canonicalEvenFamily K L) v =
      cubicDefectFunctional L K v :=
  rfl

theorem isUnit_canonicalOddFamily {L : ℝ} (hpos : 0 < parityRayleighBottom .odd L K) :
    IsUnit (canonicalOddFamily K L) :=
  ⟨(oddCompressedCanonicalEquiv L K hpos).toContinuousLinearEquiv.toUnit, rfl⟩

theorem secularRayFamily_canonical {L : ℝ} (hpos : 0 < parityRayleighBottom .odd L K) :
    secularRayFamily (canonicalIndexEquiv K hK) (oddCubicCompressionVector K)
        (canonicalOddFamily K) L =
      canonicalResolventRay L K hK hpos := by
  have hu : canonicalOddFamily K L =
      ((oddCompressedCanonicalEquiv L K hpos).toContinuousLinearEquiv.toUnit :
        euclideanOddBoundaryFlatSubspace K →L[ℂ] euclideanOddBoundaryFlatSubspace K) := rfl
  unfold secularRayFamily
  rw [hu, Ring.inverse_unit]
  rfl


/-- The canonical secular scalar `T_K(s) = H_s(D⁻¹ B_s⁻¹ g)`. -/
def canonicalSecularScalar (s : ℝ) : ℂ :=
  secularScalarFamily (E := euclideanEvenBoundaryFlatSubspace K)
    (O := euclideanOddBoundaryFlatSubspace K) (canonicalIndexEquiv K hK)
    (oddCubicCompressionVector K)
    (canonicalEvenFamily K) (canonicalOddFamily K) s

/-- `T_K' = H'(x) + H(x')`, `x' = -D⁻¹ R B' r`. -/
def canonicalSecularScalarFirst (s : ℝ) : ℂ :=
  secularScalarFirst (E := euclideanEvenBoundaryFlatSubspace K)
    (O := euclideanOddBoundaryFlatSubspace K) (canonicalIndexEquiv K hK)
    (oddCubicCompressionVector K)
    (canonicalEvenFamily K) (canonicalEvenFirst K) (canonicalOddFamily K) (canonicalOddFirst K) s

/-- `T_K'' = H''(x) + 2 H'(x') + H(x'')`, `x'' = D⁻¹(2 R B' R B' r - R B'' r)`. -/
def canonicalSecularScalarSecond (s : ℝ) : ℂ :=
  secularScalarSecond (E := euclideanEvenBoundaryFlatSubspace K)
    (O := euclideanOddBoundaryFlatSubspace K) (canonicalIndexEquiv K hK)
    (oddCubicCompressionVector K)
    (canonicalEvenFamily K) (canonicalEvenFirst K) (canonicalEvenSecond K)
    (canonicalOddFamily K) (canonicalOddFirst K) (canonicalOddSecond K) s

/-- Where `λ_odd(L) > 0`, `T_K(L)` is the source moment of the resolvent ray, the
secular scalar of M74 (`1 - T_K(L) = det A_L / det B_L`). -/
theorem canonicalSecularScalar_eq {L : ℝ} (hL : 0 < L)
    (hpos : 0 < parityRayleighBottom .odd L K) :
    canonicalSecularScalar K hK L =
      explicitCanonicalSourceMoment L K (canonicalResolventRay L K hK hpos) := by
  unfold canonicalSecularScalar secularScalarFamily
  rw [secularRayFamily_canonical K hK hpos, secularDefectScalar_canonical,
    cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK]

/-- **M29 (Steps 61, 62).**  At every aperture `L > 0` with `λ_odd(L) > 0`, the
secular scalar is twice differentiable with
`T' = H'(x) + H(x')` and `T'' = H''(x) + 2 H'(x') + H(x'')`, where
`x = D⁻¹ R g`, `x' = -D⁻¹ R B' r`, `x'' = D⁻¹(2 R B' R B' r - R B'' r)`, `R = B_L⁻¹`,
`r = R g`, and `H', H''` are the defect scalars of the production first and second
jets.  No F04 hypothesis: only the merged compressed `C²` jets are used. -/
theorem canonicalSecularScalar_hasDerivAt {L : ℝ} (hL : 0 < L)
    (hpos : 0 < parityRayleighBottom .odd L K) :
    HasDerivAt (canonicalSecularScalar K hK) (canonicalSecularScalarFirst K hK L) L ∧
      HasDerivAt (canonicalSecularScalarFirst K hK) (canonicalSecularScalarSecond K hK L) L := by
  have hA : HasDerivAt (canonicalEvenFamily K) (canonicalEvenFirst K L) L :=
    hasDerivAt_parityCompressedCanonicalCLM_pos .even K hL
  have hB : HasDerivAt (canonicalOddFamily K) (canonicalOddFirst K L) L :=
    hasDerivAt_parityCompressedCanonicalCLM_pos .odd K hL
  have hA1 : HasDerivAt (canonicalEvenFirst K) (canonicalEvenSecond K L) L :=
    hasDerivAt_productionParityFirstJetCLM_pos .even K hL
  have hB1 : HasDerivAt (canonicalOddFirst K) (canonicalOddSecond K L) L :=
    hasDerivAt_productionParityFirstJetCLM_pos .odd K hL
  have hu := isUnit_canonicalOddFamily K hpos
  exact ⟨hasDerivAt_secularScalarFamily _ _ hA hB hu,
    hasDerivAt_secularScalarFirst _ _ hA hA1 hB hB1 hu⟩

include hK in
/-- **M29 (Step 61), `H_L` is `C²` on the whole positive axis, seams included.**  For
fixed `v`, `s ↦ H_s(v) = ⟪g, (B_s D - D A_s) v⟫ / ⟪g, g⟫` is `C²` on `(0, ∞)`, and its
derivative is the defect scalar of the production first jets. -/
theorem cubicDefectFunctional_contDiffOn (v : euclideanEvenBoundaryFlatSubspace K) :
    ContDiffOn ℝ 2 (fun s => cubicDefectFunctional s K v) (Set.Ioi 0) := by
  set D := canonicalIndexEquiv K hK
  set g := oddCubicCompressionVector K
  have hB : ContDiffOn ℝ 2 (canonicalOddFamily K) (Set.Ioi 0) :=
    canonicalParityCompressedC2_proved .odd K
  have hA : ContDiffOn ℝ 2 (canonicalEvenFamily K) (Set.Ioi 0) :=
    canonicalParityCompressedC2_proved .even K
  let Ψb :
      (euclideanOddBoundaryFlatSubspace K →L[ℂ] euclideanOddBoundaryFlatSubspace K) →L[ℝ]
        ℂ :=
    ((innerSL ℂ g).comp (ContinuousLinearMap.apply ℂ _ (D v))).restrictScalars ℝ
  let Ψa :
      (euclideanEvenBoundaryFlatSubspace K →L[ℂ] euclideanEvenBoundaryFlatSubspace K) →L[ℝ]
        ℂ :=
    ((innerSL ℂ g).comp ((D : euclideanEvenBoundaryFlatSubspace K →L[ℂ] _).comp
      (ContinuousLinearMap.apply ℂ _ v))).restrictScalars ℝ
  have h := ((Ψb.contDiff.comp_contDiffOn hB).sub (Ψa.contDiff.comp_contDiffOn hA)).div_const
    (inner ℂ g g)
  refine h.congr fun s _ => ?_
  rw [← secularDefectScalar_canonical K hK]
  simp only [secularDefectScalar, Ψb, Ψa, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, innerSL_apply_apply, inner_sub_right]
  rfl

theorem cubicDefectFunctional_hasDerivAt {L : ℝ} (hL : 0 < L)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    HasDerivAt (fun s => cubicDefectFunctional s K v)
      (secularDefectScalar (canonicalIndexEquiv K hK) (oddCubicCompressionVector K)
        (canonicalOddFirst K L) (canonicalEvenFirst K L) v) L := by
  have h := hasDerivAt_secularDefectScalar_const (E := euclideanEvenBoundaryFlatSubspace K)
    (O := euclideanOddBoundaryFlatSubspace K) (canonicalIndexEquiv K hK)
    (oddCubicCompressionVector K)
    (hasDerivAt_parityCompressedCanonicalCLM_pos .odd K hL)
    (hasDerivAt_parityCompressedCanonicalCLM_pos .even K hL) v
  have hf : (fun s => cubicDefectFunctional s K v) = fun s =>
      secularDefectScalar (canonicalIndexEquiv K hK) (oddCubicCompressionVector K)
        (canonicalOddFamily K s) (canonicalEvenFamily K s) v :=
    funext fun s => (secularDefectScalar_canonical K hK s v).symm
  rw [hf]
  exact h

/-- `H_L` on the canonical carriers, with `D` the centered-index map and `g` the
compressed cubic vector. -/
abbrev canonicalDefect
    (b : euclideanOddBoundaryFlatSubspace K →L[ℂ] euclideanOddBoundaryFlatSubspace K)
    (a : euclideanEvenBoundaryFlatSubspace K →L[ℂ] euclideanEvenBoundaryFlatSubspace K)
    (z : euclideanEvenBoundaryFlatSubspace K) : ℂ :=
  secularDefectScalar (E := euclideanEvenBoundaryFlatSubspace K)
    (O := euclideanOddBoundaryFlatSubspace K) (canonicalIndexEquiv K hK)
    (oddCubicCompressionVector K) b a z

/-- The resolvent ray `x_s = D⁻¹ B_s⁻¹ g` and its jets `x'`, `x''`. -/
abbrev canonicalRay (s : ℝ) : euclideanEvenBoundaryFlatSubspace K :=
  secularRayFamily (E := euclideanEvenBoundaryFlatSubspace K)
    (O := euclideanOddBoundaryFlatSubspace K) (canonicalIndexEquiv K hK)
    (oddCubicCompressionVector K) (canonicalOddFamily K) s

abbrev canonicalRayFirst (s : ℝ) : euclideanEvenBoundaryFlatSubspace K :=
  secularRayFirst (E := euclideanEvenBoundaryFlatSubspace K)
    (O := euclideanOddBoundaryFlatSubspace K) (canonicalIndexEquiv K hK)
    (oddCubicCompressionVector K) (canonicalOddFamily K) (canonicalOddFirst K) s

abbrev canonicalRaySecond (s : ℝ) : euclideanEvenBoundaryFlatSubspace K :=
  secularRaySecond (E := euclideanEvenBoundaryFlatSubspace K)
    (O := euclideanOddBoundaryFlatSubspace K) (canonicalIndexEquiv K hK)
    (oddCubicCompressionVector K) (canonicalOddFamily K) (canonicalOddFirst K)
    (canonicalOddSecond K) s

/-- **M29, stationary identities.**  Where `T'(L) = 0`,
`H'(x) = -H(x') = H(D⁻¹ R B' r)`; if also `T''(L) = 0`,
`H''(x) = -2 H'(x') - H(x'') = 2 H'(D⁻¹ R B' r) - H(D⁻¹(2 R B' R B' r - R B'' r))`.
These are consequences of stationarity, not a sign for the third derivative. -/
theorem canonicalSecularScalar_stationary {L : ℝ}
    (h1 : canonicalSecularScalarFirst K hK L = 0) :
    canonicalDefect K hK (canonicalOddFirst K L) (canonicalEvenFirst K L) (canonicalRay K hK L) =
        -canonicalDefect K hK (canonicalOddFamily K L) (canonicalEvenFamily K L)
          (canonicalRayFirst K hK L) ∧
      (canonicalSecularScalarSecond K hK L = 0 →
        canonicalDefect K hK (canonicalOddSecond K L) (canonicalEvenSecond K L)
            (canonicalRay K hK L) =
          -2 * canonicalDefect K hK (canonicalOddFirst K L) (canonicalEvenFirst K L)
              (canonicalRayFirst K hK L) -
            canonicalDefect K hK (canonicalOddFamily K L) (canonicalEvenFamily K L)
              (canonicalRaySecond K hK L)) := by
  unfold canonicalSecularScalarFirst secularScalarFirst at h1
  unfold canonicalSecularScalarSecond secularScalarSecond
  exact ⟨by linear_combination h1, fun h2 => by linear_combination h2⟩

end Canonical

end Zeta23.CCM

#print axioms Zeta23.CCM.hasDerivAt_complexCLM_apply_real
#print axioms Zeta23.CCM.hasDerivAt_ringInverse_complexCLM
#print axioms Zeta23.CCM.hasDerivAt_secularDefectScalar
#print axioms Zeta23.CCM.hasDerivAt_secularDefectScalar_const
#print axioms Zeta23.CCM.hasDerivAt_secularRayFamily
#print axioms Zeta23.CCM.hasDerivAt_secularRayFirst
#print axioms Zeta23.CCM.hasDerivAt_secularScalarFamily
#print axioms Zeta23.CCM.hasDerivAt_secularScalarFirst
#print axioms Zeta23.CCM.secularScalar_stationary
#print axioms Zeta23.CCM.secularDefectScalar_canonical
#print axioms Zeta23.CCM.isUnit_canonicalOddFamily
#print axioms Zeta23.CCM.secularRayFamily_canonical
#print axioms Zeta23.CCM.canonicalSecularScalar_eq
#print axioms Zeta23.CCM.canonicalSecularScalar_hasDerivAt
#print axioms Zeta23.CCM.cubicDefectFunctional_contDiffOn
#print axioms Zeta23.CCM.cubicDefectFunctional_hasDerivAt
#print axioms Zeta23.CCM.canonicalSecularScalar_stationary
