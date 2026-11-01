import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Determinant

noncomputable section
namespace Zeta23.OPICARound4.NativeParitySeparation
open Module.End
open scoped ComplexConjugate

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

def nativeSylvester (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) :
    (E →ₗ[ℂ] F) →ₗ[ℂ] (E →ₗ[ℂ] F) where
  toFun X := B.comp X - X.comp A
  map_add' X Y := by ext x; simp [sub_eq_add_neg]; abel
  map_smul' c X := by ext x; simp [smul_sub]

theorem nativeSylvester_injective_of_disjoint
    (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) (hA : A.IsSymmetric)
    (hsep : ∀ lam : ℂ, HasEigenvalue A lam → ¬ HasEigenvalue B lam) :
    Function.Injective (nativeSylvester A B) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  apply (hA.eigenvectorBasis rfl).toBasis.ext
  intro i
  change X (hA.eigenvectorBasis rfl i) = 0
  by_contra hn
  have he : B (X (hA.eigenvectorBasis rfl i)) =
      (hA.eigenvalues rfl i : ℂ) • X (hA.eigenvectorBasis rfl i) := by
    have hx := congrArg (fun Y : E →ₗ[ℂ] F => Y (hA.eigenvectorBasis rfl i)) hX
    change B (X (hA.eigenvectorBasis rfl i)) - X (A (hA.eigenvectorBasis rfl i)) = 0 at hx
    rw [hA.apply_eigenvectorBasis, map_smul] at hx
    exact sub_eq_zero.mp hx
  exact hsep _ (hA.hasEigenvalue_eigenvalues rfl i)
    (hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr he, hn⟩)

theorem nativeSylvester_not_injective_of_common
    (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) (hA : A.IsSymmetric)
    (lam : ℂ) (ha : HasEigenvalue A lam) (hb : HasEigenvalue B lam) :
    ¬ Function.Injective (nativeSylvester A B) := by
  obtain ⟨u, hu, hu0⟩ := ha.exists_hasEigenvector
  obtain ⟨v, hv, hv0⟩ := hb.exists_hasEigenvector
  have hua := mem_eigenspace_iff.mp hu
  have hvb := mem_eigenspace_iff.mp hv
  let X : E →ₗ[ℂ] F := (innerₛₗ ℂ u).smulRight v
  have hX0 : X ≠ 0 := by
    intro hz
    have h := congrArg (fun Y : E →ₗ[ℂ] F => Y u) hz
    change inner ℂ u u • v = 0 at h
    exact (inner_self_ne_zero.mpr hu0) ((smul_eq_zero.mp h).resolve_right hv0)
  have hX : nativeSylvester A B X = 0 := by
    ext x
    change B (inner ℂ u x • v) - inner ℂ u (A x) • v = 0
    rw [map_smul, hvb, ← hA u x, hua, inner_smul_left,
      hA.conj_eigenvalue_eq_self ha, smul_smul]
    rw [mul_comm]
    exact sub_self _
  intro hinj
  exact hX0 (hinj (by simpa using hX))

theorem nativeSylvester_injective_iff_disjoint
    (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) (hA : A.IsSymmetric) :
    Function.Injective (nativeSylvester A B) ↔
      ∀ lam : ℂ, HasEigenvalue A lam → ¬ HasEigenvalue B lam := by
  constructor
  · intro hi lam ha hb
    exact nativeSylvester_not_injective_of_common A B hA lam ha hb hi
  · exact nativeSylvester_injective_of_disjoint A B hA

theorem nativeSylvester_det_ne_zero_iff_disjoint
    (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) (hA : A.IsSymmetric) :
    LinearMap.det (nativeSylvester A B) ≠ 0 ↔
      ∀ lam : ℂ, HasEigenvalue A lam → ¬ HasEigenvalue B lam := by
  rw [ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
  exact nativeSylvester_injective_iff_disjoint A B hA

/-- The complete Gram factors are retained; no inverse is introduced. -/
def nativePencilSylvester (He Ge : E →ₗ[ℂ] E) (Ho Go : F →ₗ[ℂ] F) :
    (E →ₗ[ℂ] F) →ₗ[ℂ] (E →ₗ[ℂ] F) where
  toFun X := (Ho.comp X).comp Ge - (Go.comp X).comp He
  map_add' X Y := by ext x; simp [sub_eq_add_neg]; abel
  map_smul' c X := by ext x; simp [smul_sub]

/-- A shared scalar cannot separate spectra, even in a nonorthonormal frame. -/
theorem nativePencilSylvester_common_scalar
    (He Ge : E →ₗ[ℂ] E) (Ho Go : F →ₗ[ℂ] F) (c : ℂ) :
    nativePencilSylvester (He + c • Ge) Ge (Ho + c • Go) Go =
      nativePencilSylvester He Ge Ho Go := by
  ext X x
  simp [nativePencilSylvester, map_add, map_smul]

theorem nativePencilSylvester_scale
    (He Ge : E →ₗ[ℂ] E) (Ho Go : F →ₗ[ℂ] F) (c : ℂ) :
    nativePencilSylvester (c • He) Ge (c • Ho) Go =
      c • nativePencilSylvester He Ge Ho Go := by
  ext X x
  simp [nativePencilSylvester, map_smul, smul_sub]

theorem nativePencilSylvester_identity_gram
    (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) :
    nativePencilSylvester A LinearMap.id B LinearMap.id = nativeSylvester A B := by
  ext X x
  rfl

section Frame
variable {E' F' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [FiniteDimensional ℂ E'] [NormedAddCommGroup F'] [InnerProductSpace ℂ F']
  [FiniteDimensional ℂ F']

/-- The actual congruence factors remain on both sides. Taking `V=U*` and
`Y=W*` gives the native Gram pencil; no unitary frame is assumed. -/
theorem nativePencilSylvester_frame_factor
    (A : E' →ₗ[ℂ] E') (B : F' →ₗ[ℂ] F')
    (U : E →ₗ[ℂ] E') (V : E' →ₗ[ℂ] E)
    (W : F →ₗ[ℂ] F') (Y : F' →ₗ[ℂ] F) (X : E →ₗ[ℂ] F) :
    nativePencilSylvester ((V.comp A).comp U) (V.comp U)
      ((Y.comp B).comp W) (Y.comp W) X =
      (Y.comp (nativeSylvester A B ((W.comp X).comp V))).comp U := by
  ext x
  simp [nativePencilSylvester, nativeSylvester, map_sub]

theorem nativePencilSylvester_frame_injective_of_disjoint
    (A : E' →ₗ[ℂ] E') (B : F' →ₗ[ℂ] F') (hA : A.IsSymmetric)
    (U : E ≃ₗ[ℂ] E') (V : E' ≃ₗ[ℂ] E)
    (W : F ≃ₗ[ℂ] F') (Y : F' ≃ₗ[ℂ] F)
    (hsep : ∀ lam : ℂ, HasEigenvalue A lam → ¬ HasEigenvalue B lam) :
    Function.Injective (nativePencilSylvester
      ((V.toLinearMap.comp A).comp U.toLinearMap) (V.toLinearMap.comp U.toLinearMap)
      ((Y.toLinearMap.comp B).comp W.toLinearMap) (Y.toLinearMap.comp W.toLinearMap)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  rw [nativePencilSylvester_frame_factor] at hX
  have hs : nativeSylvester A B ((W.toLinearMap.comp X).comp V.toLinearMap) = 0 := by
    ext x
    obtain ⟨u, rfl⟩ := U.surjective x
    apply Y.injective
    have hu := congrArg (fun Z : E →ₗ[ℂ] F => Z u) hX
    simpa using hu
  have hz : (W.toLinearMap.comp X).comp V.toLinearMap = 0 :=
    (nativeSylvester_injective_of_disjoint A B hA hsep) (by simpa using hs)
  ext x
  obtain ⟨u, rfl⟩ := V.surjective x
  apply W.injective
  have hu := congrArg (fun Z : E' →ₗ[ℂ] F' => Z u) hz
  simpa using hu

theorem nativePencilSylvester_frame_disjoint_of_injective
    (A : E' →ₗ[ℂ] E') (B : F' →ₗ[ℂ] F') (hA : A.IsSymmetric)
    (U : E ≃ₗ[ℂ] E') (V : E' ≃ₗ[ℂ] E)
    (W : F ≃ₗ[ℂ] F') (Y : F' ≃ₗ[ℂ] F)
    (hi : Function.Injective (nativePencilSylvester
      ((V.toLinearMap.comp A).comp U.toLinearMap) (V.toLinearMap.comp U.toLinearMap)
      ((Y.toLinearMap.comp B).comp W.toLinearMap) (Y.toLinearMap.comp W.toLinearMap))) :
    ∀ lam : ℂ, HasEigenvalue A lam → ¬ HasEigenvalue B lam := by
  apply (nativeSylvester_injective_iff_disjoint A B hA).mp
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Z hZ
  let X : E →ₗ[ℂ] F := (W.symm.toLinearMap.comp Z).comp V.symm.toLinearMap
  have ht : (W.toLinearMap.comp X).comp V.toLinearMap = Z := by
    ext x
    simp [X]
  have hx : nativePencilSylvester
      ((V.toLinearMap.comp A).comp U.toLinearMap) (V.toLinearMap.comp U.toLinearMap)
      ((Y.toLinearMap.comp B).comp W.toLinearMap) (Y.toLinearMap.comp W.toLinearMap) X = 0 := by
    rw [nativePencilSylvester_frame_factor, ht, hZ]
    ext x
    simp
  have hx0 : X = 0 := hi (by simpa using hx)
  ext x
  have h := congrArg (fun T : E →ₗ[ℂ] F => W (T (V x))) hx0
  simpa [X] using h

theorem nativePencilSylvester_frame_det_ne_zero_iff_disjoint
    (A : E' →ₗ[ℂ] E') (B : F' →ₗ[ℂ] F') (hA : A.IsSymmetric)
    (U : E ≃ₗ[ℂ] E') (V : E' ≃ₗ[ℂ] E)
    (W : F ≃ₗ[ℂ] F') (Y : F' ≃ₗ[ℂ] F) :
    LinearMap.det (nativePencilSylvester
      ((V.toLinearMap.comp A).comp U.toLinearMap) (V.toLinearMap.comp U.toLinearMap)
      ((Y.toLinearMap.comp B).comp W.toLinearMap) (Y.toLinearMap.comp W.toLinearMap)) ≠ 0 ↔
      ∀ lam : ℂ, HasEigenvalue A lam → ¬ HasEigenvalue B lam := by
  rw [ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
  exact ⟨nativePencilSylvester_frame_disjoint_of_injective A B hA U V W Y,
    nativePencilSylvester_frame_injective_of_disjoint A B hA U V W Y⟩

end Frame

end Zeta23.OPICARound4.NativeParitySeparation
