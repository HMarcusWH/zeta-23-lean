import Zeta23.OPICARound4.RegularCells.NativeParityPrimeAnchor
import Zeta23.OPICARound4.RegularCells.NativeParityMatrixPencils

noncomputable section
namespace Zeta23.OPICARound4.NativeParityPencils
open CCM RegularCells NativeParitySeparation PrimeSourceLaurent PrimeSourceGerms Filter
open scoped Topology

def nativeFormalSeparationDet (Q K : ℕ) (z : ℂ) (X : boundedPrimeSet Q → ℂˣ) : ℂ :=
  (formalRawFrameSylvester Q K (coordinateFrame .even K) (coordinateFrame .odd K) z X).det

def nativeActualSeparationDet (Q K : ℕ) (z : ℂ) : ℂ :=
  nativeFormalSeparationDet Q K z (primePhaseUnits (boundedPrimeSet Q) z)

theorem exists_native_formal_separation_anchor (Q K : ℕ) (hQ : 2 ≤ Q) (hK : 3 ≤ K) :
    ∃ X : boundedPrimeSet Q → ℂˣ, nativeFormalSeparationDet Q K 0 X ≠ 0 := by
  obtain ⟨X,hX⟩ := exists_native_formal_pencil_injective Q K hQ hK
  exact ⟨X,(coordinateFrame_sylvester_det_iff Q K 0 X).mpr hX⟩

theorem nativeActualSeparationDet_germ_nonzero (Q K : ℕ) (hQ : 2 ≤ Q) (hK : 3 ≤ K) :
    ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ), nativeActualSeparationDet Q K z = 0 := by
  obtain ⟨X,hX⟩ := exists_native_formal_separation_anchor Q K hQ hK
  exact actual_sylvester_germ_nonzero_of_formal_anchor Q K
    (coordinateFrame .even K) (coordinateFrame .odd K) X hX

theorem analyticOnNhd_nativeActualSeparationDet (Q K : ℕ) :
    AnalyticOnNhd ℂ (nativeActualSeparationDet Q K) complexFrozenSourceDomain :=
  analyticOnNhd_actualRawFrameSylvesterDet Q K (coordinateFrame .even K) (coordinateFrame .odd K)

/-- The actual prime path has a nonzero full-frame separation determinant in
every positive open interval. The source horizon and finite cutoff are fixed first. -/
theorem exists_nativeActualSeparationDet_nonzero_in_open_positive (Q K : ℕ)
    (hQ : 2 ≤ Q) (hK : 3 ≤ K) {J : Set ℝ}
    (hJo : IsOpen J) (hJn : J.Nonempty) (hJp : J ⊆ Set.Ioi 0) :
    ∃ L ∈ J, nativeActualSeparationDet Q K (L : ℂ) ≠ 0 :=
  exists_source_nonzero_in_open_positive_of_germ _
    (analyticOnNhd_nativeActualSeparationDet Q K)
    (nativeActualSeparationDet_germ_nonzero Q K hQ hK) hJo hJn hJp

theorem exists_finite_nativeActualSeparationDet_nonzero (Q : ℕ) (hQ : 2 ≤ Q)
    (s : Finset ℕ) (hs : ∀ K ∈ s, 3 ≤ K) {J : Set ℝ}
    (hJo : IsOpen J) (hJn : J.Nonempty) (hJp : J ⊆ Set.Ioi 0) :
    ∃ L ∈ J, ∀ K ∈ s, nativeActualSeparationDet Q K (L : ℂ) ≠ 0 :=
  exists_finite_source_nonzero_in_open_positive_of_germ s (nativeActualSeparationDet Q)
    (fun K _ => analyticOnNhd_nativeActualSeparationDet Q K)
    (fun K hK => nativeActualSeparationDet_germ_nonzero Q K hQ (hs K hK)) hJo hJn hJp

end Zeta23.OPICARound4.NativeParityPencils
