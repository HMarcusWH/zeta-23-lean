import Zeta23.CCM.FirstCrossingProductionCurvatureBridge
import Zeta23.CCM.FirstCrossingInheritedStationarity

noncomputable section

namespace Zeta23.CCM

open Complex

/-!
# Post-#281 generated strict-even frontier

This module assembles the exact generated global contact with a normalized
strict-even zero mode.  It proves the first-order/stationary split and
constructs the stationary response in the zero-first-variation branch.

The arithmetic curvature identity and the outgoing-contact saturation
necessity remain separately visible.  They are not smuggled into the state
constructor.
-/

/-- Actual strict-even data at the selected cutoff of a generated global
first-crossing state. -/
structure GeneratedStrictEvenContact where
  generated : GeneratedGlobalFirstCrossing
  selected_even : generated.shell.p = .even
  z : euclideanEvenBoundaryFlatSubspace (generated.shell.k + 1)
  z_ne : z ≠ 0
  z_norm : ‖z‖ = 1
  z_kernel :
    evenCompressedCanonical generated.shell.Lstar
      (generated.shell.k + 1) z = 0
  odd_positive :
    0 < parityRayleighBottom .odd generated.shell.Lstar
      (generated.shell.k + 1)

/-- Selected cutoff is nontrivial. -/
theorem GeneratedStrictEvenContact.two_le_K
    (c : GeneratedStrictEvenContact) :
    2 ≤ c.generated.shell.k + 1 := by
  have hk : 1 ≤ c.generated.shell.k :=
    le_trans c.generated.shell.one_le_n c.generated.shell.n_le_k
  omega

/-- Contact aperture is positive. -/
theorem GeneratedStrictEvenContact.Lstar_pos
    (c : GeneratedStrictEvenContact) :
    0 < c.generated.shell.Lstar :=
  lt_trans c.generated.shell.Lsmall_pos
    c.generated.shell.Lsmall_lt_Lstar

/-- The selected even parity bottom is exactly zero. -/
theorem GeneratedStrictEvenContact.evenGround_zero
    (c : GeneratedStrictEvenContact) :
    parityRayleighBottom .even c.generated.shell.Lstar
      (c.generated.shell.k + 1) = 0 := by
  have hsel :
      parityRayleighBottom c.generated.shell.p c.generated.shell.Lstar
          (c.generated.shell.k + 1) = 0 := by
    simpa [paritySuccessorGround] using
      c.generated.shell.plateau_zero
        c.generated.shell.k
        c.generated.shell.n_le_k
        c.generated.shell.k_le_N
  simpa [c.selected_even] using hsel

/-- A generated even-strict branch supplies its own nonzero normalized even
kernel representative; callers do not have to inject an unrelated vector. -/
theorem GeneratedGlobalFirstCrossing.exists_generatedStrictEvenContact_of_evenStrict
    (g : GeneratedGlobalFirstCrossing)
    (heven :
      parityRayleighBottom .even g.shell.Lstar (g.shell.k + 1) = 0)
    (hodd :
      0 < parityRayleighBottom .odd g.shell.Lstar (g.shell.k + 1)) :
    ∃ c : GeneratedStrictEvenContact, c.generated = g := by
  have hk : 1 ≤ g.shell.k :=
    le_trans g.shell.one_le_n g.shell.n_le_k
  have hp : g.shell.p = .even := by
    cases hpg : g.shell.p with
    | even => rfl
    | odd =>
        have hsel :
            parityRayleighBottom .odd g.shell.Lstar (g.shell.k + 1) = 0 := by
          have hzero :=
            g.shell.plateau_zero g.shell.k g.shell.n_le_k g.shell.k_le_N
          simpa [paritySuccessorGround, hpg] using hzero
        linarith
  have hstrict :
      parityRayleighBottom .even g.shell.Lstar (g.shell.k + 1) <
        parityRayleighBottom .odd g.shell.Lstar (g.shell.k + 1) := by
    rw [heven]
    exact hodd
  have hLstar : 0 < g.shell.Lstar :=
    lt_trans g.shell.Lsmall_pos g.shell.Lsmall_lt_Lstar
  obtain ⟨z0, hz0ne, hz0eig, _hsourceNe, _hsourceGap⟩ :=
    exists_evenGround_source_gap_bound_of_strict
      hLstar g.shell.k hk hstrict
  have hz0ker :
      evenCompressedCanonical g.shell.Lstar (g.shell.k + 1) z0 = 0 := by
    change
      evenCompressedCanonical g.shell.Lstar (g.shell.k + 1) z0 =
        (parityRayleighBottom .even g.shell.Lstar
          (g.shell.k + 1) : ℂ) • z0 at hz0eig
    rw [heven] at hz0eig
    have hzeroCast : ((0 : ℝ) : ℂ) = 0 := by
      norm_num
    rw [hzeroCast, zero_smul] at hz0eig
    exact hz0eig
  let z : euclideanEvenBoundaryFlatSubspace (g.shell.k + 1) :=
    (‖z0‖⁻¹ : ℂ) • z0
  have hz0coe :
      (z0 : EuclideanSpace ℂ (Fin (2 * (g.shell.k + 1) + 1))) ≠ 0 := by
    intro h
    apply hz0ne
    apply Subtype.ext
    simpa using h
  have hznorm : ‖z‖ = 1 := by
    dsimp [z]
    exact norm_smul_inv_norm hz0coe
  have hzne : z ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hznorm
    norm_num at hznorm
  have hzker :
      evenCompressedCanonical g.shell.Lstar (g.shell.k + 1) z = 0 := by
    dsimp [z]
    rw [map_smul, hz0ker, smul_zero]
  let c : GeneratedStrictEvenContact := {
    generated := g
    selected_even := hp
    z := z
    z_ne := hzne
    z_norm := hznorm
    z_kernel := hzker
    odd_positive := hodd
  }
  exact ⟨c, rfl⟩

/-- First-order vs stationary generated-contact frontier. -/
inductive GeneratedStrictEvenVariationBranch
    (c : GeneratedStrictEvenContact) : Type
  | firstOrder
      (hneg :
        productionContactFirstVariation .even
          c.generated.shell.Lstar (c.generated.shell.k + 1) c.z < 0)
  | stationary
      (hzero :
        productionContactFirstVariation .even
          c.generated.shell.Lstar (c.generated.shell.k + 1) c.z = 0)
      (w : euclideanEvenBoundaryFlatSubspace (c.generated.shell.k + 1))
      (hperp : inner ℂ c.z w = 0)
      (hresponse :
        evenCompressedCanonical c.generated.shell.Lstar
            (c.generated.shell.k + 1) w =
          -(evenProductionApertureFirst
            c.generated.shell.Lstar (c.generated.shell.k + 1) c.z))

/-- Generated contact forces J1 <= 0 once the exact fixed-vector derivative
realization is supplied. -/
theorem GeneratedStrictEvenContact.firstVariation_nonpos
    (c : GeneratedStrictEvenContact)
    (hrealized :
      ProductionContactFirstVariationRealized .even
        c.generated.shell.Lstar (c.generated.shell.k + 1) c.z) :
    productionContactFirstVariation .even
      c.generated.shell.Lstar (c.generated.shell.k + 1) c.z ≤ 0 := by
  exact c.generated.firstVariation_nonpos_of_kernel
    .even c.z c.z_kernel hrealized

/-- Headline branch split: either the actual production first variation is
strictly negative, or it is stationary and the unique perpendicular response
is constructed. -/
theorem GeneratedStrictEvenContact.frontier
    (c : GeneratedStrictEvenContact)
    (hoperator :
      EvenProductionContactFirstOperatorRealized
        c.generated.shell.Lstar (c.generated.shell.k + 1))
    (hrealized :
      ProductionContactFirstVariationRealized .even
        c.generated.shell.Lstar (c.generated.shell.k + 1) c.z) :
    Nonempty (GeneratedStrictEvenVariationBranch c) := by
  have _hactual := hoperator c.z
  have hnonpos := c.firstVariation_nonpos hrealized
  rcases lt_or_eq_of_le hnonpos with hneg | hzero
  · exact ⟨.firstOrder hneg⟩
  · let w :=
      stationaryEvenResponse
        c.Lstar_pos
        (c.generated.shell.k + 1) c.two_le_K
        c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hoperator hzero
    have hspec :=
      stationaryEvenResponse_spec
        c.Lstar_pos
        (c.generated.shell.k + 1) c.two_le_K
        c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hoperator hzero
    exact ⟨.stationary hzero w hspec.1 hspec.2⟩

/-- Exact positive source value at every generated strict-even contact. -/
theorem GeneratedStrictEvenContact.sourceValue_pos
    (c : GeneratedStrictEvenContact) :
    0 < productionStrictEvenSourceValue
      c.generated.shell.Lstar (c.generated.shell.k + 1) c.z := by
  exact productionStrictEvenSourceValue_pos_of_even_zero_ground_strict
    c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K c.z c.z_ne
    c.evenGround_zero c.z_kernel c.odd_positive

/-- Stationary arithmetic saturation endpoint for the concrete response.  The
two hypotheses are intentionally the exact remaining theorem obligations:
actual production differentiation and outgoing-contact zero curvature. -/
theorem GeneratedStrictEvenContact.stationary_saturation_frontier
    (c : GeneratedStrictEvenContact)
    (hc2 :
      EvenProductionContactC2Realized
        c.generated.shell.Lstar (c.generated.shell.k + 1))
    (hstationary :
      productionContactFirstVariation .even
        c.generated.shell.Lstar (c.generated.shell.k + 1) c.z = 0)
    (hbridge :
      ProductionContactCurvatureArithmeticIdentity
        c.generated.shell.Lstar (c.generated.shell.k + 1) c.z
        (stationaryEvenResponse
          c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
          c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hc2.1 hstationary))
    (hkappa :
      productionContactOptimizedCurvature
        c.generated.shell.Lstar (c.generated.shell.k + 1) c.z
        (stationaryEvenResponse
          c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
          c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hc2.1 hstationary) = 0) :
    productionContactRemainderValue
        c.generated.shell.Lstar (c.generated.shell.k + 1) c.z
        (stationaryEvenResponse
          c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
          c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hc2.1 hstationary) =
      (2 * Real.pi) ^ 2 / c.generated.shell.Lstar ^ 2 *
        productionStrictEvenSourceValue
          c.generated.shell.Lstar (c.generated.shell.k + 1) c.z := by
  have _hfirst := hc2.1 c.z
  have _hsecond := hc2.2 c.z
  exact
    (productionContactOptimizedCurvature_zero_iff
      c.Lstar_pos (by omega : 1 ≤ c.generated.shell.k + 1) hbridge).mp hkappa

/-- Production first variation no longer needs a supplied realization witness. -/
theorem GeneratedStrictEvenContact.firstVariation_nonpos_production
    (c : GeneratedStrictEvenContact) :
    productionContactFirstVariation .even c.generated.shell.Lstar
      (c.generated.shell.k+1) c.z ≤ 0 := by
  have hC2 := canonicalEvenCompressedC2_proved (c.generated.shell.k+1)
  have hreal :
      ProductionContactFirstVariationRealized .even
        c.generated.shell.Lstar (c.generated.shell.k+1) c.z := by
    exact
      ((hC2 c.generated.shell.Lstar c.Lstar_pos).differentiable le_rfl).hasDerivAt
  exact c.generated.firstVariation_nonpos_of_kernel .even c.z c.z_kernel hreal

/-- Inherited strict-even contacts are stationary; transverse crossing remains
only in the fresh-born branch. -/
theorem GeneratedStrictEvenContact.firstVariation_eq_zero_of_inherited
    (c : GeneratedStrictEvenContact)
    (hinh : c.generated.shell.n < c.generated.shell.k) :
    productionContactFirstVariation .even c.generated.shell.Lstar
      (c.generated.shell.k+1) c.z = 0 := by
  have hseed :=
    c.generated.inheritedSeed_firstVariation_zero hinh
  have hline :=
    strictEven_zeroKernel_is_line c.Lstar_pos (c.generated.shell.k+1)
      c.two_le_K c.z c.z_ne c.z_kernel c.odd_positive
      (parityPlateauExtend c.generated.shell.p c.generated.shell.n_le_k
        c.generated.shell.seed)
      (by
        simpa [c.selected_even] using
          c.generated.shell.extended_kernel c.generated.shell.k
            c.generated.shell.n_le_k c.generated.shell.k_le_N)
  obtain ⟨a,ha⟩ := hline
  have ha0 : a ≠ 0 := by
    intro h
    rw [h,zero_smul] at ha
    exact parityPlateauExtend_ne_zero _ _ c.generated.shell.seed
      c.generated.shell.seed_ne (by simpa [ha])
  simpa [inheritedSelectedEnergy,ha,ha0] using hseed

/-- Production-authoritative branch type.  Unlike the historical #282 branch,
the stationary response equation is stated using the compressed-first
derivative and therefore does not silently identify it with the legacy
entrywise candidate at a seam. -/
inductive GeneratedStrictEvenProductionBranch
    (c : GeneratedStrictEvenContact) : Type
  | firstOrder
      (hneg :
        productionContactFirstVariation .even
          c.generated.shell.Lstar (c.generated.shell.k + 1) c.z < 0)
  | stationary
      (hzero :
        productionContactFirstVariation .even
          c.generated.shell.Lstar (c.generated.shell.k + 1) c.z = 0)
      (w : euclideanEvenBoundaryFlatSubspace (c.generated.shell.k + 1))
      (hperp : inner ℂ c.z w = 0)
      (hresponse :
        evenCompressedCanonical c.generated.shell.Lstar
            (c.generated.shell.k + 1) w =
          -(canonicalEvenApertureFirst
            c.generated.shell.Lstar (c.generated.shell.k + 1) c.z))

/-- Branch split using the actual production derivative and actual response. -/
theorem GeneratedStrictEvenContact.production_frontier
    (c : GeneratedStrictEvenContact) :
    Nonempty (GeneratedStrictEvenProductionBranch c) := by
  have hnonpos := c.firstVariation_nonpos_production
  rcases lt_or_eq_of_le hnonpos with hneg | hzero
  · exact ⟨.firstOrder hneg⟩
  · let w :=
      canonicalStationaryEvenResponse
        c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
        c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hzero
    have hs :=
      canonicalStationaryEvenResponse_spec
        c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
        c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hzero
    exact ⟨.stationary hzero w hs.1 hs.2⟩

/-- The stationary generated contact has zero actual optimized curvature.
The generic Schur-contact layer is responsible for upgrading right-negative
ground information to the scalar optimized profile; no fixed-z right-negative
shortcut is permitted. -/
theorem GeneratedStrictEvenContact.actual_stationary_curvature_eq_zero
    (c : GeneratedStrictEvenContact)
    (hstationary :
      productionContactFirstVariation .even c.generated.shell.Lstar
        (c.generated.shell.k + 1) c.z = 0) :
    canonicalOptimizedContactCurvature
      c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
      c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary = 0 :=
  production_stationary_schur_curvature_eq_zero
    c hstationary

/-- Exact positive stationary production saturation balance. -/
theorem GeneratedStrictEvenContact.production_stationary_saturation
    (c : GeneratedStrictEvenContact)
    (hstationary :
      productionContactFirstVariation .even c.generated.shell.Lstar
        (c.generated.shell.k + 1) c.z = 0) :
    productionContactRemainderValue c.generated.shell.Lstar
        (c.generated.shell.k + 1) c.z
        (canonicalStationaryEvenResponse
          c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
          c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary) =
      (2 * Real.pi)^2 / c.generated.shell.Lstar^2 *
        productionStrictEvenSourceValue c.generated.shell.Lstar
          (c.generated.shell.k + 1) c.z := by
  have hk := c.actual_stationary_curvature_eq_zero hstationary
  have hb :=
    canonicalStationaryCurvature_eq_productionSaturationGap
      c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
      c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary
  unfold productionContactSaturationGap at hb
  linarith

theorem GeneratedStrictEvenContact.production_stationary_remainder_pos
    (c : GeneratedStrictEvenContact)
    (hstationary :
      productionContactFirstVariation .even c.generated.shell.Lstar
        (c.generated.shell.k + 1) c.z = 0) :
    0 < productionContactRemainderValue c.generated.shell.Lstar
      (c.generated.shell.k + 1) c.z
      (canonicalStationaryEvenResponse
        c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
        c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary) := by
  rw [c.production_stationary_saturation hstationary]
  positivity [c.sourceValue_pos]

/-- Inherited strict-even contacts satisfy the stationary positive balance. -/
theorem GeneratedStrictEvenContact.inherited_production_saturation
    (c : GeneratedStrictEvenContact)
    (hinh : c.generated.shell.n < c.generated.shell.k) :
    productionContactRemainderValue c.generated.shell.Lstar
        (c.generated.shell.k + 1) c.z
        (canonicalStationaryEvenResponse
          c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
          c.z c.z_ne c.z_norm c.z_kernel c.odd_positive
          (c.firstVariation_eq_zero_of_inherited hinh)) =
      (2 * Real.pi)^2 / c.generated.shell.Lstar^2 *
        productionStrictEvenSourceValue c.generated.shell.Lstar
          (c.generated.shell.k + 1) c.z :=
  c.production_stationary_saturation
    (c.firstVariation_eq_zero_of_inherited hinh)

end Zeta23.CCM

#print axioms Zeta23.CCM.GeneratedStrictEvenContact.production_frontier
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.firstVariation_eq_zero_of_inherited
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.production_stationary_saturation
#print axioms Zeta23.CCM.GeneratedGlobalFirstCrossing.exists_generatedStrictEvenContact_of_evenStrict
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.frontier
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.sourceValue_pos
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.stationary_saturation_frontier
