import Zeta23.CCM.FirstCrossingProductionCurvatureBridge

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
          -(parityProductionApertureFirst .even
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
    (hrealized :
      ProductionContactFirstVariationRealized .even
        c.generated.shell.Lstar (c.generated.shell.k + 1) c.z) :
    GeneratedStrictEvenVariationBranch c := by
  have hnonpos := c.firstVariation_nonpos hrealized
  rcases lt_or_eq_of_le hnonpos with hneg | hzero
  · exact .firstOrder hneg
  · let w :=
      stationaryEvenResponse
        c.Lstar_pos
        (c.generated.shell.k + 1) c.two_le_K
        c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hzero
    have hspec :=
      stationaryEvenResponse_spec
        c.Lstar_pos
        (c.generated.shell.k + 1) c.two_le_K
        c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hzero
    exact .stationary hzero w hspec.1 hspec.2

/-- Exact positive source value at every generated strict-even contact. -/
theorem GeneratedStrictEvenContact.sourceValue_pos
    (c : GeneratedStrictEvenContact) :
    0 < productionStrictEvenSourceValue
      c.generated.shell.Lstar (c.generated.shell.k + 1) c.z := by
  exact productionStrictEvenSourceValue_pos_of_even_zero_ground_strict
    c.Lstar_pos c.two_le_K c.z c.z_ne
    c.evenGround_zero c.z_kernel c.odd_positive

/-- Stationary arithmetic saturation endpoint for the concrete response.  The
two hypotheses are intentionally the exact remaining theorem obligations:
actual production differentiation and outgoing-contact zero curvature. -/
theorem GeneratedStrictEvenContact.stationary_saturation_frontier
    (c : GeneratedStrictEvenContact)
    (hstationary :
      productionContactFirstVariation .even
        c.generated.shell.Lstar (c.generated.shell.k + 1) c.z = 0)
    (hbridge :
      ProductionContactCurvatureArithmeticIdentity
        c.generated.shell.Lstar (c.generated.shell.k + 1) c.z
        (stationaryEvenResponse
          c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
          c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary))
    (hkappa :
      productionContactOptimizedCurvature
        c.generated.shell.Lstar (c.generated.shell.k + 1) c.z
        (stationaryEvenResponse
          c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
          c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary) = 0) :
    productionContactRemainderValue
        c.generated.shell.Lstar (c.generated.shell.k + 1) c.z
        (stationaryEvenResponse
          c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
          c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary) =
      (2 * Real.pi) ^ 2 / c.generated.shell.Lstar ^ 2 *
        productionStrictEvenSourceValue
          c.generated.shell.Lstar (c.generated.shell.k + 1) c.z := by
  exact
    (productionContactOptimizedCurvature_zero_iff hbridge).mp hkappa

end Zeta23.CCM

#print axioms Zeta23.CCM.GeneratedStrictEvenContact.frontier
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.sourceValue_pos
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.stationary_saturation_frontier
