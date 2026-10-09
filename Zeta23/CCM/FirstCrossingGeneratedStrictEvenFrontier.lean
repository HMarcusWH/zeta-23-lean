import Zeta23.CCM.FirstCrossingProductionCurvatureBridge
import Zeta23.CCM.FirstCrossingInheritedStationarity

noncomputable section

namespace Zeta23.CCM

open Complex Filter Set
open scoped Topology

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
      (hfresh : c.generated.shell.k = c.generated.shell.n)
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

/-- Inherited strict-even contacts are stationary; transverse crossing remains
only in the fresh-born branch. -/
theorem GeneratedStrictEvenContact.firstVariation_eq_zero_of_inherited
    (c : GeneratedStrictEvenContact)
    (hinh : c.generated.shell.n < c.generated.shell.k) :
    productionContactFirstVariation .even c.generated.shell.Lstar
      (c.generated.shell.k+1) c.z = 0 := by
  have hseed :=
    c.generated.inheritedSeed_firstVariation_zero hinh
  let yp : euclideanParityBoundaryFlatSubspace c.generated.shell.p
      (c.generated.shell.k + 1) :=
    parityPlateauExtend c.generated.shell.p c.generated.shell.n_le_k
      c.generated.shell.seed
  have hcarrier :
      euclideanParityBoundaryFlatSubspace c.generated.shell.p
          (c.generated.shell.k + 1) =
        euclideanEvenBoundaryFlatSubspace (c.generated.shell.k + 1) := by
    rw [c.selected_even]
    exact euclideanParityBoundaryFlatSubspace_even _
  have hymem :
      (yp : EuclideanSpace ℂ (Fin (2 * (c.generated.shell.k + 1) + 1))) ∈
        euclideanEvenBoundaryFlatSubspace (c.generated.shell.k + 1) := by
    rw [← hcarrier]
    exact yp.property
  let y : euclideanEvenBoundaryFlatSubspace (c.generated.shell.k + 1) :=
    ⟨yp, hymem⟩
  have hyval :
      (y : EuclideanSpace ℂ (Fin (2 * (c.generated.shell.k + 1) + 1))) =
        (yp : EuclideanSpace ℂ (Fin (2 * (c.generated.shell.k + 1) + 1))) := rfl
  have hparker :
      parityCompressedCanonical c.generated.shell.p c.generated.shell.Lstar
        (c.generated.shell.k + 1) yp = 0 := by
    exact c.generated.shell.extended_kernel c.generated.shell.k
      c.generated.shell.n_le_k c.generated.shell.k_le_N
  have hparAmbient :
      (((euclideanParityBoundaryFlatSubspace c.generated.shell.p
          (c.generated.shell.k + 1)).orthogonalProjectionOnto
        ((canonicalSourceMatrix c.generated.shell.Lstar
          (c.generated.shell.k + 1)).toEuclideanLin
          (yp : EuclideanSpace ℂ
            (Fin (2 * (c.generated.shell.k + 1) + 1))))) :
        EuclideanSpace ℂ (Fin (2 * (c.generated.shell.k + 1) + 1))) = 0 := by
    have hval := congrArg Subtype.val hparker
    change
      (((euclideanParityBoundaryFlatSubspace c.generated.shell.p
          (c.generated.shell.k + 1)).orthogonalProjectionOnto
        ((canonicalSourceMatrix c.generated.shell.Lstar
          (c.generated.shell.k + 1)).toEuclideanLin
          (yp : EuclideanSpace ℂ
            (Fin (2 * (c.generated.shell.k + 1) + 1))))) :
        EuclideanSpace ℂ (Fin (2 * (c.generated.shell.k + 1) + 1))) = 0 at hval
    exact hval
  have hyker :
      evenCompressedCanonical c.generated.shell.Lstar
        (c.generated.shell.k + 1) y = 0 := by
    apply Subtype.ext
    change
      (((euclideanEvenBoundaryFlatSubspace
          (c.generated.shell.k + 1)).orthogonalProjectionOnto
        ((canonicalSourceMatrix c.generated.shell.Lstar
          (c.generated.shell.k + 1)).toEuclideanLin
          (y : EuclideanSpace ℂ
            (Fin (2 * (c.generated.shell.k + 1) + 1))))) :
        EuclideanSpace ℂ (Fin (2 * (c.generated.shell.k + 1) + 1))) = 0
    simpa only [hcarrier, hyval] using hparAmbient
  obtain ⟨a, ha⟩ :=
    strictEven_zeroKernel_is_line c.Lstar_pos (c.generated.shell.k + 1)
      c.two_le_K c.z c.z_ne c.z_kernel c.odd_positive y hyker
  have hyne : y ≠ 0 := by
    have hpne : yp ≠ 0 := by
      exact parityPlateauExtend_ne_zero c.generated.shell.p
        c.generated.shell.n_le_k c.generated.shell.seed
        c.generated.shell.seed_ne
    intro hyzero
    apply hpne
    apply Subtype.ext
    calc
      (yp : EuclideanSpace ℂ (Fin (2 * (c.generated.shell.k + 1) + 1))) =
          (y : EuclideanSpace ℂ (Fin (2 * (c.generated.shell.k + 1) + 1))) :=
        hyval.symm
      _ = 0 := by simp [hyzero]
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_smul] at ha
    exact hyne ha.symm
  have henergy (s : ℝ) :
      productionContactFixedEnergy .even s
          (c.generated.shell.k + 1) y =
        inheritedSelectedEnergy c.generated s := by
    have hnative :
        productionContactFixedEnergy .even s
            (c.generated.shell.k + 1) y =
          Complex.re
            (inner ℂ
              ((canonicalSourceMatrix s
                (c.generated.shell.k + 1)).toEuclideanLin
                (y : EuclideanSpace ℂ
                  (Fin (2 * (c.generated.shell.k + 1) + 1))))
              (y : EuclideanSpace ℂ
                (Fin (2 * (c.generated.shell.k + 1) + 1)))) := by
      exact re_inner_parityCompressedCanonical_self .even s
        (c.generated.shell.k + 1) y
    have hselected :
        inheritedSelectedEnergy c.generated s =
          Complex.re
            (inner ℂ
              ((canonicalSourceMatrix s
                (c.generated.shell.k + 1)).toEuclideanLin
                (yp : EuclideanSpace ℂ
                  (Fin (2 * (c.generated.shell.k + 1) + 1))))
              (yp : EuclideanSpace ℂ
                (Fin (2 * (c.generated.shell.k + 1) + 1)))) := by
      change
        Complex.re
          (inner ℂ
            (parityCompressedCanonical c.generated.shell.p s
              (c.generated.shell.k + 1) yp) yp) = _
      exact re_inner_parityCompressedCanonical_self
        c.generated.shell.p s (c.generated.shell.k + 1) yp
    rw [hnative, hselected, hyval]
  have hyfirst :
      productionContactFirstVariation .even c.generated.shell.Lstar
        (c.generated.shell.k + 1) y = 0 := by
    change
      deriv (fun s : ℝ => productionContactFixedEnergy .even s
        (c.generated.shell.k + 1) y) c.generated.shell.Lstar = 0
    rw [show
      (fun s : ℝ => productionContactFixedEnergy .even s
        (c.generated.shell.k + 1) y) =
          inheritedSelectedEnergy c.generated from funext henergy]
    exact hseed
  rw [← ha, canonicalEven_firstVariation_smul
    c.Lstar_pos (c.generated.shell.k + 1) a c.z] at hyfirst
  have hapos : 0 < ‖a‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr ha0)
  exact (mul_eq_zero.mp hyfirst).resolve_left (ne_of_gt hapos)


/-- A strict negative first variation cannot be inherited: F06 forces every
inherited strict-even contact to be stationary.  Hence the transverse branch is
fresh-born at the first zero-plateau index. -/
theorem GeneratedStrictEvenContact.firstOrder_is_fresh
    (c : GeneratedStrictEvenContact)
    (hneg :
      productionContactFirstVariation .even c.generated.shell.Lstar
        (c.generated.shell.k + 1) c.z < 0) :
    c.generated.shell.k = c.generated.shell.n := by
  rcases lt_or_eq_of_le c.generated.shell.n_le_k with hinh | heq
  · have hzero := c.firstVariation_eq_zero_of_inherited hinh
    linarith
  · exact heq.symm

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
  · exact ⟨.firstOrder (c.firstOrder_is_fresh hneg) hneg⟩
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
  have hreal :
      ProductionContactFirstVariationRealized .even
        c.generated.shell.Lstar (c.generated.shell.k+1) c.z := by
    change HasDerivAt
      (fun s : ℝ => productionContactFixedEnergy .even s
        (c.generated.shell.k+1) c.z)
      (productionContactFirstVariation .even c.generated.shell.Lstar
        (c.generated.shell.k+1) c.z) c.generated.shell.Lstar
    rw [canonicalEven_firstVariation_eq_inner
      c.Lstar_pos (c.generated.shell.k+1) c.z]
    exact canonicalParity_fixedEnergy_hasDerivAt
      .even c.Lstar_pos (c.generated.shell.k+1) c.z
  exact c.generated.firstVariation_nonpos_of_kernel .even c.z c.z_kernel hreal

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


/-! ## Production specialization of the generic Schur theorem -/

/-- The authoritative native-even continuous map and historical legal
compression act identically on each vector.  This bridge prevents instance
elaboration from conflating the generic parity carrier with the native one. -/
private theorem canonicalEvenCompressedFamilyCLM_apply_legacy
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    canonicalEvenCompressedFamilyCLM K L v =
      evenCompressedCanonical L K v := by
  apply Subtype.ext
  rfl



/-- The actual compressed even family has the first derivative exported by
F01. -/
theorem canonicalEvenCompressedFamily_deriv
    {L : ℝ} (hL : 0 < L) (K : ℕ) :
    deriv (canonicalEvenCompressedFamilyCLM K) L =
      canonicalEvenApertureFirstCLM L K := by
  change deriv (canonicalParityCompressedFamilyCLM .even K) L =
    canonicalParityApertureFirstCLM .even L K
  exact canonicalParityCompressedFamily_deriv .even hL K

/-- The second derivative of the actual compressed even family is the F01
second jet. -/
theorem canonicalEvenCompressedFamily_secondDeriv
    {L : ℝ} (hL : 0 < L) (K : ℕ) :
    deriv (deriv (canonicalEvenCompressedFamilyCLM K)) L =
      canonicalEvenApertureSecondCLM L K := by
  change deriv (deriv (canonicalParityCompressedFamilyCLM .even K)) L =
    canonicalParityApertureSecondCLM .even L K
  exact canonicalParityCompressedFamily_secondDeriv .even hL K

/-- The selected strict-even successor is negative arbitrarily close on the
right in the actual fixed cutoff carrier. -/
theorem GeneratedStrictEvenContact.even_negative_direction_right
    (c : GeneratedStrictEvenContact) :
    ∀ ε > 0, ∃ L,
      c.generated.shell.Lstar < L ∧
      L < c.generated.shell.Lstar + ε ∧
      ∃ v : euclideanEvenBoundaryFlatSubspace
          (c.generated.shell.k + 1),
        Complex.re
          (inner ℂ
            (canonicalEvenCompressedFamilyCLM
              (c.generated.shell.k + 1) L v) v) < 0 := by
  have hcross :
      ParityRightCrossesNegative .even
        c.generated.shell.k c.generated.shell.Lstar := by
    simpa [c.selected_even] using
      c.generated.shell.successor_right_crossing
  intro ε hε
  obtain ⟨L, hLlo, hLhi, hbottom⟩ := hcross ε hε
  have hk : 1 ≤ c.generated.shell.k :=
    le_trans c.generated.shell.one_le_n c.generated.shell.n_le_k
  have hbottom' :
      parityRayleighBottom .even L (c.generated.shell.k + 1) < 0 := hbottom
  obtain ⟨v₀, hv₀ne, hv₀eig⟩ :=
    exists_eigenmode_at_parityRayleighBottom_succ
      .even L c.generated.shell.k hk
  have hbad : ParityBad .even L (c.generated.shell.k + 1) :=
    parityBad_of_negative_eigenmode hbottom' hv₀ne hv₀eig
  obtain ⟨x, _hxne, hxneg⟩ :=
    exists_negative_compressed_direction_of_parityBad hbad
  have hxAmbientNeg :
      Complex.re
        (inner ℂ
          ((canonicalSourceMatrix L (c.generated.shell.k + 1)).toEuclideanLin
            (x : EuclideanSpace ℂ
              (Fin (2 * (c.generated.shell.k + 1) + 1))))
          (x : EuclideanSpace ℂ
            (Fin (2 * (c.generated.shell.k + 1) + 1)))) < 0 := by
    rw [re_inner_parityCompressedCanonical_self] at hxneg
    exact hxneg
  let v : euclideanEvenBoundaryFlatSubspace
      (c.generated.shell.k + 1) :=
    ⟨x, by
      simpa only [euclideanParityBoundaryFlatSubspace_even] using x.property⟩
  have hvval :
      (v : EuclideanSpace ℂ (Fin (2 * (c.generated.shell.k + 1) + 1))) =
        (x : EuclideanSpace ℂ (Fin (2 * (c.generated.shell.k + 1) + 1))) := rfl
  have hvneg :
      Complex.re
        (inner ℂ
          (canonicalEvenCompressedFamilyCLM
            (c.generated.shell.k + 1) L v) v) < 0 := by
    change Complex.re
      (inner ℂ
        ((euclideanEvenBoundaryFlatSubspace
          (c.generated.shell.k + 1)).orthogonalProjectionOnto
          ((canonicalSourceMatrix L (c.generated.shell.k + 1)).toEuclideanLin
            (v : EuclideanSpace ℂ
              (Fin (2 * (c.generated.shell.k + 1) + 1)))))
        v) < 0
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
    simpa only [hvval] using hxAmbientNeg
  exact ⟨L, hLlo, hLhi, v, hvneg⟩

/-- The selected strict-even family is PSD throughout the generated left
prefix. -/
theorem GeneratedStrictEvenContact.even_nonnegative_left
    (c : GeneratedStrictEvenContact) :
    ∀ L,
      c.generated.shell.Lsmall ≤ L →
      L ≤ c.generated.shell.Lstar →
      ∀ v : euclideanEvenBoundaryFlatSubspace
          (c.generated.shell.k + 1),
        0 ≤ Complex.re
          (inner ℂ
            (canonicalEvenCompressedFamilyCLM
              (c.generated.shell.k + 1) L v) v) := by
  intro L hsmall hstar v
  have hbottom :=
    c.generated.selectedParity_prefix_nonnegative
      .even hsmall hstar
  let x : euclideanParityBoundaryFlatSubspace .even
      (c.generated.shell.k + 1) :=
    ⟨(v : EuclideanSpace ℂ
        (Fin (2 * (c.generated.shell.k + 1) + 1))), by
      simpa only [euclideanParityBoundaryFlatSubspace_even] using v.property⟩
  have hxval :
      (x : EuclideanSpace ℂ (Fin (2 * (c.generated.shell.k + 1) + 1))) =
        (v : EuclideanSpace ℂ (Fin (2 * (c.generated.shell.k + 1) + 1))) := rfl
  have hbound :=
    parityRayleighBottom_mul_norm_sq_le
      .even L (c.generated.shell.k + 1) x
  have hleft :
      0 ≤ parityRayleighBottom .even L
          (c.generated.shell.k + 1) * ‖x‖ ^ 2 :=
    mul_nonneg hbottom (sq_nonneg ‖x‖)
  have hq :
      0 ≤ Complex.re
        (inner ℂ
          (parityCompressedCanonical .even L
            (c.generated.shell.k + 1) x) x) :=
    le_trans hleft hbound
  have hqAmbient :
      0 ≤ Complex.re
        (inner ℂ
          ((canonicalSourceMatrix L (c.generated.shell.k + 1)).toEuclideanLin
            (v : EuclideanSpace ℂ
              (Fin (2 * (c.generated.shell.k + 1) + 1))))
          (v : EuclideanSpace ℂ
            (Fin (2 * (c.generated.shell.k + 1) + 1)))) := by
    rw [re_inner_parityCompressedCanonical_self] at hq
    simpa only [hxval] using hq
  change 0 ≤ Complex.re
    (inner ℂ
      ((euclideanEvenBoundaryFlatSubspace
        (c.generated.shell.k + 1)).orthogonalProjectionOnto
        ((canonicalSourceMatrix L (c.generated.shell.k + 1)).toEuclideanLin
          (v : EuclideanSpace ℂ
            (Fin (2 * (c.generated.shell.k + 1) + 1)))))
      v)
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  exact hqAmbient

/-- The generic stationary Schur geometry, stated at the raw aperture
derivative pairing before identifying the optimized physical curvature.
Passing the response explicitly avoids unfolding it in this proof target. -/
private theorem production_stationary_schur_raw_pair_eq_zero
    (c : GeneratedStrictEvenContact)
    (hstationary :
      productionContactFirstVariation .even c.generated.shell.Lstar
        (c.generated.shell.k + 1) c.z = 0)
    (w : euclideanEvenBoundaryFlatSubspace (c.generated.shell.k + 1))
    (hwperp : inner ℂ c.z w = 0)
    (hwresponse :
      evenCompressedCanonical c.generated.shell.Lstar
        (c.generated.shell.k + 1) w =
        -(canonicalEvenApertureFirst c.generated.shell.Lstar
          (c.generated.shell.k + 1) c.z)) :
    Complex.re (inner ℂ
      (canonicalEvenApertureSecondCLM c.generated.shell.Lstar
        (c.generated.shell.k + 1) c.z) c.z) +
      2 * Complex.re (inner ℂ
        (canonicalEvenApertureFirstCLM c.generated.shell.Lstar
          (c.generated.shell.k + 1) w) c.z) = 0 := by
  let K := c.generated.shell.k + 1
  let L := c.generated.shell.Lstar
  let F :
      ℝ → euclideanEvenBoundaryFlatSubspace K →L[ℂ]
        euclideanEvenBoundaryFlatSubspace K :=
    canonicalEvenCompressedFamilyCLM K
  have hF :
      ContDiffAt ℝ 2 F L := by
    have hC2 := canonicalEvenCompressedC2_proved K
    exact
      (hC2 L c.Lstar_pos).contDiffAt
        (Ioi_mem_nhds c.Lstar_pos)
  have hop (s : ℝ) :
      (F s).toLinearMap = evenResponseContactOperator s K := by
    apply LinearMap.ext
    intro v
    exact (canonicalEvenCompressedFamilyCLM_apply_legacy s K v).trans
      (evenResponseContactOperator_apply s K v).symm
  have hsym :
      ∀ᶠ s in 𝓝 L,
        LinearMap.IsSymmetric (𝕜 := ℂ)
          (E := euclideanEvenBoundaryFlatSubspace K) (F s).toLinearMap := by
    filter_upwards with s
    rw [hop s]
    exact evenResponseContactOperator_isSymmetric s K
  have hz : F L c.z = 0 := by
    simpa only [F, L, K, canonicalEvenCompressedFamilyCLM_apply_legacy] using
      c.z_kernel
  have hker :
      ∀ v : euclideanEvenBoundaryFlatSubspace K,
        F L v = 0 → ∃ α : ℂ, v = α • c.z := by
    intro v hv
    have hv' :
        evenCompressedCanonical L K v = 0 := by
      simpa only [F, L, K, canonicalEvenCompressedFamilyCLM_apply_legacy] using hv
    obtain ⟨α, hα⟩ :=
      strictEven_zeroKernel_is_line
        c.Lstar_pos K c.two_le_K c.z c.z_ne c.z_kernel
        c.odd_positive v hv'
    exact ⟨α, hα.symm⟩
  have hstat :
      deriv (fun s => Complex.re (inner ℂ (F s c.z) c.z)) L = 0 := by
    have hscalar (s : ℝ) :
        Complex.re (inner ℂ (F s c.z) c.z) =
          productionContactFixedEnergy .even s K c.z := by
      change Complex.re
        (inner ℂ (canonicalEvenCompressedFamilyCLM K s c.z) c.z) =
          productionContactFixedEnergy .even s K c.z
      rw [canonicalEvenCompressedFamilyCLM_apply_legacy]
      change Complex.re (inner ℂ
        (evenCompressedCanonical s K c.z) c.z) =
        Complex.re (inner ℂ
          (parityCompressedCanonical .even s K c.z) c.z)
      rfl
    rw [show
      (fun s : ℝ => Complex.re (inner ℂ (F s c.z) c.z)) =
        (fun s : ℝ => productionContactFixedEnergy .even s K c.z)
      from funext hscalar]
    simpa only [L, K, productionContactFirstVariation] using hstationary
  have hF1 :
      deriv F L = canonicalEvenApertureFirstCLM L K := by
    simpa [F] using canonicalEvenCompressedFamily_deriv c.Lstar_pos K
  have hw :
      F L w = -((deriv F L) c.z) := by
    calc
      F L w = evenCompressedCanonical L K w := by
        exact canonicalEvenCompressedFamilyCLM_apply_legacy L K w
      _ = -(canonicalEvenApertureFirst L K c.z) := hwresponse
      _ = -((deriv F L) c.z) := by
        rw [hF1]
        rfl
  have hgeneric :=
    stationarySchur_contact_secondPairing_eq_zero
      (F := F) (z := c.z) (w := w)
      (x := L) (a := c.generated.shell.Lsmall)
      (b := c.generated.shell.Lneg)
      c.generated.shell.Lsmall_lt_Lstar
      c.generated.shell.Lstar_lt_Lneg
      hF hsym hz c.z_norm hker
      (by
        intro y hySmall hyStar v
        exact c.even_nonnegative_left y hySmall hyStar v)
      (by
        intro ε hε
        simpa [L, K, F] using c.even_negative_direction_right ε hε)
      hstat hwperp hw
  have hF2 :
      deriv (deriv F) L = canonicalEvenApertureSecondCLM L K := by
    simpa [F] using canonicalEvenCompressedFamily_secondDeriv c.Lstar_pos K
  rw [hF2, hF1] at hgeneric
  simpa only [L, K] using hgeneric

theorem production_stationary_schur_curvature_eq_zero
    (c : GeneratedStrictEvenContact)
    (hstationary :
      productionContactFirstVariation .even c.generated.shell.Lstar
        (c.generated.shell.k + 1) c.z = 0) :
    canonicalOptimizedContactCurvature
      c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
      c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary = 0 := by
  let K := c.generated.shell.k + 1
  let L := c.generated.shell.Lstar
  let w : euclideanEvenBoundaryFlatSubspace K :=
    canonicalStationaryEvenResponse
      c.Lstar_pos K c.two_le_K
      c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary
  have hspec :=
    canonicalStationaryEvenResponse_spec
      c.Lstar_pos K c.two_le_K
      c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary
  have hgeneric :=
    production_stationary_schur_raw_pair_eq_zero
      c hstationary w hspec.1 hspec.2
  have hfixed :=
    canonicalEven_fixedSecond_eq_inner c.Lstar_pos K c.z
  have hmixed :
      Complex.re
          (inner ℂ (canonicalEvenApertureFirstCLM L K w) c.z) =
        Complex.re
          (inner ℂ c.z (canonicalEvenApertureFirstCLM L K w)) := by
    exact inner_re_symm (𝕜 := ℂ)
      (canonicalEvenApertureFirstCLM L K w) c.z
  unfold canonicalOptimizedContactCurvature canonicalContactSecondPairing
  change
    productionContactFixedSecondVariation .even L K c.z +
      2 * Complex.re
        (inner ℂ c.z (canonicalEvenApertureFirst L K w)) = 0
  rw [hfixed]
  change
    Complex.re
        (inner ℂ (canonicalEvenApertureSecondCLM L K c.z) c.z) +
      2 * Complex.re
        (inner ℂ c.z (canonicalEvenApertureFirstCLM L K w)) = 0
  rw [← hmixed]
  exact hgeneric

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
    (hF04 : ProductionContactF04DerivativeAuthority
      c.generated.shell.Lstar (c.generated.shell.k + 1))
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
      c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary hF04
  unfold productionContactSaturationGap at hb
  linarith

theorem GeneratedStrictEvenContact.production_stationary_remainder_pos
    (c : GeneratedStrictEvenContact)
    (hF04 : ProductionContactF04DerivativeAuthority
      c.generated.shell.Lstar (c.generated.shell.k + 1))
    (hstationary :
      productionContactFirstVariation .even c.generated.shell.Lstar
        (c.generated.shell.k + 1) c.z = 0) :
    0 < productionContactRemainderValue c.generated.shell.Lstar
      (c.generated.shell.k + 1) c.z
      (canonicalStationaryEvenResponse
        c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
        c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary) := by
  rw [c.production_stationary_saturation hF04 hstationary]
  apply mul_pos
  · apply div_pos
    · exact sq_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
    · exact sq_pos_of_pos c.Lstar_pos
  · exact c.sourceValue_pos

/-- Inherited strict-even contacts satisfy the stationary positive balance. -/
theorem GeneratedStrictEvenContact.inherited_production_saturation
    (c : GeneratedStrictEvenContact)
    (hF04 : ProductionContactF04DerivativeAuthority
      c.generated.shell.Lstar (c.generated.shell.k + 1))
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
  c.production_stationary_saturation hF04
    (c.firstVariation_eq_zero_of_inherited hinh)


/-! ## Completed production frontier -/

/-- Final F07 branch object.  The transverse branch records that strict
first-order escape is necessarily fresh-born.  The stationary branch carries
the actual unique perpendicular response, zero Schur curvature, exact
production saturation, and strict positivity of the concrete remainder. -/
inductive GeneratedStrictEvenCompletedProductionBranch
    (c : GeneratedStrictEvenContact) : Type
  | firstOrder
      (hfresh : c.generated.shell.k = c.generated.shell.n)
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
      (hunique :
        ∀ w' : euclideanEvenBoundaryFlatSubspace (c.generated.shell.k + 1),
          inner ℂ c.z w' = 0 →
          evenCompressedCanonical c.generated.shell.Lstar
              (c.generated.shell.k + 1) w' =
            -(canonicalEvenApertureFirst
              c.generated.shell.Lstar (c.generated.shell.k + 1) c.z) →
          w' = w)
      (hcurvature :
        canonicalOptimizedContactCurvature
          c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
          c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hzero = 0)
      (hsaturation :
        productionContactRemainderValue c.generated.shell.Lstar
            (c.generated.shell.k + 1) c.z w =
          (2 * Real.pi)^2 / c.generated.shell.Lstar^2 *
            productionStrictEvenSourceValue c.generated.shell.Lstar
              (c.generated.shell.k + 1) c.z)
      (hremainder_pos :
        0 < productionContactRemainderValue c.generated.shell.Lstar
          (c.generated.shell.k + 1) c.z w)

/-- Completed production-authoritative contact split.  No legacy realization,
curvature bridge, supplied kappa, arbitrary remainder, endpoint barrier, or RH
premise occurs in the theorem type. -/
theorem GeneratedStrictEvenContact.completed_production_frontier
    (c : GeneratedStrictEvenContact)
    (hF04 : ProductionContactF04DerivativeAuthority
      c.generated.shell.Lstar (c.generated.shell.k + 1)) :
    Nonempty (GeneratedStrictEvenCompletedProductionBranch c) := by
  have hnonpos := c.firstVariation_nonpos_production
  rcases lt_or_eq_of_le hnonpos with hneg | hzero
  · exact ⟨.firstOrder (c.firstOrder_is_fresh hneg) hneg⟩
  · let w :=
      canonicalStationaryEvenResponse
        c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
        c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hzero
    have hspec :=
      canonicalStationaryEvenResponse_spec
        c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
        c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hzero
    have hex :=
      existsUnique_canonicalStationaryEvenResponse
        c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
        c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hzero
    have huniq :
        ∀ w' : euclideanEvenBoundaryFlatSubspace (c.generated.shell.k + 1),
          inner ℂ c.z w' = 0 →
          evenCompressedCanonical c.generated.shell.Lstar
              (c.generated.shell.k + 1) w' =
            -(canonicalEvenApertureFirst
              c.generated.shell.Lstar (c.generated.shell.k + 1) c.z) →
          w' = w := by
      intro w' hp hr
      exact hex.unique ⟨hp, hr⟩ hspec
    have hk := c.actual_stationary_curvature_eq_zero hzero
    have hs := c.production_stationary_saturation hF04 hzero
    have hp := c.production_stationary_remainder_pos hF04 hzero
    refine ⟨.stationary hzero w hspec.1 hspec.2 huniq hk ?_ ?_⟩
    · simpa [w] using hs
    · simpa [w] using hp

/-- Inherited contacts enter the completed stationary branch directly. -/
theorem GeneratedStrictEvenContact.inherited_completed_production_frontier
    (c : GeneratedStrictEvenContact)
    (hF04 : ProductionContactF04DerivativeAuthority
      c.generated.shell.Lstar (c.generated.shell.k + 1))
    (hinh : c.generated.shell.n < c.generated.shell.k) :
    ∃ b : GeneratedStrictEvenCompletedProductionBranch c,
      match b with
      | .firstOrder _ _ => False
      | .stationary hzero _ _ _ _ _ _ _ =>
          hzero = c.firstVariation_eq_zero_of_inherited hinh := by
  let hzero := c.firstVariation_eq_zero_of_inherited hinh
  let w :=
    canonicalStationaryEvenResponse
      c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
      c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hzero
  have hspec :=
    canonicalStationaryEvenResponse_spec
      c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
      c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hzero
  have hex :=
    existsUnique_canonicalStationaryEvenResponse
      c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
      c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hzero
  have huniq :
      ∀ w' : euclideanEvenBoundaryFlatSubspace (c.generated.shell.k + 1),
        inner ℂ c.z w' = 0 →
        evenCompressedCanonical c.generated.shell.Lstar
            (c.generated.shell.k + 1) w' =
          -(canonicalEvenApertureFirst
            c.generated.shell.Lstar (c.generated.shell.k + 1) c.z) →
        w' = w := by
    intro w' hp hr
    exact hex.unique ⟨hp, hr⟩ hspec
  let b : GeneratedStrictEvenCompletedProductionBranch c :=
    .stationary hzero w hspec.1 hspec.2 huniq
      (c.actual_stationary_curvature_eq_zero hzero)
      (by simpa [w] using c.production_stationary_saturation hF04 hzero)
      (by simpa [w] using c.production_stationary_remainder_pos hF04 hzero)
  refine ⟨b, ?_⟩
  rfl


end Zeta23.CCM

#print axioms Zeta23.CCM.GeneratedStrictEvenContact.firstOrder_is_fresh
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.production_frontier
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.firstVariation_eq_zero_of_inherited
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.production_stationary_saturation
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.completed_production_frontier
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.inherited_completed_production_frontier
#print axioms Zeta23.CCM.GeneratedGlobalFirstCrossing.exists_generatedStrictEvenContact_of_evenStrict
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.frontier
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.sourceValue_pos
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.stationary_saturation_frontier

#print axioms Zeta23.CCM.production_stationary_schur_curvature_eq_zero
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.actual_stationary_curvature_eq_zero
