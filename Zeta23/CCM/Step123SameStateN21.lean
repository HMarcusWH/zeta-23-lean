import Zeta23.CCM.Step123OutputData
import Zeta23.CCM.CanonicalPoleNeutralPublicAPI
import Zeta23.CCM.CanonicalPoleNeutralGroundConstraints
import Zeta23.CCM.NativeDeepThresholdEvenMoment

/-!
# N21 `retained.branch`: neutral-bottom trichotomy on the stored selected ground

This module proves contract field N21 for the ACTUAL stored packet
`out : Step123NativeOutput β σ a`.  At the stored aperture
`L = fixedOriginalSincTrialAperture a` and the stored selected cutoff
`K = out.retained.state.selection.cutoff`, the actual native pole-neutral
even and odd Rayleigh bottoms `E`, `O` are compared, and each of the three
outcomes carries its branch-specific consequences stated about the
STORED selected ground `out.selectedGround` (N20) and the stored value
`lam = out.retained.state.selection.lam`:

* strict even (`E < O`): the stored parity is even, `lam = E`, the actual
  shifted odd operator is inverted at `lam` by the existing equivalence,
  the stored vector `u` satisfies the rank-one source equation
  `(B0 - lam) D0 u = S0(u) • g0`, the exact source-moment energy identity,
  the odd-gap lower bound and strict positivity (R2), `M4(u) ≠ 0`,
  `S0(u) ≠ 0`, `u = S0(u) • ray(lam)`, `S0(ray(lam)) = 1`, the eigenvalue
  iff `(∃ v ≠ 0, A0 v = lam v) ↔ S0(ray(lam)) = 1` and the shifted
  determinant identity, hence `det(A0 - lam) = 0` (SE);
* strict odd (`O < E`): the stored parity is odd, `lam = O`, the actual
  shifted even operator is inverted at `lam`, the stored vector `w`
  satisfies the exact adjoint competitor equation with the negative Riesz
  source, nonzero cubic pairing, `w = <g0,w> • ray*(lam)`,
  `<g0, ray*(lam)> = 1`, the eigenvalue iff
  `(∃ v ≠ 0, B0 v = lam v) ↔ <g0, ray*(lam)> = 1` and the adjoint
  determinant identity, hence `det(B0 - lam) = 0` (SO);
* tie (`E = O`): `lam = E = O`, both actual shifted operators are positive
  and strictly positive on the orthogonal complements of their actual
  kernels, and, for the stored vector in WHICHEVER parity was stored, its
  rank-one source equation (for odd `w`, the adjoint competitor equation
  with the negative Riesz source), the kernel compatibility identity
  obtained by projecting it onto the opposite shifted kernel, the range
  membership of its transformed source, and the complementary-response
  decomposition retaining the full actual kernel component.  For a stored
  even vector the fourth moment is nonzero (from the constructed
  simplicity) and the source moment is nonnegative; the corrected source
  `S0` is NOT claimed nonzero at a tie, and no other ground is chosen for
  a stored odd vector.

The explicit trichotomy is the inductive `DetectorRetainedSelectedGroundBranch`
(`Step123NativeOutput.n21_retained_branch`).  The same consequences are
also indexed by the EXISTING tag `PoleNeutralGroundBranch` of
`CanonicalPoleNeutralPublicAPI` (`DetectorRetainedSchurState.groundBranchFacts`):
for every value of that tag the consequences hold on the stored ground
(`Step123NativeOutput.n21_groundBranch_facts`), which strengthens the
bare `Nonempty (PoleNeutralGroundBranch ...)` of the MC08 consumer
(`Step123NativeOutput.n21_selected_ground_branch_consumer`).

Nothing is assumed about the branch: the trichotomy is decided by
`lt_trichotomy` on the actual bottoms, the stored parity in the strict
branches is DERIVED from `lam = min E O` (`lam_is_actual_global`) and the
stored eigen equation, and every vector fact is an existing all-vector
result instantiated on the stored ground through a definitional parity
view (`nativeParityEvenView` / `nativeParityOddView`).  The only
hypotheses of the packet-level branch views are the real case conditions
(`E < O`, `O < E` or `E = O`); no bridge identity, error bound or branch
consequence is a hypothesis.

What is NOT proved here: no Step 4 law, no A-X/B-Y/C-Schur estimate, no
claim that the producer or the 44-field release is complete, no D2
statement, and nothing about the Riemann hypothesis.
-/

noncomputable section

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

/-! ## Definitional parity views of a stored parity-tagged vector -/

/-- The stored parity-tagged vector read in the even carrier, given that
its stored parity is even.  Pure definitional transport; no vector is
chosen. -/
def nativeParityEvenView {L : ℝ} {K : ℕ} :
    (γ : ReversalParity) → γ = .even → nativePoleNeutralParitySpace γ L K →
      poleNeutralEvenSubspace L K
  | _, rfl, g => g

/-- The stored parity-tagged vector read in the odd carrier, given that
its stored parity is odd. -/
def nativeParityOddView {L : ℝ} {K : ℕ} :
    (γ : ReversalParity) → γ = .odd → nativePoleNeutralParitySpace γ L K →
      poleNeutralOddSubspace L K
  | _, rfl, g => g

/-- The even view IS the stored pair: equality of parity-tagged pairs. -/
theorem nativeParityEvenView_sigma {L : ℝ} {K : ℕ} (γ : ReversalParity)
    (h : γ = .even) (g : nativePoleNeutralParitySpace γ L K) :
    (⟨γ, g⟩ : Σ γ' : ReversalParity, nativePoleNeutralParitySpace γ' L K) =
      ⟨.even, nativeParityEvenView γ h g⟩ := by
  subst h
  rfl

theorem nativeParityOddView_sigma {L : ℝ} {K : ℕ} (γ : ReversalParity)
    (h : γ = .odd) (g : nativePoleNeutralParitySpace γ L K) :
    (⟨γ, g⟩ : Σ γ' : ReversalParity, nativePoleNeutralParitySpace γ' L K) =
      ⟨.odd, nativeParityOddView γ h g⟩ := by
  subst h
  rfl

/-- The even view has the same ambient coefficient vector as the stored one. -/
theorem nativeParityEvenView_ambient {L : ℝ} {K : ℕ} (γ : ReversalParity)
    (h : γ = .even) (g : nativePoleNeutralParitySpace γ L K) :
    nativePoleNeutralParityAmbient γ L K g = (nativeParityEvenView γ h g).val.val := by
  subst h
  rfl

theorem nativeParityOddView_ambient {L : ℝ} {K : ℕ} (γ : ReversalParity)
    (h : γ = .odd) (g : nativePoleNeutralParitySpace γ L K) :
    nativePoleNeutralParityAmbient γ L K g = (nativeParityOddView γ h g).val.val := by
  subst h
  rfl

theorem nativeParityEvenView_norm {L : ℝ} {K : ℕ} (γ : ReversalParity)
    (h : γ = .even) (g : nativePoleNeutralParitySpace γ L K) :
    ‖nativeParityEvenView γ h g‖ = ‖g‖ := by
  subst h
  rfl

theorem nativeParityOddView_norm {L : ℝ} {K : ℕ} (γ : ReversalParity)
    (h : γ = .odd) (g : nativePoleNeutralParitySpace γ L K) :
    ‖nativeParityOddView γ h g‖ = ‖g‖ := by
  subst h
  rfl

theorem nativeParityEvenView_eigen {L : ℝ} {K : ℕ} (γ : ReversalParity)
    (h : γ = .even) (g : nativePoleNeutralParitySpace γ L K) (c : ℝ)
    (hg : nativePoleNeutralParityCanonical γ L K g = (c : ℂ) • g) :
    poleNeutralEvenCompressedCanonical L K (nativeParityEvenView γ h g) =
      (c : ℂ) • nativeParityEvenView γ h g := by
  subst h
  exact hg

theorem nativeParityOddView_eigen {L : ℝ} {K : ℕ} (γ : ReversalParity)
    (h : γ = .odd) (g : nativePoleNeutralParitySpace γ L K) (c : ℝ)
    (hg : nativePoleNeutralParityCanonical γ L K g = (c : ℂ) • g) :
    poleNeutralOddCompressedCanonical L K (nativeParityOddView γ h g) =
      (c : ℂ) • nativeParityOddView γ h g := by
  subst h
  exact hg

/-! ## The even rank-one source equation -/

/-- For every actual even eigenvector `u` at `lam`, the actual shifted odd
operator sends its index image to the corrected source multiple of the
projected cubic vector: `(B0 - lam) D0 u = S0(u) • g0`.  This is the
existing shifted rank-one intertwining evaluated at `u`; no gap, tie or
simplicity hypothesis is used. -/
theorem poleNeutral_even_eigen_index_odd_shifted_eq_source {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :
    poleNeutralOddShiftedCanonical L K lam (poleNeutralIndexLinearMap hL K u) =
      poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K := by
  have hr := poleNeutral_shifted_rankOneIntertwining hL K hK lam u
  have ha : poleNeutralEvenShiftedCanonical L K lam u = 0 := by
    simp only [poleNeutralEvenShiftedCanonical, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, hu, sub_self]
  rw [ha, map_zero, sub_zero] at hr
  exact hr

/-! ## Branch consequence records (all-vector statements) -/

/-- Strict-even consequences for ONE actual even vector `u` at the actual
value `lam`: R2 source-moment identity/positivity and SE ray facts. -/
structure PoleNeutralStrictEvenGroundFacts {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (lam : ℝ) (u : poleNeutralEvenSubspace L K) : Prop where
  lam_eq_bottom : lam = poleNeutralEvenRayleighBottom L K hL hK
  below_odd : lam < poleNeutralOddRayleighBottom L K hL hK
  odd_shift_inverse : ∀ v : poleNeutralOddSubspace L K,
    poleNeutralOddShiftedCanonical L K lam
        ((poleNeutralOddShiftedCanonicalEquiv hL K hK lam below_odd).symm v) = v ∧
      (poleNeutralOddShiftedCanonicalEquiv hL K hK lam below_odd).symm
        (poleNeutralOddShiftedCanonical L K lam v) = v
  unit : ‖u‖ = 1
  eigen : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u
  simple : Module.finrank ℂ
    (Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K) (lam : ℂ)) = 1
  source_equation :
    poleNeutralOddShiftedCanonical L K lam (poleNeutralIndexLinearMap hL K u) =
      poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K
  source_moment_energy :
    (star (poleNeutralCorrectedCubicSource L K u) *
      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re =
    (inner ℂ (poleNeutralOddCompressedCanonical L K (poleNeutralIndexLinearMap hL K u) -
      (lam : ℂ) • poleNeutralIndexLinearMap hL K u) (poleNeutralIndexLinearMap hL K u)).re
  source_moment_gap :
    (poleNeutralOddRayleighBottom L K hL hK - lam) * ‖poleNeutralIndexLinearMap hL K u‖ ^ 2 ≤
      (star (poleNeutralCorrectedCubicSource L K u) *
        centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re
  source_moment_pos :
    0 < (star (poleNeutralCorrectedCubicSource L K u) *
      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re
  momentFour_ne_zero : centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val) ≠ 0
  source_ne_zero : poleNeutralCorrectedCubicSource L K u ≠ 0
  ray_eq : u = poleNeutralCorrectedCubicSource L K u •
    poleNeutralEvenShiftedRay hL K hK lam below_odd
  ray_source_eq_one :
    poleNeutralCorrectedCubicSource L K (poleNeutralEvenShiftedRay hL K hK lam below_odd) = 1
  eigen_iff :
    (∃ v : poleNeutralEvenSubspace L K, v ≠ 0 ∧
      poleNeutralEvenCompressedCanonical L K v = (lam : ℂ) • v) ↔
    poleNeutralCorrectedCubicSource L K (poleNeutralEvenShiftedRay hL K hK lam below_odd) = 1
  det_eq : LinearMap.det (poleNeutralEvenShiftedCanonical L K lam) =
    LinearMap.det (poleNeutralOddShiftedCanonical L K lam) *
      (1 - poleNeutralCorrectedCubicSource L K (poleNeutralEvenShiftedRay hL K hK lam below_odd))
  det_eq_zero : LinearMap.det (poleNeutralEvenShiftedCanonical L K lam) = 0

/-- Strict-odd consequences for ONE actual odd vector `w` at the actual
value `lam`: SO adjoint-ray facts with the negative Riesz source. -/
structure PoleNeutralStrictOddGroundFacts {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (lam : ℝ) (w : poleNeutralOddSubspace L K) : Prop where
  lam_eq_bottom : lam = poleNeutralOddRayleighBottom L K hL hK
  below_even : lam < poleNeutralEvenRayleighBottom L K hL hK
  even_shift_inverse : ∀ v : poleNeutralEvenSubspace L K,
    poleNeutralEvenShiftedCanonical L K lam
        ((poleNeutralEvenShiftedCanonicalEquiv hL K hK lam below_even).symm v) = v ∧
      (poleNeutralEvenShiftedCanonicalEquiv hL K hK lam below_even).symm
        (poleNeutralEvenShiftedCanonical L K lam v) = v
  unit : ‖w‖ = 1
  eigen : poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w
  simple : Module.finrank ℂ
    (Module.End.eigenspace (poleNeutralOddCompressedCanonical L K) (lam : ℂ)) = 1
  adjoint_competitor :
    poleNeutralEvenShiftedCanonical L K lam
      ((LinearMap.adjoint (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
        (F := poleNeutralOddSubspace L K) (poleNeutralIndexLinearMap hL K)) w) =
      -poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K
  pairing_ne_zero : poleNeutralCubicPairingFunctional L K w ≠ 0
  ray_eq : w = poleNeutralCubicPairingFunctional L K w •
    poleNeutralOddAdjointShiftedRay hL K hK lam below_even
  ray_pairing_eq_one :
    poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam below_even) = 1
  eigen_iff :
    (∃ v : poleNeutralOddSubspace L K, v ≠ 0 ∧
      poleNeutralOddCompressedCanonical L K v = (lam : ℂ) • v) ↔
    poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam below_even) = 1
  det_eq : LinearMap.det (poleNeutralOddShiftedCanonical L K lam) =
    LinearMap.det (poleNeutralEvenShiftedCanonical L K lam) *
      (1 - poleNeutralCubicPairingFunctional L K
        (poleNeutralOddAdjointShiftedRay hL K hK lam below_even))
  det_eq_zero : LinearMap.det (poleNeutralOddShiftedCanonical L K lam) = 0

/-- Tie consequences for ONE actual even vector `u` at `lam`: the rank-one
source equation `(B0 - lam) D0 u = S0(u) • g0`, its kernel compatibility,
range membership and the complementary response with the retained kernel
component.  No nonvanishing of `S0(u)` is asserted. -/
structure PoleNeutralTiedEvenGroundFacts {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (lam : ℝ) (u : poleNeutralEvenSubspace L K) : Prop where
  unit : ‖u‖ = 1
  eigen : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u
  simple : Module.finrank ℂ
    (Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K) (lam : ℂ)) = 1
  source_equation :
    poleNeutralOddShiftedCanonical L K lam (poleNeutralIndexLinearMap hL K u) =
      poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K
  momentFour_ne_zero : centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val) ≠ 0
  source_moment_energy :
    (star (poleNeutralCorrectedCubicSource L K u) *
      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re =
    (inner ℂ (poleNeutralOddCompressedCanonical L K (poleNeutralIndexLinearMap hL K u) -
      (lam : ℂ) • poleNeutralIndexLinearMap hL K u) (poleNeutralIndexLinearMap hL K u)).re
  source_moment_nonneg :
    0 ≤ (star (poleNeutralCorrectedCubicSource L K u) *
      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re
  kernel_compatibility :
    poleNeutralCorrectedCubicSource L K u •
      poleNeutralOddShiftedKernelProjection L K lam (poleNeutralCubicCompressionVector L K) = 0
  range_mem :
    poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K ∈
      LinearMap.range (poleNeutralOddShiftedCanonical L K lam)
  complementary_response :
    poleNeutralIndexLinearMap hL K u =
      (LinearMap.ker (poleNeutralOddShiftedCanonical L K lam)).starProjection
        (poleNeutralIndexLinearMap hL K u) +
      poleNeutralOddKernelComplementResponse L K lam
        (poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K) range_mem

/-- Tie consequences for ONE actual odd vector `w` at `lam`: the adjoint
competitor equation, kernel compatibility, range membership and the
complementary response with the retained kernel component. -/
structure PoleNeutralTiedOddGroundFacts {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (lam : ℝ) (w : poleNeutralOddSubspace L K) : Prop where
  unit : ‖w‖ = 1
  eigen : poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w
  simple : Module.finrank ℂ
    (Module.End.eigenspace (poleNeutralOddCompressedCanonical L K) (lam : ℂ)) = 1
  adjoint_competitor :
    poleNeutralEvenShiftedCanonical L K lam
      ((LinearMap.adjoint (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
        (F := poleNeutralOddSubspace L K) (poleNeutralIndexLinearMap hL K)) w) =
      -poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K
  kernel_compatibility :
    -poleNeutralCubicPairingFunctional L K w •
      poleNeutralEvenShiftedKernelProjection L K lam (poleNeutralCorrectedCubicRieszVector L K) = 0
  range_mem :
    -poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K ∈
      LinearMap.range (poleNeutralEvenShiftedCanonical L K lam)
  complementary_response :
    (LinearMap.adjoint (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
        (F := poleNeutralOddSubspace L K) (poleNeutralIndexLinearMap hL K)) w =
      (LinearMap.ker (poleNeutralEvenShiftedCanonical L K lam)).starProjection
        ((LinearMap.adjoint (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
          (F := poleNeutralOddSubspace L K) (poleNeutralIndexLinearMap hL K)) w) +
      poleNeutralEvenKernelComplementResponse L K lam
        (-poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K)
        range_mem

/-- Positivity of both actual shifted operators at `lam`, and strict
positivity of each on the orthogonal complement of its actual kernel (any
kernel multiplicity).  This is the carrier on which the tie responses invert
the shifted operators. -/
structure PoleNeutralShiftedPositivity (L : ℝ) (K : ℕ) (lam : ℝ) : Prop where
  even_positive : LinearMap.IsPositive (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
    (poleNeutralEvenShiftedCanonical L K lam)
  odd_positive : LinearMap.IsPositive (𝕜 := ℂ) (E := poleNeutralOddSubspace L K)
    (poleNeutralOddShiftedCanonical L K lam)
  even_complement_pos : ∀ x : poleNeutralEvenSubspace L K,
    x ∈ Submodule.orthogonal (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
      (LinearMap.ker (poleNeutralEvenShiftedCanonical L K lam)) → x ≠ 0 →
    0 < (inner ℂ (poleNeutralEvenShiftedCanonical L K lam x) x).re
  odd_complement_pos : ∀ x : poleNeutralOddSubspace L K,
    x ∈ Submodule.orthogonal (𝕜 := ℂ) (E := poleNeutralOddSubspace L K)
      (LinearMap.ker (poleNeutralOddShiftedCanonical L K lam)) → x ≠ 0 →
    0 < (inner ℂ (poleNeutralOddShiftedCanonical L K lam x) x).re

/-- At or below both actual bottoms, both shifted operators are positive and
strictly positive on their kernel complements (existing
`nativeKernelComplement_positive`). -/
theorem PoleNeutralShiftedPositivity.of_le_bottoms {L : ℝ} (hL : 0 < L) (K : ℕ)
    (hK : 3 ≤ K) (lam : ℝ) (hE : lam ≤ poleNeutralEvenRayleighBottom L K hL hK)
    (hO : lam ≤ poleNeutralOddRayleighBottom L K hL hK) :
    PoleNeutralShiftedPositivity L K lam := by
  have hpe := poleNeutralEvenShifted_isPositive_of_le_bottom hL K hK lam hE
  have hpo := poleNeutralOddShifted_isPositive_of_le_bottom hL K hK lam hO
  refine ⟨hpe, hpo, ?_, ?_⟩
  · intro x hx hx0
    exact @nativeKernelComplement_positive (poleNeutralEvenSubspace L K) inferInstance
      (poleNeutralEven_innerProductSpace L K) inferInstance
      (poleNeutralEvenShiftedCanonical L K lam) hpe ⟨x, hx⟩
      (fun h => hx0 (congrArg Subtype.val h))
  · intro x hx hx0
    exact @nativeKernelComplement_positive (poleNeutralOddSubspace L K) inferInstance
      (poleNeutralOdd_innerProductSpace L K) inferInstance
      (poleNeutralOddShiftedCanonical L K lam) hpo ⟨x, hx⟩
      (fun h => hx0 (congrArg Subtype.val h))

/-- Tie consequences for a stored parity-tagged vector, in its own stored
parity. -/
def PoleNeutralTiedStoredGroundFacts {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (lam : ℝ) : (γ : ReversalParity) → nativePoleNeutralParitySpace γ L K → Prop
  | .even, u => PoleNeutralTiedEvenGroundFacts hL K hK lam u
  | .odd, w => PoleNeutralTiedOddGroundFacts hL K hK lam w

/-! ## Actual bottoms and the stored parity -/

/-- The stored actual value is literally the minimum of the two actual
neutral bottoms at the same aperture and cutoff. -/
theorem nativeDeepThreshold_lam_eq_min {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (s : NativeDeepThresholdGroundData L Kd D hL) :
    s.lam = min (poleNeutralEvenRayleighBottom L s.cutoff hL s.cutoff_nonempty)
      (poleNeutralOddRayleighBottom L s.cutoff hL s.cutoff_nonempty) :=
  s.lam_is_actual_global

/-- An actual nonzero even eigenvector has eigenvalue at least the even bottom. -/
theorem poleNeutralEvenRayleighBottom_le_of_eigen {L : ℝ} (hL : 0 < L) (K : ℕ)
    (hK : 3 ≤ K) (lam : ℝ) (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :
    poleNeutralEvenRayleighBottom L K hL hK ≤ lam := by
  have hb := poleNeutralEvenRayleighBottom_mul_norm_sq_le hL K hK u
  rw [hu] at hb
  have hs := @re_inner_ofReal_smul_self (poleNeutralEvenSubspace L K) inferInstance
    (poleNeutralEven_innerProductSpace L K) lam u
  have h2 : poleNeutralEvenRayleighBottom L K hL hK * ‖u‖ ^ 2 ≤ lam * ‖u‖ ^ 2 :=
    hb.trans_eq hs
  have hn : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu0) 2
  exact (mul_le_mul_iff_left₀ hn).mp h2

/-- An actual nonzero odd eigenvector has eigenvalue at least the odd bottom. -/
theorem poleNeutralOddRayleighBottom_le_of_eigen {L : ℝ} (hL : 0 < L) (K : ℕ)
    (hK : 3 ≤ K) (lam : ℝ) (w : poleNeutralOddSubspace L K) (hw0 : w ≠ 0)
    (hw : poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w) :
    poleNeutralOddRayleighBottom L K hL hK ≤ lam := by
  have hb := poleNeutralOddRayleighBottom_mul_norm_sq_le hL K hK w
  rw [hw] at hb
  have hs := @re_inner_ofReal_smul_self (poleNeutralOddSubspace L K) inferInstance
    (poleNeutralOdd_innerProductSpace L K) lam w
  have h2 : poleNeutralOddRayleighBottom L K hL hK * ‖w‖ ^ 2 ≤ lam * ‖w‖ ^ 2 :=
    hb.trans_eq hs
  have hn : 0 < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.mpr hw0) 2
  exact (mul_le_mul_iff_left₀ hn).mp h2

/-- At a strict-even comparison, a nonzero parity-tagged eigenvector at the
actual minimum is necessarily even. -/
theorem nativeParity_eq_even_of_strictEven {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (s : NativeDeepThresholdGroundData L Kd D hL)
    (hlt : poleNeutralEvenRayleighBottom L s.cutoff hL s.cutoff_nonempty <
      poleNeutralOddRayleighBottom L s.cutoff hL s.cutoff_nonempty)
    (γ : ReversalParity) (g : nativePoleNeutralParitySpace γ L s.cutoff) (hg0 : g ≠ 0)
    (hg : nativePoleNeutralParityCanonical γ L s.cutoff g = (s.lam : ℂ) • g) :
    γ = .even := by
  cases γ with
  | even => rfl
  | odd =>
    exfalso
    have hb := poleNeutralOddRayleighBottom_le_of_eigen hL s.cutoff s.cutoff_nonempty
      s.lam g hg0 hg
    have hm : s.lam = poleNeutralEvenRayleighBottom L s.cutoff hL s.cutoff_nonempty := by
      rw [nativeDeepThreshold_lam_eq_min s]
      exact min_eq_left hlt.le
    linarith

/-- At a strict-odd comparison, a nonzero parity-tagged eigenvector at the
actual minimum is necessarily odd. -/
theorem nativeParity_eq_odd_of_strictOdd {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (s : NativeDeepThresholdGroundData L Kd D hL)
    (hlt : poleNeutralOddRayleighBottom L s.cutoff hL s.cutoff_nonempty <
      poleNeutralEvenRayleighBottom L s.cutoff hL s.cutoff_nonempty)
    (γ : ReversalParity) (g : nativePoleNeutralParitySpace γ L s.cutoff) (hg0 : g ≠ 0)
    (hg : nativePoleNeutralParityCanonical γ L s.cutoff g = (s.lam : ℂ) • g) :
    γ = .odd := by
  cases γ with
  | even =>
    exfalso
    have hb := poleNeutralEvenRayleighBottom_le_of_eigen hL s.cutoff s.cutoff_nonempty
      s.lam g hg0 hg
    have hm : s.lam = poleNeutralOddRayleighBottom L s.cutoff hL s.cutoff_nonempty := by
      rw [nativeDeepThreshold_lam_eq_min s]
      exact min_eq_right hlt.le
    linarith
  | odd => rfl

/-! ## All-vector branch facts at the actual selection -/

/-- R2 and SE for every unit even eigenvector at the actual selected value,
in the strict-even branch. -/
theorem PoleNeutralStrictEvenGroundFacts.of_selection {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (hD : 0 < D) (s : NativeDeepThresholdGroundData L Kd D hL)
    (hlt : poleNeutralEvenRayleighBottom L s.cutoff hL s.cutoff_nonempty <
      poleNeutralOddRayleighBottom L s.cutoff hL s.cutoff_nonempty)
    (u : poleNeutralEvenSubspace L s.cutoff) (hu1 : ‖u‖ = 1)
    (hu : poleNeutralEvenCompressedCanonical L s.cutoff u = (s.lam : ℂ) • u) :
    PoleNeutralStrictEvenGroundFacts hL s.cutoff s.cutoff_nonempty s.lam u := by
  have hu0 : u ≠ 0 := by
    have hn : (0 : ℝ) < ‖u‖ := by rw [hu1]; exact one_pos
    exact norm_pos_iff.mp hn
  have hlamE : s.lam = poleNeutralEvenRayleighBottom L s.cutoff hL s.cutoff_nonempty := by
    rw [nativeDeepThreshold_lam_eq_min s]
    exact min_eq_left hlt.le
  have hlam : s.lam < poleNeutralOddRayleighBottom L s.cutoff hL s.cutoff_nonempty := by
    rw [hlamE]
    exact hlt
  have hray := poleNeutral_even_eigen_shiftedRay_source_eq_one hL s.cutoff
    s.cutoff_nonempty s.lam hlam u hu0 hu
  have hdet : LinearMap.det (poleNeutralEvenShiftedCanonical L s.cutoff s.lam) =
      LinearMap.det (poleNeutralOddShiftedCanonical L s.cutoff s.lam) *
        (1 - poleNeutralCorrectedCubicSource L s.cutoff
          (poleNeutralEvenShiftedRay hL s.cutoff s.cutoff_nonempty s.lam hlam)) :=
    poleNeutral_evenShifted_det_eq hL s.cutoff s.cutoff_nonempty s.lam hlam
  exact {
    lam_eq_bottom := hlamE
    below_odd := hlam
    odd_shift_inverse := fun v =>
      ⟨(poleNeutralOddShiftedCanonicalEquiv hL s.cutoff s.cutoff_nonempty s.lam hlam).apply_symm_apply v,
        (poleNeutralOddShiftedCanonicalEquiv hL s.cutoff s.cutoff_nonempty s.lam hlam).symm_apply_apply v⟩
    unit := hu1
    eigen := hu
    simple := nativeDeepThreshold_even_ground_simple hD s u hu0 hu
    source_equation := poleNeutral_even_eigen_index_odd_shifted_eq_source hL s.cutoff
      s.cutoff_nonempty s.lam u hu
    source_moment_energy :=
      poleNeutral_source_moment_energy_eq hL s.cutoff (by have := s.cutoff_nonempty; omega)
        s.lam u hu
    source_moment_gap := poleNeutral_source_moment_gap_le hL s.cutoff s.cutoff_nonempty s.lam u hu
    source_moment_pos := poleNeutral_even_eigen_source_moment_pos_of_lt_odd_bottom hL s.cutoff
      s.cutoff_nonempty s.lam u hu0 hu hlam
    momentFour_ne_zero := poleNeutral_even_eigen_momentFour_ne_zero_of_lt_odd_bottom hL s.cutoff
      s.cutoff_nonempty s.lam u hu0 hu hlam
    source_ne_zero := poleNeutral_even_eigen_source_ne_zero_of_lt_odd_bottom hL s.cutoff
      s.cutoff_nonempty s.lam hlam u hu0 hu
    ray_eq := poleNeutral_even_eigenvector_eq_source_smul_shiftedRay hL s.cutoff
      s.cutoff_nonempty s.lam hlam u hu
    ray_source_eq_one := hray
    eigen_iff := poleNeutral_evenShifted_eigen_iff hL s.cutoff s.cutoff_nonempty s.lam hlam
    det_eq := hdet
    det_eq_zero := by rw [hdet, hray, sub_self, mul_zero] }

/-- SO for every unit odd eigenvector at the actual selected value, in the
strict-odd branch. -/
theorem PoleNeutralStrictOddGroundFacts.of_selection {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (hD : 0 < D) (s : NativeDeepThresholdGroundData L Kd D hL)
    (hlt : poleNeutralOddRayleighBottom L s.cutoff hL s.cutoff_nonempty <
      poleNeutralEvenRayleighBottom L s.cutoff hL s.cutoff_nonempty)
    (w : poleNeutralOddSubspace L s.cutoff) (hw1 : ‖w‖ = 1)
    (hw : poleNeutralOddCompressedCanonical L s.cutoff w = (s.lam : ℂ) • w) :
    PoleNeutralStrictOddGroundFacts hL s.cutoff s.cutoff_nonempty s.lam w := by
  have hw0 : w ≠ 0 := by
    have hn : (0 : ℝ) < ‖w‖ := by rw [hw1]; exact one_pos
    exact norm_pos_iff.mp hn
  have hlamO : s.lam = poleNeutralOddRayleighBottom L s.cutoff hL s.cutoff_nonempty := by
    rw [nativeDeepThreshold_lam_eq_min s]
    exact min_eq_right hlt.le
  have hlam : s.lam < poleNeutralEvenRayleighBottom L s.cutoff hL s.cutoff_nonempty := by
    rw [hlamO]
    exact hlt
  have hray := poleNeutral_odd_eigen_adjointRay_pairing_eq_one hL s.cutoff
    s.cutoff_nonempty s.lam hlam w hw0 hw
  have hdet : LinearMap.det (poleNeutralOddShiftedCanonical L s.cutoff s.lam) =
      LinearMap.det (poleNeutralEvenShiftedCanonical L s.cutoff s.lam) *
        (1 - poleNeutralCubicPairingFunctional L s.cutoff
          (poleNeutralOddAdjointShiftedRay hL s.cutoff s.cutoff_nonempty s.lam hlam)) :=
    poleNeutral_oddShifted_det_eq hL s.cutoff s.cutoff_nonempty s.lam hlam
  exact {
    lam_eq_bottom := hlamO
    below_even := hlam
    even_shift_inverse := fun v =>
      ⟨(poleNeutralEvenShiftedCanonicalEquiv hL s.cutoff s.cutoff_nonempty s.lam hlam).apply_symm_apply v,
        (poleNeutralEvenShiftedCanonicalEquiv hL s.cutoff s.cutoff_nonempty s.lam hlam).symm_apply_apply v⟩
    unit := hw1
    eigen := hw
    simple := nativeDeepThreshold_odd_ground_simple hD s w hw0 hw
    adjoint_competitor := poleNeutral_odd_eigen_adjoint_competitor_eq_source hL s.cutoff
      s.cutoff_nonempty s.lam w hw
    pairing_ne_zero := poleNeutral_odd_eigen_cubic_pairing_ne_zero_of_lt_even_bottom hL s.cutoff
      s.cutoff_nonempty s.lam hlam w hw0 hw
    ray_eq := poleNeutral_odd_eigenvector_eq_pairing_smul_adjointRay hL s.cutoff
      s.cutoff_nonempty s.lam hlam w hw
    ray_pairing_eq_one := hray
    eigen_iff := poleNeutral_oddShifted_eigen_iff hL s.cutoff s.cutoff_nonempty s.lam hlam
    det_eq := hdet
    det_eq_zero := by rw [hdet, hray, sub_self, mul_zero] }

/-- Tie facts for every unit even eigenvector at the actual selected value.
The fourth moment is nonzero by the constructed simplicity; the corrected
source is not claimed nonzero. -/
theorem PoleNeutralTiedEvenGroundFacts.of_selection {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (hD : 0 < D) (s : NativeDeepThresholdGroundData L Kd D hL)
    (htie : poleNeutralEvenRayleighBottom L s.cutoff hL s.cutoff_nonempty =
      poleNeutralOddRayleighBottom L s.cutoff hL s.cutoff_nonempty)
    (u : poleNeutralEvenSubspace L s.cutoff) (hu1 : ‖u‖ = 1)
    (hu : poleNeutralEvenCompressedCanonical L s.cutoff u = (s.lam : ℂ) • u) :
    PoleNeutralTiedEvenGroundFacts hL s.cutoff s.cutoff_nonempty s.lam u := by
  have hu0 : u ≠ 0 := by
    have hn : (0 : ℝ) < ‖u‖ := by rw [hu1]; exact one_pos
    exact norm_pos_iff.mp hn
  have hlamO : s.lam = poleNeutralOddRayleighBottom L s.cutoff hL s.cutoff_nonempty := by
    rw [nativeDeepThreshold_lam_eq_min s, htie]
    exact min_self _
  obtain ⟨hr, hresp⟩ :=
    (poleNeutral_tied_complementary_response hL s.cutoff s.cutoff_nonempty s.lam).1 u hu
  have hgap := poleNeutral_source_moment_gap_le hL s.cutoff s.cutoff_nonempty s.lam u hu
  rw [← hlamO, sub_self, zero_mul] at hgap
  exact {
    unit := hu1
    eigen := hu
    simple := nativeDeepThreshold_even_ground_simple hD s u hu0 hu
    source_equation := poleNeutral_even_eigen_index_odd_shifted_eq_source hL s.cutoff
      s.cutoff_nonempty s.lam u hu
    momentFour_ne_zero := nativeDeepThreshold_even_ground_momentFour_ne_zero hD s u hu0 hu
    source_moment_energy :=
      poleNeutral_source_moment_energy_eq hL s.cutoff (by have := s.cutoff_nonempty; omega)
        s.lam u hu
    source_moment_nonneg := hgap
    kernel_compatibility := poleNeutral_even_eigen_shifted_kernel_compatibility hL s.cutoff
      s.cutoff_nonempty s.lam u hu
    range_mem := hr
    complementary_response := hresp }

/-- Tie facts for every unit odd eigenvector at the actual selected value,
with the actual adjoint source and its required minus sign. -/
theorem PoleNeutralTiedOddGroundFacts.of_selection {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (hD : 0 < D) (s : NativeDeepThresholdGroundData L Kd D hL)
    (w : poleNeutralOddSubspace L s.cutoff) (hw1 : ‖w‖ = 1)
    (hw : poleNeutralOddCompressedCanonical L s.cutoff w = (s.lam : ℂ) • w) :
    PoleNeutralTiedOddGroundFacts hL s.cutoff s.cutoff_nonempty s.lam w := by
  have hw0 : w ≠ 0 := by
    have hn : (0 : ℝ) < ‖w‖ := by rw [hw1]; exact one_pos
    exact norm_pos_iff.mp hn
  obtain ⟨hr, hresp⟩ :=
    (poleNeutral_tied_complementary_response hL s.cutoff s.cutoff_nonempty s.lam).2 w hw
  exact {
    unit := hw1
    eigen := hw
    simple := nativeDeepThreshold_odd_ground_simple hD s w hw0 hw
    adjoint_competitor := poleNeutral_odd_eigen_adjoint_competitor_eq_source hL s.cutoff
      s.cutoff_nonempty s.lam w hw
    kernel_compatibility := poleNeutral_odd_eigen_shifted_kernel_compatibility hL s.cutoff
      s.cutoff_nonempty s.lam w hw
    range_mem := hr
    complementary_response := hresp }

/-- Tie facts for a unit parity-tagged eigenvector, in its own parity. -/
theorem PoleNeutralTiedStoredGroundFacts.of_selection {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (hD : 0 < D) (s : NativeDeepThresholdGroundData L Kd D hL)
    (htie : poleNeutralEvenRayleighBottom L s.cutoff hL s.cutoff_nonempty =
      poleNeutralOddRayleighBottom L s.cutoff hL s.cutoff_nonempty)
    (γ : ReversalParity) (g : nativePoleNeutralParitySpace γ L s.cutoff) (hg1 : ‖g‖ = 1)
    (hg : nativePoleNeutralParityCanonical γ L s.cutoff g = (s.lam : ℂ) • g) :
    PoleNeutralTiedStoredGroundFacts hL s.cutoff s.cutoff_nonempty s.lam γ g := by
  cases γ with
  | even => exact PoleNeutralTiedEvenGroundFacts.of_selection hD s htie g hg1 hg
  | odd => exact PoleNeutralTiedOddGroundFacts.of_selection hD s g hg1 hg

/-- Reading stored tie facts through the even view. -/
theorem PoleNeutralTiedStoredGroundFacts.even_view {L : ℝ} {hL : 0 < L} {K : ℕ}
    {hK : 3 ≤ K} {lam : ℝ} {γ : ReversalParity} {g : nativePoleNeutralParitySpace γ L K}
    (h : PoleNeutralTiedStoredGroundFacts hL K hK lam γ g) (hγ : γ = .even) :
    PoleNeutralTiedEvenGroundFacts hL K hK lam (nativeParityEvenView γ hγ g) := by
  subst hγ
  exact h

/-- Reading stored tie facts through the odd view. -/
theorem PoleNeutralTiedStoredGroundFacts.odd_view {L : ℝ} {hL : 0 < L} {K : ℕ}
    {hK : 3 ≤ K} {lam : ℝ} {γ : ReversalParity} {g : nativePoleNeutralParitySpace γ L K}
    (h : PoleNeutralTiedStoredGroundFacts hL K hK lam γ g) (hγ : γ = .odd) :
    PoleNeutralTiedOddGroundFacts hL K hK lam (nativeParityOddView γ hγ g) := by
  subst hγ
  exact h

/-! ## The trichotomy on the stored retained state -/

/-- N21 branch record for the ACTUAL retained state: the actual neutral
bottoms at the stored aperture and stored selected cutoff are compared,
and each outcome carries its consequences about the STORED selected
ground and the STORED value `lam`. -/
inductive DetectorRetainedSelectedGroundBranch {σ : ReversalParity} {L : ℝ} {Kd : ℕ}
    {D : ℝ} {hL : 0 < L} (state : DetectorRetainedSchurState σ L Kd D hL) : Prop where
  | strictEven
      (gap : poleNeutralEvenRayleighBottom L state.selection.cutoff hL
          state.selection.cutoff_nonempty <
        poleNeutralOddRayleighBottom L state.selection.cutoff hL state.selection.cutoff_nonempty)
      (parity : state.selectedParity = .even)
      (facts : PoleNeutralStrictEvenGroundFacts hL state.selection.cutoff
        state.selection.cutoff_nonempty state.selection.lam
        (nativeParityEvenView state.selectedParity parity state.selectedGround))
  | strictOdd
      (gap : poleNeutralOddRayleighBottom L state.selection.cutoff hL
          state.selection.cutoff_nonempty <
        poleNeutralEvenRayleighBottom L state.selection.cutoff hL state.selection.cutoff_nonempty)
      (parity : state.selectedParity = .odd)
      (facts : PoleNeutralStrictOddGroundFacts hL state.selection.cutoff
        state.selection.cutoff_nonempty state.selection.lam
        (nativeParityOddView state.selectedParity parity state.selectedGround))
  | tie
      (equal : poleNeutralEvenRayleighBottom L state.selection.cutoff hL
          state.selection.cutoff_nonempty =
        poleNeutralOddRayleighBottom L state.selection.cutoff hL state.selection.cutoff_nonempty)
      (lam_eq_even : state.selection.lam =
        poleNeutralEvenRayleighBottom L state.selection.cutoff hL state.selection.cutoff_nonempty)
      (lam_eq_odd : state.selection.lam =
        poleNeutralOddRayleighBottom L state.selection.cutoff hL state.selection.cutoff_nonempty)
      (positivity : PoleNeutralShiftedPositivity L state.selection.cutoff state.selection.lam)
      (facts : PoleNeutralTiedStoredGroundFacts hL state.selection.cutoff
        state.selection.cutoff_nonempty state.selection.lam
        state.selectedParity state.selectedGround)

/-- The trichotomy holds for every actual retained state, with the branch
facts instantiated on its stored selected ground. -/
theorem DetectorRetainedSchurState.selectedGround_branch {σ : ReversalParity} {L : ℝ}
    {Kd : ℕ} {D : ℝ} {hL : 0 < L} (state : DetectorRetainedSchurState σ L Kd D hL) :
    DetectorRetainedSelectedGroundBranch state := by
  have hg0 : state.selectedGround ≠ 0 := by
    intro hz
    have h := state.selectedGround_unit
    rw [hz, norm_zero] at h
    exact zero_ne_one h
  rcases lt_trichotomy
      (poleNeutralEvenRayleighBottom L state.selection.cutoff hL state.selection.cutoff_nonempty)
      (poleNeutralOddRayleighBottom L state.selection.cutoff hL state.selection.cutoff_nonempty)
    with h | h | h
  · have hpar := nativeParity_eq_even_of_strictEven state.selection h
      state.selectedParity state.selectedGround hg0 state.selectedGround_eigen
    refine .strictEven h hpar ?_
    exact PoleNeutralStrictEvenGroundFacts.of_selection state.depth_pos state.selection h _
      ((nativeParityEvenView_norm _ hpar _).trans state.selectedGround_unit)
      (nativeParityEvenView_eigen _ hpar _ _ state.selectedGround_eigen)
  · have hlamE : state.selection.lam =
        poleNeutralEvenRayleighBottom L state.selection.cutoff hL
          state.selection.cutoff_nonempty := by
      rw [nativeDeepThreshold_lam_eq_min state.selection, ← h]
      exact min_self _
    have hlamO := hlamE.trans h
    exact .tie h hlamE hlamO
      (PoleNeutralShiftedPositivity.of_le_bottoms hL _ _ _ hlamE.le hlamO.le)
      (PoleNeutralTiedStoredGroundFacts.of_selection state.depth_pos state.selection h
        state.selectedParity state.selectedGround state.selectedGround_unit
        state.selectedGround_eigen)
  · have hpar := nativeParity_eq_odd_of_strictOdd state.selection h
      state.selectedParity state.selectedGround hg0 state.selectedGround_eigen
    refine .strictOdd h hpar ?_
    exact PoleNeutralStrictOddGroundFacts.of_selection state.depth_pos state.selection h _
      ((nativeParityOddView_norm _ hpar _).trans state.selectedGround_unit)
      (nativeParityOddView_eigen _ hpar _ _ state.selectedGround_eigen)

/-! ## The same facts indexed by the existing neutral-bottom tag -/

/-- Branch consequences on the STORED selected ground, indexed by the
existing native neutral-bottom tag `PoleNeutralGroundBranch` at the stored
aperture and stored selected cutoff.  The tag carries only the comparison of
the actual bottoms; the selected parity is a separate stored field, and in
the strict branches its value is part of the conclusion. -/
def DetectorRetainedSchurState.groundBranchFacts {σ : ReversalParity} {L : ℝ} {Kd : ℕ}
    {D : ℝ} {hL : 0 < L} (state : DetectorRetainedSchurState σ L Kd D hL) :
    PoleNeutralGroundBranch L state.selection.cutoff hL state.selection.cutoff_nonempty → Prop
  | .strictEven _ => ∃ parity : state.selectedParity = .even,
      PoleNeutralStrictEvenGroundFacts hL state.selection.cutoff
        state.selection.cutoff_nonempty state.selection.lam
        (nativeParityEvenView state.selectedParity parity state.selectedGround)
  | .strictOdd _ => ∃ parity : state.selectedParity = .odd,
      PoleNeutralStrictOddGroundFacts hL state.selection.cutoff
        state.selection.cutoff_nonempty state.selection.lam
        (nativeParityOddView state.selectedParity parity state.selectedGround)
  | .tie _ =>
      state.selection.lam =
          poleNeutralEvenRayleighBottom L state.selection.cutoff hL
            state.selection.cutoff_nonempty ∧
        state.selection.lam =
          poleNeutralOddRayleighBottom L state.selection.cutoff hL
            state.selection.cutoff_nonempty ∧
        PoleNeutralShiftedPositivity L state.selection.cutoff state.selection.lam ∧
        PoleNeutralTiedStoredGroundFacts hL state.selection.cutoff
          state.selection.cutoff_nonempty state.selection.lam
          state.selectedParity state.selectedGround

/-- Whatever value of the existing tag is taken, its branch consequences
hold for the stored selected ground. -/
theorem DetectorRetainedSchurState.groundBranchFacts_holds {σ : ReversalParity} {L : ℝ}
    {Kd : ℕ} {D : ℝ} {hL : 0 < L} (state : DetectorRetainedSchurState σ L Kd D hL)
    (b : PoleNeutralGroundBranch L state.selection.cutoff hL state.selection.cutoff_nonempty) :
    state.groundBranchFacts b := by
  cases b with
  | strictEven gap =>
    rcases state.selectedGround_branch with ⟨_, hpar, hf⟩ | ⟨h, _, _⟩ | ⟨h, _, _, _, _⟩
    · exact Exists.intro hpar hf
    · exact absurd gap (lt_asymm h)
    · exact absurd h (ne_of_lt gap)
  | strictOdd gap =>
    rcases state.selectedGround_branch with ⟨h, _, _⟩ | ⟨_, hpar, hf⟩ | ⟨h, _, _, _, _⟩
    · exact absurd gap (lt_asymm h)
    · exact Exists.intro hpar hf
    · exact absurd h.symm (ne_of_lt gap)
  | tie equal =>
    rcases state.selectedGround_branch with ⟨h, _, _⟩ | ⟨h, _, _⟩ | ⟨_, hE, hO, hp, hf⟩
    · exact absurd equal (ne_of_lt h)
    · exact absurd equal.symm (ne_of_lt h)
    · exact And.intro hE (And.intro hO (And.intro hp hf))

/-! ## N21 on the actual stored output packet -/

/-- N21 for the actual stored packet: the trichotomy of the actual
neutral bottoms at the stored aperture and stored selected cutoff, with
every branch consequence stated about `out.selectedGround` and the stored
`lam`. -/
theorem Step123NativeOutput.n21_retained_branch {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    DetectorRetainedSelectedGroundBranch out.retained.state :=
  out.retained.state.selectedGround_branch

/-- N21 indexed by the existing tag on the actual stored packet: for every
value of `PoleNeutralGroundBranch` at the stored aperture and stored
selected cutoff, its consequences hold for `out.selectedGround`. -/
theorem Step123NativeOutput.n21_groundBranch_facts {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (b : PoleNeutralGroundBranch (fixedOriginalSincTrialAperture a)
      out.retained.state.selection.cutoff out.aperture_pos
      out.retained.state.selection.cutoff_nonempty) :
    out.retained.state.groundBranchFacts b :=
  out.retained.state.groundBranchFacts_holds b

/-- The stored selected ground, in every branch, has a nonzero shell
coordinate in the kernel of the actual selected-ground Schur operator and
its exact predecessor response (existing `NativeSelectedGroundSchur`
package, instantiated on the stored eigenpair and the stored inverses). -/
theorem Step123NativeOutput.n21_selectedGround_shell_kernel {β : ℝ} {σ : ReversalParity}
    {a : ℝ} (out : Step123NativeOutput β σ a) :
    let γ := out.retained.state.selectedParity
    let s := out.retained.state.selection
    let J := nativeSelectedGroundPredecessorEmbedding γ s
    let T := nativePoleNeutralParityShifted γ (fixedOriginalSincTrialAperture a) s.cutoff s.lam
    let P := nativeSelectedGroundPredecessorEquiv γ out.retained.state.inverses
    let x := J.toLinearMap.adjoint out.selectedGround
    let y := isometricDetectorComplementCoordinate J out.selectedGround
    y ≠ 0 ∧ x = -isometricDetectorResponse J T P y ∧
      nativeSelectedGroundSchurOperator γ out.retained.state.inverses y = 0 := by
  have hg0 : out.retained.state.selectedGround ≠ 0 := by
    intro hz
    have h := out.retained.state.selectedGround_unit
    rw [hz, norm_zero] at h
    exact zero_ne_one h
  exact nativeSelectedGroundSchur_kernel_package out.retained.state.selectedParity
    out.retained.state.inverses out.retained.state.selectedGround hg0
    out.retained.state.selectedGround_eigen

/-- The MC08 consumer strengthened as the review asks: the stored eigenpair
together with an actual value of the existing neutral-bottom tag (at the
same aperture and cutoff, with the selector's own nonemptiness proof) whose
branch consequences are instantiated on that same stored eigenpair, rather
than a bare `Nonempty` of the tag. -/
theorem Step123NativeOutput.n21_selected_ground_branch_consumer {β : ℝ}
    {σ : ReversalParity} {a : ℝ} (out : Step123NativeOutput β σ a) :
    (‖out.selectedGround‖ = 1 ∧
      nativePoleNeutralParityCanonical out.retained.state.selectedParity
        (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.selectedGround =
        (out.retained.state.selection.lam : ℂ) • out.selectedGround) ∧
    ∃ b : PoleNeutralGroundBranch (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.source_selector.cutoff_nonempty,
      out.retained.state.groundBranchFacts b := by
  obtain ⟨b⟩ := poleNeutralGround_branch_exhaustive out.aperture_pos
    out.retained.state.selection.cutoff out.source_selector.cutoff_nonempty
  exact ⟨⟨out.retained.state.selectedGround_unit, out.retained.state.selectedGround_eigen⟩,
    b, out.retained.state.groundBranchFacts_holds b⟩

/-- N21 bundled with the stored eigenpair it is instantiated on, the
literal identification of `lam` as the minimum of the two actual bottoms
at the same aperture and cutoff, the trichotomy with branch facts on the
stored ground, and the stored ground's selected-shell Schur kernel
package. -/
theorem Step123NativeOutput.n21_retained_branch_package {β : ℝ} {σ : ReversalParity}
    {a : ℝ} (out : Step123NativeOutput β σ a) :
    (‖out.selectedGround‖ = 1 ∧
      nativePoleNeutralParityCanonical out.retained.state.selectedParity
        (fixedOriginalSincTrialAperture a) out.retained.state.selection.cutoff
        out.selectedGround =
        (out.retained.state.selection.lam : ℂ) • out.selectedGround) ∧
    out.retained.state.selection.lam =
      min (poleNeutralEvenRayleighBottom (fixedOriginalSincTrialAperture a)
          out.retained.state.selection.cutoff out.aperture_pos
          out.retained.state.selection.cutoff_nonempty)
        (poleNeutralOddRayleighBottom (fixedOriginalSincTrialAperture a)
          out.retained.state.selection.cutoff out.aperture_pos
          out.retained.state.selection.cutoff_nonempty) ∧
    DetectorRetainedSelectedGroundBranch out.retained.state ∧
    (let γ := out.retained.state.selectedParity
     let s := out.retained.state.selection
     let J := nativeSelectedGroundPredecessorEmbedding γ s
     let T := nativePoleNeutralParityShifted γ (fixedOriginalSincTrialAperture a) s.cutoff s.lam
     let P := nativeSelectedGroundPredecessorEquiv γ out.retained.state.inverses
     let x := J.toLinearMap.adjoint out.selectedGround
     let y := isometricDetectorComplementCoordinate J out.selectedGround
     y ≠ 0 ∧ x = -isometricDetectorResponse J T P y ∧
       nativeSelectedGroundSchurOperator γ out.retained.state.inverses y = 0) :=
  ⟨⟨out.retained.state.selectedGround_unit, out.retained.state.selectedGround_eigen⟩,
    nativeDeepThreshold_lam_eq_min out.retained.state.selection,
    out.n21_retained_branch, out.n21_selectedGround_shell_kernel⟩

/-- Strict-even view on the actual stored packet: the stored parity is even
and the stored ground carries R2 and SE. -/
theorem Step123NativeOutput.n21_strictEven_selectedGround {β : ℝ} {σ : ReversalParity}
    {a : ℝ} (out : Step123NativeOutput β σ a)
    (hgap : poleNeutralEvenRayleighBottom (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty <
      poleNeutralOddRayleighBottom (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty) :
    ∃ hpar : out.retained.state.selectedParity = .even,
      PoleNeutralStrictEvenGroundFacts out.aperture_pos out.retained.state.selection.cutoff
        out.retained.state.selection.cutoff_nonempty out.retained.state.selection.lam
        (nativeParityEvenView out.retained.state.selectedParity hpar out.selectedGround) :=
  out.retained.state.groundBranchFacts_holds (.strictEven hgap)

/-- Strict-odd view on the actual stored packet: the stored parity is odd
and the stored ground carries SO. -/
theorem Step123NativeOutput.n21_strictOdd_selectedGround {β : ℝ} {σ : ReversalParity}
    {a : ℝ} (out : Step123NativeOutput β σ a)
    (hgap : poleNeutralOddRayleighBottom (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty <
      poleNeutralEvenRayleighBottom (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty) :
    ∃ hpar : out.retained.state.selectedParity = .odd,
      PoleNeutralStrictOddGroundFacts out.aperture_pos out.retained.state.selection.cutoff
        out.retained.state.selection.cutoff_nonempty out.retained.state.selection.lam
        (nativeParityOddView out.retained.state.selectedParity hpar out.selectedGround) :=
  out.retained.state.groundBranchFacts_holds (.strictOdd hgap)

/-- Tie view on the actual stored packet: `lam` equals both actual bottoms,
both shifted operators at the stored `lam` are positive (strictly on their
kernel complements) and the stored ground, in its stored parity, carries
its rank-one source equation, kernel compatibility, range membership and
the complementary response with retained kernel component.  No `S0 ≠ 0`
claim. -/
theorem Step123NativeOutput.n21_tie_selectedGround {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (htie : poleNeutralEvenRayleighBottom (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty =
      poleNeutralOddRayleighBottom (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty) :
    out.retained.state.selection.lam =
        poleNeutralEvenRayleighBottom (fixedOriginalSincTrialAperture a)
          out.retained.state.selection.cutoff out.aperture_pos
          out.retained.state.selection.cutoff_nonempty ∧
      out.retained.state.selection.lam =
        poleNeutralOddRayleighBottom (fixedOriginalSincTrialAperture a)
          out.retained.state.selection.cutoff out.aperture_pos
          out.retained.state.selection.cutoff_nonempty ∧
      PoleNeutralShiftedPositivity (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.retained.state.selection.lam ∧
      PoleNeutralTiedStoredGroundFacts out.aperture_pos out.retained.state.selection.cutoff
        out.retained.state.selection.cutoff_nonempty out.retained.state.selection.lam
        out.retained.state.selectedParity out.selectedGround :=
  out.retained.state.groundBranchFacts_holds (.tie htie)

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeParityEvenView_sigma
#print axioms Zeta23.CCM.nativeParityOddView_sigma
#print axioms Zeta23.CCM.nativeParityEvenView_ambient
#print axioms Zeta23.CCM.nativeParityOddView_ambient
#print axioms Zeta23.CCM.nativeParityEvenView_norm
#print axioms Zeta23.CCM.nativeParityOddView_norm
#print axioms Zeta23.CCM.nativeParityEvenView_eigen
#print axioms Zeta23.CCM.nativeParityOddView_eigen
#print axioms Zeta23.CCM.nativeDeepThreshold_lam_eq_min
#print axioms Zeta23.CCM.poleNeutral_even_eigen_index_odd_shifted_eq_source
#print axioms Zeta23.CCM.poleNeutralEvenRayleighBottom_le_of_eigen
#print axioms Zeta23.CCM.poleNeutralOddRayleighBottom_le_of_eigen
#print axioms Zeta23.CCM.nativeParity_eq_even_of_strictEven
#print axioms Zeta23.CCM.nativeParity_eq_odd_of_strictOdd
#print axioms Zeta23.CCM.PoleNeutralStrictEvenGroundFacts.of_selection
#print axioms Zeta23.CCM.PoleNeutralStrictOddGroundFacts.of_selection
#print axioms Zeta23.CCM.PoleNeutralTiedEvenGroundFacts.of_selection
#print axioms Zeta23.CCM.PoleNeutralTiedOddGroundFacts.of_selection
#print axioms Zeta23.CCM.PoleNeutralShiftedPositivity.of_le_bottoms
#print axioms Zeta23.CCM.PoleNeutralTiedStoredGroundFacts.of_selection
#print axioms Zeta23.CCM.PoleNeutralTiedStoredGroundFacts.even_view
#print axioms Zeta23.CCM.PoleNeutralTiedStoredGroundFacts.odd_view
#print axioms Zeta23.CCM.DetectorRetainedSchurState.selectedGround_branch
#print axioms Zeta23.CCM.DetectorRetainedSchurState.groundBranchFacts_holds
#print axioms Zeta23.CCM.Step123NativeOutput.n21_retained_branch
#print axioms Zeta23.CCM.Step123NativeOutput.n21_groundBranch_facts
#print axioms Zeta23.CCM.Step123NativeOutput.n21_selectedGround_shell_kernel
#print axioms Zeta23.CCM.Step123NativeOutput.n21_selected_ground_branch_consumer
#print axioms Zeta23.CCM.Step123NativeOutput.n21_retained_branch_package
#print axioms Zeta23.CCM.Step123NativeOutput.n21_strictEven_selectedGround
#print axioms Zeta23.CCM.Step123NativeOutput.n21_strictOdd_selectedGround
#print axioms Zeta23.CCM.Step123NativeOutput.n21_tie_selectedGround
