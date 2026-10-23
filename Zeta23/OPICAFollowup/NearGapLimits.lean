import Zeta23.OPICAFollowup.DilatedComb
import Zeta23.OPICA.SignedHeatSeparator

/-! Actual near-gap Jordan-measure budget, the explicit CT1 dilation family and
the quantitative HT2 controlled limit. The CT1 normalized nonmeasure limit
remains OPEN until its own root and consumers pass. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology FourierTransform SchwartzMap ENNReal NNReal
namespace Zeta23.OPICAFollowup
open Zeta23.OPICA

def hasNearGap (nu : LocallyFiniteSignedMeasure) (a : ℝ) : Prop :=
  nu.positive (Ioo (-a) a)=0 ∧ nu.negative (Ioo (-a) a)=0

/-- The actual canonical Jordan carrier for the CT1 auxiliary dilation defect.
It represents D_L + D_(-L) - 2 cosh(L/2) D_0.  Canonicalization is
necessary: scaled lattice supports can meet the integer lattice, so the
uncancelled positive/negative measures need not be mutually singular. -/
def nearGapCombFamily (L : ℝ) : LocallyFiniteSignedMeasure :=
  localJordanAdd
    (localJordanAdd (dilatedCombJordan L) (dilatedCombJordan (-L)))
    (localJordanScale (-(2 * Real.cosh (L / 2))) (dilatedCombJordan 0))

/-- The original CT1 signed dilation identity holds as an equality of
actual finite signed measures on every compact set. This is stronger than a
formal Schwartz coefficient calculation: the construction already resolves
overlaps of the three lattice supports by its canonical Jordan operations. -/
theorem nearGapCombFamily_compactRestriction (L : ℝ)
    (K : Set ℝ) (hK : IsCompact K) :
    localSignedCompactRestriction (nearGapCombFamily L) K hK =
      localSignedCompactRestriction (dilatedCombJordan L) K hK +
      localSignedCompactRestriction (dilatedCombJordan (-L)) K hK -
      (2 * Real.cosh (L / 2)) •
        localSignedCompactRestriction (dilatedCombJordan 0) K hK := by
  unfold nearGapCombFamily
  rw [localJordanAdd_compactRestriction, localJordanAdd_compactRestriction,
    localJordanScale_compactRestriction]
  first
    | rw [sub_eq_add_neg, neg_smul]
    | (ext s hs; simp [sub_eq_add_neg])

/-- Explicit CT1 Fourier source before transporting the identity through
canonical locally finite Jordan measures. The use of the real scalar
2 cosh(L/2) keeps the original paper's exact normalization. -/
def nearGapExplicitDilationDistribution (L : ℝ) : TemperedDistribution ℝ ℂ :=
  dilatedCombDistribution L + dilatedCombDistribution (-L) -
    ((2 * Real.cosh (L / 2) : ℝ) : ℂ) • dilatedCombDistribution 0

/-- The genuine scaled Poisson-summation identities show that the explicit
three-comb CT1 distribution is Fourier self-dual for EVERY real L. This
does not yet identify it with the canonical Jordan distribution; that
independent physical-equality bridge remains required for the original
dilation_near_gap_family root. -/
theorem nearGapExplicitDilationDistribution_selfdual (L : ℝ) :
    𝓕 (nearGapExplicitDilationDistribution L) =
      nearGapExplicitDilationDistribution L := by
  have hL := (dilated_comb_fourier L).2.2
  have hminus := (dilated_comb_fourier (-L)).2.2
  have hzero := (dilated_comb_fourier 0).2.2
  unfold nearGapExplicitDilationDistribution
  simp only [sub_eq_add_neg, FourierTransform.fourier_add,
    FourierTransform.fourier_neg, FourierTransform.fourier_smul,
    hL, hminus, hzero, neg_neg, neg_zero]
  abel

/-- Exact cancellation of the origin coefficient in the CT1 signed dilation
comb.  This is the coefficient identity; its realization as an atom of the
canonical Jordan carrier is a separate physical measure obligation. -/
theorem nearGapComb_origin_coefficient_zero (L : ℝ) :
    Real.exp (L / 2) + Real.exp (-L / 2) -
      2 * Real.cosh (L / 2) = 0 := by
  rw [Real.cosh_eq]
  have hneg : -(L / 2) = -L / 2 := by ring
  rw [hneg]
  ring

/-- The actual positive dilated counting measure assigns its prescribed
atom at the origin, after compact restriction and signed Jordan embedding.
This is a physical measure statement, not just the formal coefficient law. -/
theorem nearGap_dilatedComb_origin_signed (t : ℝ) :
    localSignedCompactRestriction (dilatedCombJordan t)
      ({0} : Set ℝ) isCompact_singleton ({0} : Set ℝ) =
        Real.exp (t / 2) := by
  rw [localSignedCompactRestriction_apply _ _ _
    ({0} : Set ℝ) (measurableSet_singleton 0)]
  have hmass :
      ((dilatedCombMeasure t).restrict ({0} : Set ℝ)).real
        ({0} : Set ℝ) = Real.exp (t / 2) := by
    change (((dilatedCombMeasure t).restrict ({0} : Set ℝ))
      ({0} : Set ℝ)).toReal = Real.exp (t / 2)
    rw [Measure.restrict_apply (measurableSet_singleton (0 : ℝ))]
    simp only [inter_self]
    rw [dilatedCombMeasure_origin,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simpa [dilatedCombJordan, localJordanDifference] using hmass

/-- Mutual singularity prevents cancellation of nonzero Jordan atoms
at a SINGLE point. Thus a vanishing real signed evaluation forces the
positive and negative atoms to vanish separately. Local finiteness
rules out the misleading toReal(∞) = 0 possibility. -/
theorem nearGap_jordan_singleton_of_signed_zero
    (mu : LocallyFiniteSignedMeasure) (x : ℝ)
    (hzero : localSignedCompactRestriction mu ({x} : Set ℝ)
      isCompact_singleton ({x} : Set ℝ) = 0) :
    mu.positive ({x} : Set ℝ) = 0 ∧
      mu.negative ({x} : Set ℝ) = 0 := by
  have hreal : mu.positive.real ({x} : Set ℝ) =
      mu.negative.real ({x} : Set ℝ) := by
    rw [localSignedCompactRestriction_apply _ _ _ _
      (measurableSet_singleton x)] at hzero
    simp only [Measure.real,
      Measure.restrict_apply (measurableSet_singleton x),
      inter_self] at hzero
    exact sub_eq_zero.mp hzero
  obtain ⟨s, hs, hposnull, hnegnull⟩ := mu.mutuallySingular
  by_cases hx : x ∈ s
  · have hsub : ({x} : Set ℝ) ⊆ s := by
      intro y hy
      rcases mem_singleton_iff.mp hy with rfl
      exact hx
    have hp : mu.positive ({x} : Set ℝ) = 0 :=
      measure_mono_null hsub hposnull
    refine ⟨hp, ?_⟩
    have hpReal : mu.positive.real ({x} : Set ℝ) = 0 := by
      simp [Measure.real, hp]
    have hnReal : mu.negative.real ({x} : Set ℝ) = 0 := by
      rw [← hreal]
      exact hpReal
    exact (measureReal_eq_zero_iff
      (isCompact_singleton.measure_lt_top.ne)).mp hnReal
  · have hsub : ({x} : Set ℝ) ⊆ sᶜ := by
      intro y hy
      rcases mem_singleton_iff.mp hy with rfl
      exact hx
    have hn : mu.negative ({x} : Set ℝ) = 0 :=
      measure_mono_null hsub hnegnull
    refine ⟨?_, hn⟩
    have hnReal : mu.negative.real ({x} : Set ℝ) = 0 := by
      simp [Measure.real, hn]
    have hpReal : mu.positive.real ({x} : Set ℝ) = 0 :=
      hreal.trans hnReal
    exact (measureReal_eq_zero_iff
      (isCompact_singleton.measure_lt_top.ne)).mp hpReal

/-- The genuine CT1 signed measure has zero mass at its origin on the
finite singleton restriction. This closes the physical origin cancellation
step, separately from Jordan-part nonnegativity, gap and Fourier properties. -/
theorem nearGapCombFamily_origin_signed_zero (L : ℝ) :
    localSignedCompactRestriction (nearGapCombFamily L)
      ({0} : Set ℝ) isCompact_singleton ({0} : Set ℝ) = 0 := by
  have h := congrArg (fun m : SignedMeasure ℝ => m ({0} : Set ℝ))
    (nearGapCombFamily_compactRestriction L ({0} : Set ℝ) isCompact_singleton)
  simp only [_root_.add_apply, _root_.sub_apply, smul_apply,
    smul_eq_mul, nearGap_dilatedComb_origin_signed,
    Real.exp_zero, zero_div, neg_div, mul_one] at h
  have hc := nearGapComb_origin_coefficient_zero L
  rw [neg_div] at hc
  exact h.trans hc

/-- Full canonical Jordan origin cancellation of the genuine CT1
signed measure, not merely its signed scalar coefficient. -/
theorem nearGapCombFamily_origin_jordan_zero (L : ℝ) :
    (nearGapCombFamily L).positive ({0} : Set ℝ) = 0 ∧
      (nearGapCombFamily L).negative ({0} : Set ℝ) = 0 :=
  nearGap_jordan_singleton_of_signed_zero
    (nearGapCombFamily L) 0 (nearGapCombFamily_origin_signed_zero L)

/-- Local Jordan evaluation of an origin atom is independent of the compact
collar, provided the collar actually contains the origin. This is an
ordinary measure restriction identity, not a special CT1 hypothesis. -/
theorem nearGap_signed_origin_restriction_of_mem
    (mu : LocallyFiniteSignedMeasure) (K : Set ℝ) (hK : IsCompact K)
    (h0 : (0 : ℝ) ∈ K) :
    localSignedCompactRestriction mu K hK ({0} : Set ℝ) =
      localSignedCompactRestriction mu ({0} : Set ℝ)
        isCompact_singleton ({0} : Set ℝ) := by
  have hset : ({0} : Set ℝ) ∩ K = ({0} : Set ℝ) := by
    ext x
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · exact And.left
    · intro hx
      subst x
      exact ⟨rfl, h0⟩
  rw [localSignedCompactRestriction_apply _ _ _ _
        (measurableSet_singleton (0 : ℝ)),
      localSignedCompactRestriction_apply _ _ _ _
        (measurableSet_singleton (0 : ℝ))]
  simp only [Measure.real,
    Measure.restrict_apply (measurableSet_singleton (0 : ℝ)),
    hset, inter_self]

/-- The physical signed origin cancellation of the CT1 measure survives
every genuine compact restriction containing zero. The zero atom cannot
be hidden by choosing a different compact cutoff. -/
theorem nearGapCombFamily_origin_signed_zero_on_compact (L : ℝ)
    (K : Set ℝ) (hK : IsCompact K) (h0 : (0 : ℝ) ∈ K) :
    localSignedCompactRestriction (nearGapCombFamily L) K hK
      ({0} : Set ℝ) = 0 := by
  rw [nearGap_signed_origin_restriction_of_mem
    (nearGapCombFamily L) K hK h0]
  exact nearGapCombFamily_origin_signed_zero L

/-- All three actual positive lattice carriers vanish on the same
punctured interval (-exp(-L), exp(-L)) whenever L is nonnegative.
This is source-backed support, not a stipulated signed gap; the origin
atom is deliberately excluded and handled separately. -/
theorem nearGapComb_three_carriers_punctured_gap {L : ℝ} (hL : 0 ≤ L) :
    dilatedCombMeasure L
      (Ioo (-Real.exp (-L)) (Real.exp (-L)) \ ({0} : Set ℝ)) = 0 ∧
    dilatedCombMeasure (-L)
      (Ioo (-Real.exp (-L)) (Real.exp (-L)) \ ({0} : Set ℝ)) = 0 ∧
    dilatedCombMeasure 0
      (Ioo (-Real.exp (-L)) (Real.exp (-L)) \ ({0} : Set ℝ)) = 0 := by
  have hwide : Real.exp (-L) ≤ Real.exp L :=
    Real.exp_le_exp.mpr (by linarith)
  have hone : Real.exp (-L) ≤ Real.exp (0 : ℝ) :=
    Real.exp_le_exp.mpr (by linarith)
  exact ⟨dilatedCombMeasure_punctured_gap_of_le L _ hwide,
    dilatedCombMeasure_punctured_gap_of_le (-L) _ le_rfl,
    dilatedCombMeasure_punctured_gap_of_le 0 _ hone⟩

/-- The genuine CT1 signed Jordan measure vanishes on the punctured
first-cell gap, evaluated on an arbitrary compact restriction. The proof
uses the three actual positive counting carriers, the canonical Jordan
compact identity, and no hypothesized Fourier or positivity property.
Origin cancellation is a separate established candidate. -/
theorem nearGapCombFamily_punctured_gap_signed
    {L : ℝ} (hL : 0 ≤ L) (K : Set ℝ) (hK : IsCompact K) :
    localSignedCompactRestriction (nearGapCombFamily L) K hK
      (Ioo (-Real.exp (-L)) (Real.exp (-L)) \ ({0} : Set ℝ)) = 0 := by
  let E : Set ℝ :=
    Ioo (-Real.exp (-L)) (Real.exp (-L)) \ ({0} : Set ℝ)
  have hE : MeasurableSet E :=
    measurableSet_Ioo.diff (measurableSet_singleton 0)
  have hthree := nearGapComb_three_carriers_punctured_gap hL
  change dilatedCombMeasure L E = 0 ∧
    dilatedCombMeasure (-L) E = 0 ∧
    dilatedCombMeasure 0 E = 0 at hthree
  have hterm (t : ℝ) (hz : dilatedCombMeasure t E = 0) :
      localSignedCompactRestriction (dilatedCombJordan t) K hK E = 0 := by
    rw [localSignedCompactRestriction_apply _ _ _ E hE]
    have hrestricted : (dilatedCombMeasure t).restrict K E = 0 := by
      rw [Measure.restrict_apply hE]
      exact measure_mono_null inter_subset_left hz
    simp [dilatedCombJordan, localJordanDifference, Measure.real, hrestricted]
  have hLzero := hterm L hthree.1
  have hMinusZero := hterm (-L) hthree.2.1
  have hOriginZero := hterm 0 hthree.2.2
  have hcombine := congrArg (fun m : SignedMeasure ℝ => m E)
    (nearGapCombFamily_compactRestriction L K hK)
  simpa only [_root_.add_apply, _root_.sub_apply, smul_apply,
    smul_eq_mul, hLzero, hMinusZero, hOriginZero,
    zero_add, mul_zero, sub_zero] using hcombine

/-- The original CT1 parameter range places the actual punctured gap
strictly between the half-unit and the unit gap. -/
theorem nearGapComb_radius_bounds {L : ℝ} (hL : 0 < L)
    (hupper : L < Real.log 2) :
    (1 / 2 : ℝ) < Real.exp (-L) ∧ Real.exp (-L) < 1 := by
  constructor
  · have h : Real.exp (-Real.log (2 : ℝ)) < Real.exp (-L) :=
      Real.exp_lt_exp.mpr (by linarith)
    have heq : Real.exp (-Real.log (2 : ℝ)) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rwa [heq] at h
  · have h : Real.exp (-L) < Real.exp (0 : ℝ) :=
      Real.exp_lt_exp.mpr (by linarith)
    simpa only [Real.exp_zero] using h

/-- The physical, canonically reduced CT1 Jordan variation is dominated
by the three original lattice measures. The estimate remains valid even when
their supports overlap; no false mutual-singularity premise is added. -/
theorem nearGapCombFamily_variation_le (L : ℝ) :
    (nearGapCombFamily L).totalVariation ≤
      ((dilatedCombJordan L).totalVariation +
       (dilatedCombJordan (-L)).totalVariation) +
        ENNReal.ofReal |-(2 * Real.cosh (L / 2))| •
          (dilatedCombJordan 0).totalVariation := by
  unfold nearGapCombFamily
  calc
    (localJordanAdd
      (localJordanAdd (dilatedCombJordan L) (dilatedCombJordan (-L)))
      (localJordanScale (-(2 * Real.cosh (L / 2)))
        (dilatedCombJordan 0))).totalVariation ≤
      (localJordanAdd (dilatedCombJordan L)
        (dilatedCombJordan (-L))).totalVariation +
        (localJordanScale (-(2 * Real.cosh (L / 2)))
          (dilatedCombJordan 0)).totalVariation :=
      localJordanAdd_totalVariation_le _ _
    _ ≤ _ := add_le_add
      (localJordanAdd_totalVariation_le _ _)
      (localJordanScale_totalVariation_le _ _)

/-- The actual positive-comb Jordan variation is its original positive
counting measure. This retains possible infinite whole-line mass. -/
theorem nearGap_dilatedComb_variation (t : ℝ) :
    (dilatedCombJordan t).totalVariation = dilatedCombMeasure t := by
  simp [dilatedCombJordan,localJordanDifference,
    LocallyFiniteSignedMeasure.totalVariation]

/-- Strong first-cell exclusion: the *canonical Jordan total variation*
has zero mass on the punctured CT1 gap. The estimate comes from genuine
positive lattice support and the proved Jordan-variation domination.
No Fourier self-duality, supplied gap or zero-measure shortcut is assumed. -/
theorem nearGapCombFamily_punctured_gap_variation_zero
    {L : ℝ} (hL : 0 ≤ L) :
    (nearGapCombFamily L).totalVariation
      (Ioo (-Real.exp (-L)) (Real.exp (-L)) \ ({0} : Set ℝ)) = 0 := by
  let E : Set ℝ :=
    Ioo (-Real.exp (-L)) (Real.exp (-L)) \ ({0} : Set ℝ)
  have hthree := nearGapComb_three_carriers_punctured_gap hL
  change dilatedCombMeasure L E = 0 ∧
    dilatedCombMeasure (-L) E = 0 ∧
    dilatedCombMeasure 0 E = 0 at hthree
  have hbound :
      (nearGapCombFamily L).totalVariation E ≤
        (dilatedCombMeasure L E + dilatedCombMeasure (-L) E) +
          ENNReal.ofReal |-(2 * Real.cosh (L / 2))| *
            dilatedCombMeasure 0 E := by
    simpa only [nearGap_dilatedComb_variation,
      Measure.add_apply, Measure.smul_apply, smul_eq_mul] using
        (nearGapCombFamily_variation_le L E)
  rw [hthree.1, hthree.2.1, hthree.2.2] at hbound
  simpa [E] using (le_antisymm (by simpa using hbound) (zero_le))

/-- Hence both genuine Jordan parts vanish off the origin in the
first-cell gap. This is stronger than a signed-measure cancellation. -/
theorem nearGapCombFamily_punctured_gap_jordan_zero
    {L : ℝ} (hL : 0 ≤ L) :
    (nearGapCombFamily L).positive
      (Ioo (-Real.exp (-L)) (Real.exp (-L)) \ ({0} : Set ℝ)) = 0 ∧
    (nearGapCombFamily L).negative
      (Ioo (-Real.exp (-L)) (Real.exp (-L)) \ ({0} : Set ℝ)) = 0 := by
  have hz := nearGapCombFamily_punctured_gap_variation_zero hL
  change ((nearGapCombFamily L).positive +
      (nearGapCombFamily L).negative)
    (Ioo (-Real.exp (-L)) (Real.exp (-L)) \ ({0} : Set ℝ)) = 0 at hz
  rw [Measure.add_apply] at hz
  exact add_eq_zero.mp hz

/-- The ACTUAL canonical CT1 Jordan pair has a full open gap, including
the origin. This composes independent physical facts: genuine first-cell
support away from zero, and mutual-singularity-based cancellation of the
origin atom. The original nonzero/Fourier/positivity family root remains
OPEN; no synthetic measure or assumed gap enters this theorem. -/
theorem nearGapCombFamily_actual_gap {L : ℝ} (hL : 0 ≤ L) :
    hasNearGap (nearGapCombFamily L) (Real.exp (-L)) := by
  let S : Set ℝ := Ioo (-Real.exp (-L)) (Real.exp (-L))
  let E : Set ℝ := S \ ({0} : Set ℝ)
  have hcover : S ⊆ E ∪ ({0} : Set ℝ) := by
    intro x hx
    by_cases hzero : x = 0
    · exact Or.inr (by simpa [mem_singleton_iff] using hzero)
    · exact Or.inl ⟨hx, by simpa only [mem_singleton_iff] using hzero⟩
  have hzeroUnion (mu : Measure ℝ)
      (hpunctured : mu E = 0) (horigin : mu ({0} : Set ℝ) = 0) :
      mu S = 0 := by
    have hu : mu (E ∪ ({0} : Set ℝ)) = 0 := by
      apply le_antisymm
      · calc
          _ ≤ mu E + mu ({0} : Set ℝ) := measure_union_le _ _
          _ = 0 := by rw [hpunctured, horigin]; simp
      · exact zero_le
    exact measure_mono_null hcover hu
  have hpunctured := nearGapCombFamily_punctured_gap_jordan_zero hL
  have horigin := nearGapCombFamily_origin_jordan_zero L
  change (nearGapCombFamily L).positive E = 0 ∧
    (nearGapCombFamily L).negative E = 0 at hpunctured
  unfold hasNearGap
  change (nearGapCombFamily L).positive S = 0 ∧
    (nearGapCombFamily L).negative S = 0
  exact ⟨hzeroUnion _ hpunctured.1 horigin.1,
    hzeroUnion _ hpunctured.2 horigin.2⟩

/-- Negative Jordan mass of a canonical sum is bounded by the genuine
negative sources. The positive/negative cancellation internal to
localJordanDifference can only REDUCE negative mass. -/
theorem nearGap_localJordanAdd_negative_le
    (mu nu : LocallyFiniteSignedMeasure) :
    (localJordanAdd mu nu).negative ≤ mu.negative + nu.negative := by
  change (mu.negative + nu.negative) -
    (mu.positive + nu.positive) ≤ mu.negative + nu.negative
  exact Measure.sub_le

/-- Scaling a signed source cannot create negative measure on a set where
the source's actual total variation vanishes. -/
theorem nearGap_localJordanScale_negative_zero
    (a : ℝ) (mu : LocallyFiniteSignedMeasure) (E : Set ℝ)
    (hz : mu.totalVariation E = 0) :
    (localJordanScale a mu).negative E = 0 := by
  have hvar := localJordanScale_totalVariation_le a mu E
  simp only [Measure.smul_apply, smul_eq_mul, hz, mul_zero] at hvar
  have hnegative :
      (localJordanScale a mu).negative E ≤
        (localJordanScale a mu).totalVariation E := by
    rw [LocallyFiniteSignedMeasure.totalVariation, Measure.add_apply]
    exact le_add_of_nonneg_left (zero_le)
  exact le_antisymm (hnegative.trans hvar) (zero_le)

/-- The true integer comb D_0 has no mass away from the literal
integer lattice. This is checked on the preimage of the actual
Measure.map counting construction, not stipulated as a support packet. -/
theorem nearGap_undilatedComb_integer_support :
    dilatedCombMeasure 0 integerLatticeᶜ = 0 := by
  rw [dilatedCombMeasure, Measure.smul_apply,
    scaledLatticeMeasure,
    Measure.map_apply (scaledLatticePoint_measurable 0)
      integerLattice_measurable.compl]
  have hpre :
      (scaledLatticePoint 0) ⁻¹' integerLatticeᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro n hn
    apply hn
    exact ⟨n, by simp [scaledLatticePoint]⟩
  rw [hpre]
  simp

/-- In the exact CT1 range, the first dilated point lies strictly
between consecutive integers 1 and 2, hence is off the integer lattice. -/
theorem nearGap_first_dilated_point_off_integer {L : ℝ}
    (hL : 0 < L) (hu : L < Real.log 2) :
    Real.exp L ∉ integerLattice := by
  intro hx
  obtain ⟨n, hn⟩ := hx
  have hlo : (1 : ℝ) < Real.exp L := by
    have h := Real.exp_lt_exp.mpr hL
    simpa only [Real.exp_zero] using h
  have hhi : Real.exp L < (2 : ℝ) := by
    have h := Real.exp_lt_exp.mpr hu
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  have hnlo : (1 : ℝ) < (n : ℝ) := by simpa only [hn] using hlo
  have hnhi : (n : ℝ) < (2 : ℝ) := by simpa only [hn] using hhi
  have ha : (1 : ℤ) < n := by exact_mod_cast hnlo
  have hb : n < (2 : ℤ) := by exact_mod_cast hnhi
  omega

/-- The negative source carrier D_0 has no atom at the first positive
dilated point of D_L. This separates the genuine positive noninteger
witness from any possible cancellation by the undilated lattice. -/
theorem nearGap_undilatedComb_first_dilated_atom_zero {L : ℝ}
    (hL : 0 < L) (hu : L < Real.log 2) :
    dilatedCombMeasure 0 ({Real.exp L} : Set ℝ) = 0 := by
  apply measure_mono_null
    (s := ({Real.exp L} : Set ℝ))
    (t := integerLatticeᶜ) ?_ nearGap_undilatedComb_integer_support
  intro x hx
  have hx' : x = Real.exp L := by simpa only [Set.mem_singleton_iff] using hx
  subst x
  exact nearGap_first_dilated_point_off_integer hL hu

/-- The signed compact evaluation of an actual positive dilated comb
is precisely its positive counting-measure evaluation. This keeps all
atomic masses and compact-domain restrictions physical. -/
theorem nearGap_dilatedComb_compact_signed_apply
    (t : ℝ) (K : Set ℝ) (hK : IsCompact K) (E : Set ℝ)
    (hE : MeasurableSet E) :
    localSignedCompactRestriction (dilatedCombJordan t) K hK E =
      ((dilatedCombMeasure t).restrict K).real E := by
  rw [localSignedCompactRestriction_apply _ _ _ E hE]
  simp [dilatedCombJordan, localJordanDifference]

/-- Every actual dilated integer atom has strictly positive signed
evaluation on its compact singleton restriction. -/
theorem nearGap_dilatedComb_compact_signed_atom (t : ℝ) (n : ℤ) :
    localSignedCompactRestriction (dilatedCombJordan t)
      ({scaledLatticePoint t n} : Set ℝ) isCompact_singleton
      ({scaledLatticePoint t n} : Set ℝ) = Real.exp (t / 2) := by
  rw [nearGap_dilatedComb_compact_signed_apply t _ _ _
    (measurableSet_singleton _)]
  change (((dilatedCombMeasure t).restrict
      ({scaledLatticePoint t n} : Set ℝ))
      ({scaledLatticePoint t n} : Set ℝ)).toReal = Real.exp (t / 2)
  rw [Measure.restrict_apply (measurableSet_singleton _)]
  simp only [inter_self]
  rw [dilatedCombMeasure_atom, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- Physical first noninteger atom of the CT1 signed measure is POSITIVE:
D_L supplies exp(L/2), the reflected comb supplies a nonnegative
additional mass, and the undilated negative comb has no atom there.
No off-lattice positivity premise is assumed about the result. -/
theorem nearGapCombFamily_first_atom_signed_pos {L : ℝ}
    (hL : 0 < L) (hu : L < Real.log 2) :
    0 < localSignedCompactRestriction (nearGapCombFamily L)
      ({Real.exp L} : Set ℝ) isCompact_singleton
      ({Real.exp L} : Set ℝ) := by
  let S : Set ℝ := {Real.exp L}
  have hS : MeasurableSet S := measurableSet_singleton _
  have hfirst :
      localSignedCompactRestriction (dilatedCombJordan L)
        S isCompact_singleton S = Real.exp (L / 2) := by
    simpa only [S, scaledLatticePoint, Int.cast_one, mul_one] using
      nearGap_dilatedComb_compact_signed_atom L (1 : ℤ)
  have hsecond :
      0 ≤ localSignedCompactRestriction (dilatedCombJordan (-L))
        S isCompact_singleton S := by
    rw [nearGap_dilatedComb_compact_signed_apply _ _ _ _ hS]
    exact measureReal_nonneg
  have hthird :
      localSignedCompactRestriction (dilatedCombJordan 0)
        S isCompact_singleton S = 0 := by
    rw [nearGap_dilatedComb_compact_signed_apply _ _ _ _ hS]
    have hz : ((dilatedCombMeasure 0).restrict S) S = 0 := by
      rw [Measure.restrict_apply hS, inter_self]
      exact nearGap_undilatedComb_first_dilated_atom_zero hL hu
    exact (measureReal_eq_zero_iff
      (isCompact_singleton.measure_lt_top.ne)).mpr hz
  have hsum := congrArg (fun mu : SignedMeasure ℝ => mu S)
    (nearGapCombFamily_compactRestriction L S isCompact_singleton)
  simp only [_root_.add_apply, _root_.sub_apply,
    smul_apply, smul_eq_mul, hfirst, hthird,
    mul_zero, sub_zero] at hsum
  rw [hsum]
  exact add_pos_of_pos_of_nonneg (Real.exp_pos _) hsecond

/-- The genuine positive lattice comb has zero negative Jordan part,
regardless of the dilation. This is a canonical Jordan property. -/
theorem nearGap_dilatedComb_negative_zero (t : ℝ) :
    (dilatedCombJordan t).negative = 0 := by
  simp [dilatedCombJordan, localJordanDifference]

/-- The sum of the two positive dilated lattice carriers has no negative
Jordan mass. Overlapping positive supports cannot change this. -/
theorem nearGap_two_positive_combs_negative_zero (L : ℝ) :
    (localJordanAdd (dilatedCombJordan L)
      (dilatedCombJordan (-L))).negative = 0 := by
  simp [localJordanAdd, localJordanDifference,
    nearGap_dilatedComb_negative_zero]

/-- The actual CT1 negative Jordan part is supported on the integers.
This is stronger than an off-lattice signed-integral inequality. The
only negative input carrier is the undilated integer comb; all
noninteger lattice atoms enter through nonnegative counting measures.
No positivity property is assumed for the unknown output measure. -/
theorem nearGapCombFamily_negative_integer_support (L : ℝ) :
    (nearGapCombFamily L).negative integerLatticeᶜ = 0 := by
  let plus : LocallyFiniteSignedMeasure :=
    localJordanAdd (dilatedCombJordan L) (dilatedCombJordan (-L))
  let minus : LocallyFiniteSignedMeasure :=
    localJordanScale (-(2 * Real.cosh (L / 2)))
      (dilatedCombJordan 0)
  have hplus : plus.negative = 0 := by
    exact nearGap_two_positive_combs_negative_zero L
  have hsource : (dilatedCombJordan 0).totalVariation
      integerLatticeᶜ = 0 := by
    rw [nearGap_dilatedComb_variation]
    exact nearGap_undilatedComb_integer_support
  have hminus : minus.negative integerLatticeᶜ = 0 :=
    nearGap_localJordanScale_negative_zero
      (-(2 * Real.cosh (L / 2))) (dilatedCombJordan 0)
      integerLatticeᶜ hsource
  have hbound :
      (nearGapCombFamily L).negative integerLatticeᶜ ≤
        plus.negative integerLatticeᶜ +
          minus.negative integerLatticeᶜ := by
    change (localJordanAdd plus minus).negative integerLatticeᶜ ≤ _
    exact nearGap_localJordanAdd_negative_le plus minus integerLatticeᶜ
  rw [hplus, Measure.coe_zero, Pi.zero_apply, hminus, zero_add] at hbound
  exact le_antisymm hbound (zero_le)

/-- Physical off-lattice nonnegativity of the genuine CT1 canonical
Jordan pair, for every real dilation parameter. -/
theorem nearGapCombFamily_offlattice_nonnegative (L : ℝ) :
    (nearGapCombFamily L).OffLatticeNonnegative :=
  nearGapCombFamily_negative_integer_support L

/-- The CT1 witness x = exp L is a strictly positive atom of the
canonical *positive Jordan measure*, not only a signed compact evaluation.
The negative Jordan atom vanishes because it is supported on the original
integer lattice, whereas exp L lies strictly between 1 and 2. -/
theorem nearGapCombFamily_first_atom_positive_real_pos {L : ℝ}
    (hL : 0 < L) (hu : L < Real.log 2) :
    0 < (nearGapCombFamily L).positive.real ({Real.exp L} : Set ℝ) := by
  let nu := nearGapCombFamily L
  let S : Set ℝ := {Real.exp L}
  have hS : MeasurableSet S := measurableSet_singleton _
  have hsubset : S ⊆ integerLatticeᶜ := by
    intro x hx
    have heq : x = Real.exp L := hx
    subst x
    exact nearGap_first_dilated_point_off_integer hL hu
  have hn : nu.negative S = 0 :=
    measure_mono_null hsubset (nearGapCombFamily_negative_integer_support L)
  have hpos := nearGapCombFamily_first_atom_signed_pos hL hu
  change 0 < localSignedCompactRestriction nu S isCompact_singleton S at hpos
  rw [localSignedCompactRestriction_apply nu S isCompact_singleton S hS] at hpos
  have hpositive : (nu.positive.restrict S).real S = nu.positive.real S := by
    rw [Measure.real, Measure.real, Measure.restrict_apply hS]
    simp
  have hnegative : (nu.negative.restrict S).real S = 0 := by
    rw [Measure.real, Measure.restrict_apply hS]
    simp [hn]
  simpa only [hpositive, hnegative, sub_zero] using hpos

/-- The actual near-gap family is a nonzero Jordan-measure object:
its positive part has a witnessed nonzero atom away from the integers.
No synthetic nonzero premise is supplied by the caller. -/
theorem nearGapCombFamily_positive_nonzero {L : ℝ}
    (hL : 0 < L) (hu : L < Real.log 2) :
    (nearGapCombFamily L).positive ≠ 0 := by
  intro hz
  have hpos := nearGapCombFamily_first_atom_positive_real_pos hL hu
  rw [hz] at hpos
  simp at hpos

/-- A positive dilated comb has no atom at a point that is not one of its
actual lattice points. -/
theorem nearGap_dilatedComb_atom_zero_of_not_lattice (t x : ℝ)
    (hx : ∀ n : ℤ, scaledLatticePoint t n ≠ x) :
    dilatedCombMeasure t ({x} : Set ℝ) = 0 := by
  rw [dilatedCombMeasure, Measure.smul_apply, scaledLatticeMeasure,
    Measure.map_apply (scaledLatticePoint_measurable t) (measurableSet_singleton x)]
  have hpre : scaledLatticePoint t ⁻¹' ({x} : Set ℝ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro n hn
    exact hx n hn
  rw [hpre]
  simp

/-- The dilated comb D_L has no atom at the gap edge exp(-L) when L > 0:
exp(L) n = exp(-L) would force 0 < n < 1. -/
theorem nearGap_forward_comb_gap_edge_atom_zero {L : ℝ} (hL : 0 < L) :
    dilatedCombMeasure L ({Real.exp (-L)} : Set ℝ) = 0 := by
  apply nearGap_dilatedComb_atom_zero_of_not_lattice
  intro n hn
  have hn' : Real.exp L * (n : ℝ) = Real.exp (-L) := hn
  have hpos : (0 : ℝ) < (n : ℝ) := by
    by_contra h
    have h' : Real.exp L * (n : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos L).le (not_lt.mp h)
    linarith [Real.exp_pos (-L)]
  have hlt : (n : ℝ) < 1 := by
    have hexp : Real.exp (-L) < Real.exp L := Real.exp_lt_exp.mpr (by linarith)
    by_contra h
    have h' : Real.exp L * 1 ≤ Real.exp L * (n : ℝ) :=
      mul_le_mul_of_nonneg_left (not_lt.mp h) (Real.exp_pos L).le
    linarith
  have h0 : (0 : ℤ) < n := by exact_mod_cast hpos
  have h1 : n < (1 : ℤ) := by exact_mod_cast hlt
  omega

/-- In the CT1 range the gap edge exp(-L) lies strictly between 0 and 1,
hence off the integer lattice. -/
theorem nearGap_gap_edge_off_integer {L : ℝ} (hL : 0 < L)
    (hu : L < Real.log 2) : Real.exp (-L) ∉ integerLattice := by
  intro hx
  obtain ⟨n, hn⟩ := hx
  have hb := nearGapComb_radius_bounds hL hu
  have hlo : (0 : ℝ) < (n : ℝ) := by
    have : (n : ℝ) = Real.exp (-L) := hn
    rw [this]; exact Real.exp_pos _
  have hhi : (n : ℝ) < 1 := by
    have : (n : ℝ) = Real.exp (-L) := hn
    rw [this]; exact hb.2
  have h0 : (0 : ℤ) < n := by exact_mod_cast hlo
  have h1 : n < (1 : ℤ) := by exact_mod_cast hhi
  omega

/-- The paper's CT1 nonzero witness: the gap-edge atom at exp(-L) has the
exact positive Jordan mass exp(-L/2) and no negative Jordan mass. Only the
reflected comb D_(-L) contributes (its n = 1 point); D_L and the integer comb
D_0 have no atom there. This also shows that the gap radius exp(-L) is sharp. -/
theorem nearGapCombFamily_gap_edge_atom {L : ℝ}
    (hL : 0 < L) (hu : L < Real.log 2) :
    (nearGapCombFamily L).positive.real ({Real.exp (-L)} : Set ℝ) =
      Real.exp (-L / 2) ∧
    (nearGapCombFamily L).negative ({Real.exp (-L)} : Set ℝ) = 0 := by
  let nu := nearGapCombFamily L
  let S : Set ℝ := {Real.exp (-L)}
  have hS : MeasurableSet S := measurableSet_singleton _
  have hneg : nu.negative S = 0 := by
    apply measure_mono_null ?_ (nearGapCombFamily_negative_integer_support L)
    intro x hx
    have heq : x = Real.exp (-L) := hx
    subst x
    exact nearGap_gap_edge_off_integer hL hu
  have hreflected :
      localSignedCompactRestriction (dilatedCombJordan (-L))
        S isCompact_singleton S = Real.exp (-L / 2) := by
    simpa only [S, scaledLatticePoint, Int.cast_one, mul_one] using
      nearGap_dilatedComb_compact_signed_atom (-L) (1 : ℤ)
  have hzero_of (t : ℝ) (hz : dilatedCombMeasure t S = 0) :
      localSignedCompactRestriction (dilatedCombJordan t)
        S isCompact_singleton S = 0 := by
    rw [nearGap_dilatedComb_compact_signed_apply _ _ _ _ hS]
    have hr : ((dilatedCombMeasure t).restrict S) S = 0 := by
      rw [Measure.restrict_apply hS, inter_self]
      exact hz
    exact (measureReal_eq_zero_iff (isCompact_singleton.measure_lt_top.ne)).mpr hr
  have hforward := hzero_of L (nearGap_forward_comb_gap_edge_atom_zero hL)
  have hinteger : dilatedCombMeasure 0 S = 0 := by
    apply measure_mono_null ?_ nearGap_undilatedComb_integer_support
    intro x hx
    have heq : x = Real.exp (-L) := hx
    subst x
    exact nearGap_gap_edge_off_integer hL hu
  have hthird := hzero_of 0 hinteger
  have hsum := congrArg (fun mu : SignedMeasure ℝ => mu S)
    (nearGapCombFamily_compactRestriction L S isCompact_singleton)
  simp only [_root_.add_apply, _root_.sub_apply, smul_apply, smul_eq_mul,
    hforward, hreflected, hthird, mul_zero, sub_zero, zero_add] at hsum
  rw [localSignedCompactRestriction_apply nu S isCompact_singleton S hS] at hsum
  have hpositive : (nu.positive.restrict S).real S = nu.positive.real S := by
    rw [Measure.real, Measure.real, Measure.restrict_apply hS, inter_self]
  have hnegative : (nu.negative.restrict S).real S = 0 := by
    rw [Measure.real, Measure.restrict_apply hS, inter_self, hneg]
    simp
  refine ⟨?_, hneg⟩
  rw [hpositive, hnegative, sub_zero] at hsum
  exact hsum

/-- Uniform interval mass bound for the actual positive lattice carrier,
deduced from the original source-bound Poisson/dilation theorem. -/
theorem nearGap_dilatedComb_interval_bound (t R : ℝ) (hR : 0 ≤ R) :
    (dilatedCombJordan t).totalVariation.real (Icc (-R) R) ≤
      Real.exp (t / 2) * (3 + 2 * Real.exp (-t) * R) := by
  rw [nearGap_dilatedComb_variation]
  have h := (dilated_comb_fourier t).1 R hR
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (by positivity)] at ht

/-- A common scalar bound for every dilation between the undeformed comb
and the limiting two-to-one lattice scale. Both signs of L are retained. -/
theorem nearGap_dilation_exp_sum_le_three {L : ℝ}
    (hL : 0 ≤ L) (hu : L ≤ Real.log 2) :
    Real.exp (L / 2) + Real.exp (-L / 2) ≤ 3 := by
  have hhalf : L / 2 ≤ Real.log 2 := by linarith
  have hplus : Real.exp (L / 2) ≤ 2 := by
    have he := Real.exp_le_exp.mpr hhalf
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using he
  have hminus : Real.exp (-L / 2) ≤ 1 := by
    have he := Real.exp_le_exp.mpr (show -L / 2 ≤ 0 by linarith)
    simpa only [Real.exp_zero] using he
  linarith

/-- Universal parameter budget for the three actual dilation amplitudes and
their interval-counting coefficients. The future uniform Jordan-variation
theorem must still prove that the actual measure is bounded by this scalar. -/
theorem nearGap_dilation_uniform_scalar_budget {L R : ℝ}
    (hL : 0 ≤ L) (hu : L ≤ Real.log 2) (hR : 0 ≤ R) :
    (6 + 4 * R) * (Real.exp (L / 2) + Real.exp (-L / 2)) ≤
      18 * (1 + R) := by
  have hsum := nearGap_dilation_exp_sum_le_three hL hu
  calc
    _ ≤ (6 + 4 * R) * 3 :=
      mul_le_mul_of_nonneg_left hsum (by linarith)
    _ ≤ 18 * (1 + R) := by nlinarith

/-- A *common* linear-variation estimate for the actual CT1 signed carrier,
valid for every 0 ≤ L ≤ log 2 with no global finite-mass assumption.

The bound is on genuine canonical Jordan variation, not merely a coefficient
envelope. It is deliberately independent of L, so it is suitable for the
weak-limit/Schwartz tail argument once the other CT1 hypotheses are proved. -/
theorem nearGapCombFamily_uniform_variation {L R : ℝ}
    (hL : 0 ≤ L) (hu : L ≤ Real.log 2) (hR : 0 ≤ R) :
    (nearGapCombFamily L).totalVariation.real (Icc (-R) R) ≤
      18 * (1 + R) := by
  let S : Set ℝ := Icc (-R) R
  let μ := dilatedCombJordan L
  let ν := dilatedCombJordan (-L)
  let ξ := dilatedCombJordan 0
  let c := |-(2 * Real.cosh (L / 2))|
  have hμ : μ.totalVariation S ≠ ∞ := isCompact_Icc.measure_lt_top.ne
  have hν : ν.totalVariation S ≠ ∞ := isCompact_Icc.measure_lt_top.ne
  have hξ : ξ.totalVariation S ≠ ∞ := isCompact_Icc.measure_lt_top.ne
  have hadd : (μ.totalVariation S + ν.totalVariation S) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hμ,hν⟩
  have hmul : ENNReal.ofReal c * ξ.totalVariation S ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hξ
  have hfin : (μ.totalVariation S + ν.totalVariation S) +
      ENNReal.ofReal c * ξ.totalVariation S ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hadd,hmul⟩
  have hle := ENNReal.toReal_mono hfin
    (nearGapCombFamily_variation_le L S)
  change ((nearGapCombFamily L).totalVariation S).toReal ≤
    ((μ.totalVariation S + ν.totalVariation S) +
      ENNReal.ofReal c * ξ.totalVariation S).toReal at hle
  rw [ENNReal.toReal_add hadd hmul, ENNReal.toReal_add hμ hν,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)] at hle
  have hcoeff : c = Real.exp (L / 2) + Real.exp (-L / 2) := by
    dsimp [c]
    rw [Real.cosh_eq]
    have hnonneg : (0 : ℝ) ≤
        2 * ((Real.exp (L / 2) + Real.exp (-(L / 2))) / 2) := by
      positivity
    rw [abs_neg, abs_of_nonneg hnonneg]
    have hneg : -(L / 2) = -L / 2 := by ring
    rw [hneg]
    ring
  have hμR := nearGap_dilatedComb_interval_bound L R hR
  have hνR := nearGap_dilatedComb_interval_bound (-L) R hR
  have hξR := nearGap_dilatedComb_interval_bound 0 R hR
  have hξR' : ξ.totalVariation.real S ≤ 3 + 2 * R := by
    simpa [ξ,S] using hξR
  have hcoefpos : 0 ≤ Real.exp (L / 2) + Real.exp (-L / 2) := by
    positivity
  have hsum :
      μ.totalVariation.real S + ν.totalVariation.real S +
        c * ξ.totalVariation.real S ≤
      Real.exp (L / 2) * (3 + 2 * Real.exp (-L) * R) +
      Real.exp (-L / 2) * (3 + 2 * Real.exp L * R) +
        (Real.exp (L / 2) + Real.exp (-L / 2)) * (3 + 2 * R) := by
    rw [hcoeff]
    have hν' : ν.totalVariation.real S ≤
        Real.exp (-L / 2) * (3 + 2 * Real.exp L * R) := by
      simpa [ν,S] using hνR
    exact add_le_add (add_le_add (by simpa [μ,S] using hμR) hν')
      (mul_le_mul_of_nonneg_left hξR' hcoefpos)
  have he1 : Real.exp (L / 2) * Real.exp (-L) =
      Real.exp (-L / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he2 : Real.exp (-L / 2) * Real.exp L =
      Real.exp (L / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have heq :
      Real.exp (L / 2) * (3 + 2 * Real.exp (-L) * R) +
      Real.exp (-L / 2) * (3 + 2 * Real.exp L * R) +
        (Real.exp (L / 2) + Real.exp (-L / 2)) * (3 + 2 * R) =
      (6 + 4 * R) * (Real.exp (L / 2) + Real.exp (-L / 2)) := by
    calc
      _ = (6 + 4 * R) * (Real.exp (L / 2) + Real.exp (-L / 2)) +
          2 * R * (Real.exp (L / 2) * Real.exp (-L) - Real.exp (-L / 2)) +
          2 * R * (Real.exp (-L / 2) * Real.exp L - Real.exp (L / 2)) := by
          ring
      _ = _ := by rw [he1, he2]; ring
  calc
    _ ≤ μ.totalVariation.real S + ν.totalVariation.real S +
        c * ξ.totalVariation.real S := hle
    _ ≤ _ := hsum
    _ = _ := heq
    _ ≤ _ := nearGap_dilation_uniform_scalar_budget hL hu hR

/-- Uniform-in-parameter source-bound growth, in the exact common-budget
interface already used by the locally finite complex Schwartz-limit theorem.
This strengthens the earlier L-dependent existential growth witness. -/
theorem nearGapCombFamily_common_growth {L : ℝ}
    (hL : 0 ≤ L) (hu : L ≤ Real.log 2) :
    CommonLinearMassBound 18 (nearGapCombFamily L).totalVariation :=
  ⟨by norm_num, fun R hR => nearGapCombFamily_uniform_variation hL hu hR⟩

/-- Uniform Schwartz tail control for the *actual* CT1 signed carrier.
Combines the common physical Jordan variation bound with the previously proved
dyadic-shell cubic-tail lemma. Crucially, no dependence on L enters the
constant, even as the near-gap parameter approaches one.

This proves the tail-control prerequisite, not compact weak convergence or
the full near_gap_controlled_limit_zero primary theorem. -/
theorem nearGapCombFamily_uniform_schwartz_tail {L R M : ℝ}
    (hL : 0 ≤ L) (hu : L ≤ Real.log 2)
    (hM : 0 ≤ M) (hR : 1 ≤ R)
    (f : ℝ → ℂ) (hf : Continuous f)
    (hdecay : ∀ x : ℝ, |x| ^ 3 * ‖f x‖ ≤ M) :
    IntegrableOn f {x : ℝ | R ≤ |x|}
      (nearGapCombFamily L).totalVariation ∧
    (∫ x in {x : ℝ | R ≤ |x|}, ‖f x‖
      ∂(nearGapCombFamily L).totalVariation) ≤ 72 * M / R ^ 2 := by
  have h := common_linear_cubic_tail
    (nearGapCombFamily L).totalVariation 18 M R
    (nearGapCombFamily_common_growth hL hu) hM hR f hf hdecay
  refine ⟨h.1, ?_⟩
  simpa only [show (4 : ℝ) * 18 = 72 by norm_num, mul_assoc] using h.2

/-- Genuine linear growth survives canonical Jordan addition; it is a
consequence of the actual total-variation inequality, not a condition placed
on the sum in advance. No whole-line finite-mass premise is used. -/
theorem nearGap_localJordanAdd_growth
    (mu nu : LocallyFiniteSignedMeasure)
    (hmu : mu.HasLinearGrowth) (hnu : nu.HasLinearGrowth) :
    (localJordanAdd mu nu).HasLinearGrowth := by
  obtain ⟨A,hA,hAb⟩ := hmu
  obtain ⟨B,hB,hBb⟩ := hnu
  refine ⟨A+B,add_nonneg hA hB,fun R hR => ?_⟩
  have hmfin : mu.totalVariation (Icc (-R) R) ≠ ∞ :=
    isCompact_Icc.measure_lt_top.ne
  have hnfin : nu.totalVariation (Icc (-R) R) ≠ ∞ :=
    isCompact_Icc.measure_lt_top.ne
  have hsumfin : (mu.totalVariation+nu.totalVariation) (Icc (-R) R) ≠ ∞ := by
    rw [Measure.add_apply]
    exact ENNReal.add_ne_top.mpr ⟨hmfin,hnfin⟩
  have hle := ENNReal.toReal_mono hsumfin
    (localJordanAdd_totalVariation_le mu nu (Icc (-R) R))
  rw [Measure.add_apply,ENNReal.toReal_add hmfin hnfin] at hle
  have ha := hAb R hR
  have hb := hBb R hR
  change ((localJordanAdd mu nu).totalVariation (Icc (-R) R)).toReal ≤ _ at hle ⊢
  change (mu.totalVariation (Icc (-R) R)).toReal ≤ _ at ha
  change (nu.totalVariation (Icc (-R) R)).toReal ≤ _ at hb
  nlinarith

/-- Canonicalization of a locally finite Jordan sum preserves its actual
Schwartz pairing. The needed source hypotheses are only linear growth of the
two genuine input measures, not global finite variation or an arbitrary
distribution identity provided by a caller. -/
theorem nearGap_localJordanAdd_pairing
    (mu nu : LocallyFiniteSignedMeasure)
    (hmu : mu.HasLinearGrowth) (hnu : nu.HasLinearGrowth)
    (f : SchwartzMap ℝ ℂ) :
    (localJordanAdd mu nu).distributionOfLinearGrowth
      (nearGap_localJordanAdd_growth mu nu hmu hnu) f =
      mu.distributionOfLinearGrowth hmu f +
      nu.distributionOfLinearGrowth hnu f := by
  have hmp : Integrable f mu.positive := by
    let := (mu.parts_temperate_of_linear_growth hmu).1
    exact f.integrable
  have hmm : Integrable f mu.negative := by
    let := (mu.parts_temperate_of_linear_growth hmu).2
    exact f.integrable
  have hnp : Integrable f nu.positive := by
    let := (nu.parts_temperate_of_linear_growth hnu).1
    exact f.integrable
  have hnm : Integrable f nu.negative := by
    let := (nu.parts_temperate_of_linear_growth hnu).2
    exact f.integrable
  have hplus : Integrable f (mu.positive + nu.positive) :=
    integrable_add_measure.mpr ⟨hmp,hnp⟩
  have hminus : Integrable f (mu.negative + nu.negative) :=
    integrable_add_measure.mpr ⟨hmm,hnm⟩
  simp only [LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply,
    localJordanAdd]
  rw [localJordanDifference_integral
    (mu.positive + nu.positive) (mu.negative + nu.negative) f hplus hminus,
    integral_add_measure hmp hnp,integral_add_measure hmm hnm]
  ring

/-- Signed scalar multiplication preserves genuine linear variation growth,
with the magnitude of the actual scalar explicitly charged. -/
theorem nearGap_localJordanScale_growth
    (a : ℝ) (mu : LocallyFiniteSignedMeasure) (hmu : mu.HasLinearGrowth) :
    (localJordanScale a mu).HasLinearGrowth := by
  obtain ⟨A,hA,hAb⟩ := hmu
  refine ⟨(|a|) * A,mul_nonneg (abs_nonneg _) hA,fun R hR => ?_⟩
  have hle := localJordanScale_totalVariation_le a mu (Icc (-R) R)
  rw [Measure.smul_apply,smul_eq_mul] at hle
  have hfin : ENNReal.ofReal |a| * mu.totalVariation (Icc (-R) R) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top isCompact_Icc.measure_lt_top.ne
  have hh := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _)] at hh
  have ha := hAb R hR
  change (mu.totalVariation (Icc (-R) R)).toReal ≤ _ at ha
  change ((localJordanScale a mu).totalVariation (Icc (-R) R)).toReal ≤ _
  exact hh.trans ((mul_le_mul_of_nonneg_left ha (abs_nonneg a)).trans_eq (by ring))

/-- A negative real scalar acts on an ACTUAL positive dilated counting
measure by placing the entire scaled mass in the negative canonical Jordan
part. Its Schwartz distribution agrees with complex scalar multiplication.

Unlike the preceding conditional bridge, this has no extra premise:
the source is the genuine counting measure D_t and c is nonnegative.
This is the exact missing CT1 Jordan-scalar compatibility. -/
theorem nearGap_dilatedComb_negative_scale_pairing
    (t c : ℝ) (hc : 0 ≤ c) :
    (localJordanScale (-c) (dilatedCombJordan t)).distributionOfLinearGrowth
      (nearGap_localJordanScale_growth (-c) (dilatedCombJordan t)
        (dilatedCombJordan_growth t)) =
    (-(c : ℂ)) • dilatedCombDistribution t := by
  have hpositive :
      (localJordanScale (-c) (dilatedCombJordan t)).positive = 0 := by
    simp [localJordanScale, dilatedCombJordan, localJordanDifference,
      Real.toNNReal_of_nonpos (neg_nonpos.mpr hc)]
  have hnegative :
      (localJordanScale (-c) (dilatedCombJordan t)).negative =
        (Real.toNNReal c : ℝ≥0∞) • dilatedCombMeasure t := by
    simp [localJordanScale, dilatedCombJordan, localJordanDifference,
      Real.toNNReal_of_nonpos (neg_nonpos.mpr hc)]
  have hsource (f : SchwartzMap ℝ ℂ) :
      dilatedCombDistribution t f =
        ∫ x, f x ∂(dilatedCombMeasure t) := by
    rw [dilatedCombDistribution,
      LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply]
    simp [dilatedCombJordan, localJordanDifference]
  ext f
  rw [LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply,
    hpositive, hnegative, integral_zero_measure, zero_sub,
    integral_smul_measure]
  rw [show ((-(c : ℂ)) • dilatedCombDistribution t) f =
      (-(c : ℂ)) * dilatedCombDistribution t f from rfl, hsource]
  simp only [ENNReal.ofNNReal_toNNReal,
    ENNReal.toReal_ofReal hc, RCLike.real_smul_eq_coe_mul]
  first
    | ring1
    | exact (neg_mul _ _).symm

/-- Genuine global linear-growth certificate for the *actual* CT1
Jordan measure at any dilation parameter. The uniform-in-L budget required
by the controlled-limit root is a separate, still OPEN estimate. -/
theorem nearGapCombFamily_growth (L : ℝ) :
    (nearGapCombFamily L).HasLinearGrowth := by
  exact nearGap_localJordanAdd_growth _ _
    (nearGap_localJordanAdd_growth _ _
      (dilatedCombJordan_growth L) (dilatedCombJordan_growth (-L)))
    (nearGap_localJordanScale_growth _ _
      (dilatedCombJordan_growth 0))

/-- The CT1 object is now represented by a genuine tempered distribution,
using the proved local-Jordan linear-growth certificate. -/
def nearGapCombDistribution (L : ℝ) : TemperedDistribution ℝ ℂ :=
  (nearGapCombFamily L).distributionOfLinearGrowth (nearGapCombFamily_growth L)

/-- A precise conditional reduction of CT1 canonical Fourier
self-duality to the missing *scalar Jordan pairing* bridge.

The scalar bridge below is an explicit hypothesis and MUST NOT be
counted as an accepted original root. It has no RH consequence by itself.
All three carrier distributions are the actual source-backed Poisson combs;
only compatibility of Jordan scalar multiplication with the Schwartz
distribution is left to establish. -/
theorem nearGapCombDistribution_eq_explicit_of_scale_pairing
    (L : ℝ)
    (hscale :
      (localJordanScale (-(2 * Real.cosh (L / 2)))
        (dilatedCombJordan 0)).distributionOfLinearGrowth
        (nearGap_localJordanScale_growth _ _
          (dilatedCombJordan_growth 0)) =
        (-(((2 * Real.cosh (L / 2) : ℝ) : ℂ))) •
          dilatedCombDistribution 0) :
    nearGapCombDistribution L = nearGapExplicitDilationDistribution L := by
  let A : LocallyFiniteSignedMeasure :=
    localJordanAdd (dilatedCombJordan L) (dilatedCombJordan (-L))
  let B : LocallyFiniteSignedMeasure :=
    localJordanScale (-(2 * Real.cosh (L / 2))) (dilatedCombJordan 0)
  let hA : A.HasLinearGrowth :=
    nearGap_localJordanAdd_growth _ _
      (dilatedCombJordan_growth L) (dilatedCombJordan_growth (-L))
  let hB : B.HasLinearGrowth :=
    nearGap_localJordanScale_growth _ _
      (dilatedCombJordan_growth 0)
  have hAB :
      (localJordanAdd A B).distributionOfLinearGrowth
        (nearGap_localJordanAdd_growth A B hA hB) =
      A.distributionOfLinearGrowth hA +
        B.distributionOfLinearGrowth hB := by
    ext f
    exact nearGap_localJordanAdd_pairing A B hA hB f
  have hAeq :
      A.distributionOfLinearGrowth hA =
        dilatedCombDistribution L + dilatedCombDistribution (-L) := by
    ext f
    exact nearGap_localJordanAdd_pairing
      (dilatedCombJordan L) (dilatedCombJordan (-L))
      (dilatedCombJordan_growth L)
      (dilatedCombJordan_growth (-L)) f
  calc
    nearGapCombDistribution L =
        (localJordanAdd A B).distributionOfLinearGrowth
          (nearGap_localJordanAdd_growth A B hA hB) := by
      rfl
    _ = A.distributionOfLinearGrowth hA +
          B.distributionOfLinearGrowth hB := hAB
    _ = (dilatedCombDistribution L + dilatedCombDistribution (-L)) +
          (-(((2 * Real.cosh (L / 2) : ℝ) : ℂ))) •
            dilatedCombDistribution 0 := by
      rw [hAeq]
      exact congrArg
        (fun T : TemperedDistribution ℝ ℂ =>
          (dilatedCombDistribution L + dilatedCombDistribution (-L)) + T)
        hscale
    _ = nearGapExplicitDilationDistribution L := by
      simp only [nearGapExplicitDilationDistribution]
      first
        | rw [neg_smul, ← sub_eq_add_neg]
        | (ext f; simp [sub_eq_add_neg])

/-- A conditional FT consequence with no new mathematical assumption beyond
the one explicitly identified Jordan-scale pairing obligation. The actual
unconditional FourierSelfdual clause remains OPEN until it is discharged. -/
theorem nearGapCombDistribution_selfdual_of_scale_pairing
    (L : ℝ)
    (hscale :
      (localJordanScale (-(2 * Real.cosh (L / 2)))
        (dilatedCombJordan 0)).distributionOfLinearGrowth
        (nearGap_localJordanScale_growth _ _
          (dilatedCombJordan_growth 0)) =
        (-(((2 * Real.cosh (L / 2) : ℝ) : ℂ))) •
          dilatedCombDistribution 0) :
    (nearGapCombFamily L).FourierSelfdual (nearGapCombFamily_growth L) := by
  change 𝓕 (nearGapCombDistribution L) = nearGapCombDistribution L
  rw [nearGapCombDistribution_eq_explicit_of_scale_pairing L hscale]
  exact nearGapExplicitDilationDistribution_selfdual L

/-- The canonical CT1 Jordan distribution is exactly the physical
three-comb source distribution. The previously explicit scalar bridge has
now been discharged by the positive-counting-measure Jordan calculation.
No conditional Fourier premise is present in this theorem. -/
theorem nearGapCombDistribution_eq_explicit (L : ℝ) :
    nearGapCombDistribution L = nearGapExplicitDilationDistribution L := by
  exact nearGapCombDistribution_eq_explicit_of_scale_pairing L
    (nearGap_dilatedComb_negative_scale_pairing
      0 (2 * Real.cosh (L / 2)) (by positivity))

/-- Unconditional Fourier self-duality of the actual canonical CT1 Jordan
carrier, given the preceding source-preserving distribution identity.
The full original CT1 root still includes its nonzero, evenness, gap,
off-lattice, growth and domain clauses. -/
theorem nearGapCombFamily_fourier_selfdual (L : ℝ) :
    (nearGapCombFamily L).FourierSelfdual (nearGapCombFamily_growth L) := by
  change 𝓕 (nearGapCombDistribution L) = nearGapCombDistribution L
  rw [nearGapCombDistribution_eq_explicit]
  exact nearGapExplicitDilationDistribution_selfdual L

/-- An independently typed evenness consequence of actual Fourier
self-duality. The reflection is the canonical Schwartz pullback under
x -> -x, not a caller-supplied symmetric test packet.

Fourier inversion is valid on the genuine tempered-distribution and
Schwartz spaces; the same Fourier conventions as the source Poisson
identity are used throughout. -/
theorem nearGapCombDistribution_even_schwartz
    (L : ℝ) (f : SchwartzMap ℝ ℂ) :
    nearGapCombDistribution L
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (LinearIsometryEquiv.neg ℝ (E := ℝ)) f) =
      nearGapCombDistribution L f := by
  let D : TemperedDistribution ℝ ℂ := nearGapCombDistribution L
  have hFourier : 𝓕 D = D := nearGapCombFamily_fourier_selfdual L
  have hInv : 𝓕⁻ D = D := by
    calc
      𝓕⁻ D = 𝓕⁻ (𝓕 D) :=
        congrArg (fun T : TemperedDistribution ℝ ℂ => 𝓕⁻ T) hFourier.symm
      _ = D := FourierTransform.fourierInv_fourier_eq D
  have hpair (g : SchwartzMap ℝ ℂ) : D (𝓕⁻ g) = D g := by
    calc
      D (𝓕⁻ g) = (𝓕⁻ D) g := rfl
      _ = D g := congrArg
        (fun T : TemperedDistribution ℝ ℂ => T g) hInv
  have hreflect :
      𝓕⁻ (𝓕⁻ f) =
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (LinearIsometryEquiv.neg ℝ (E := ℝ)) f := by
    have h := SchwartzMap.fourierInv_apply_eq (𝓕⁻ f)
    simpa only [FourierTransform.fourier_fourierInv_eq] using h
  change D (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := ℝ)) f) = D f
  calc
    D (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (LinearIsometryEquiv.neg ℝ (E := ℝ)) f) =
        D (𝓕⁻ (𝓕⁻ f)) := congrArg D hreflect.symm
    _ = D (𝓕⁻ f) := hpair (𝓕⁻ f)
    _ = D f := hpair f

/-! ## Measure-level evenness from Fourier self-duality

Since 𝓕∘𝓕 is reflection, every linearly growing Fourier-self-dual Jordan pair
is even as a distribution. The parent faithfulness theorem
`parts_eq_of_distribution_eq` then upgrades this to reflection invariance of
both canonical Jordan measures. Evenness therefore never has to be assumed
separately for self-dual measures in this class. -/

lemma nearGap_map_neg_locallyFinite (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (Measure.map (fun x : ℝ => -x) μ) := by
  have : IsFiniteMeasureOnCompacts (Measure.map (fun x : ℝ => -x) μ) := ⟨fun K hK => by
    rw [Measure.map_apply measurable_neg hK.measurableSet]
    exact hK.neg.measure_lt_top⟩
  infer_instance

/-- Reflection x ↦ -x of an actual Jordan pair; both parts are pushed forward. -/
def jordanReflect (ν : LocallyFiniteSignedMeasure) : LocallyFiniteSignedMeasure where
  positive := Measure.map (fun x : ℝ => -x) ν.positive
  negative := Measure.map (fun x : ℝ => -x) ν.negative
  positive_locallyFinite := nearGap_map_neg_locallyFinite _
  negative_locallyFinite := nearGap_map_neg_locallyFinite _
  mutuallySingular := by
    obtain ⟨s, hs, hp, hn⟩ := ν.mutuallySingular
    refine ⟨(fun x : ℝ => -x) ⁻¹' s, measurable_neg hs, ?_, ?_⟩
    · rw [Measure.map_apply measurable_neg (measurable_neg hs)]
      simpa [Set.preimage_preimage] using hp
    · rw [Measure.map_apply measurable_neg (measurable_neg hs).compl]
      simpa [Set.preimage_preimage, Set.preimage_compl] using hn

/-- Reflection preserves linear variation growth with the same constant,
because the test intervals are symmetric. -/
lemma jordanReflect_growth (ν : LocallyFiniteSignedMeasure) (hν : ν.HasLinearGrowth) :
    (jordanReflect ν).HasLinearGrowth := by
  obtain ⟨C, hC, hb⟩ := hν
  refine ⟨C, hC, fun R hR => ?_⟩
  have hpre : (fun x : ℝ => -x) ⁻¹' Icc (-R) R = Icc (-R) R := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  change ((Measure.map (fun x : ℝ => -x) ν.positive +
    Measure.map (fun x : ℝ => -x) ν.negative) (Icc (-R) R)).toReal ≤ _
  rw [Measure.add_apply, Measure.map_apply measurable_neg measurableSet_Icc,
    Measure.map_apply measurable_neg measurableSet_Icc, hpre]
  simpa [LocallyFiniteSignedMeasure.totalVariation, Measure.real] using hb R hR

/-- Distributional evenness of any self-dual linearly growing Jordan pair. -/
theorem even_schwartz_of_selfdual (ν : LocallyFiniteSignedMeasure)
    (hν : ν.HasLinearGrowth) (hself : ν.FourierSelfdual hν) (f : SchwartzMap ℝ ℂ) :
    ν.distributionOfLinearGrowth hν
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := ℝ)) f) =
    ν.distributionOfLinearGrowth hν f := by
  let D : TemperedDistribution ℝ ℂ := ν.distributionOfLinearGrowth hν
  have hFourier : 𝓕 D = D := hself
  have hInv : 𝓕⁻ D = D := by
    calc 𝓕⁻ D = 𝓕⁻ (𝓕 D) :=
          congrArg (fun T : TemperedDistribution ℝ ℂ => 𝓕⁻ T) hFourier.symm
      _ = D := FourierTransform.fourierInv_fourier_eq D
  have hpair (g : SchwartzMap ℝ ℂ) : D (𝓕⁻ g) = D g := by
    calc D (𝓕⁻ g) = (𝓕⁻ D) g := rfl
      _ = D g := congrArg (fun T : TemperedDistribution ℝ ℂ => T g) hInv
  have hreflect : 𝓕⁻ (𝓕⁻ f) = SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (LinearIsometryEquiv.neg ℝ (E := ℝ)) f := by
    have h := SchwartzMap.fourierInv_apply_eq (𝓕⁻ f)
    simpa only [FourierTransform.fourier_fourierInv_eq] using h
  change D (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := ℝ)) f) = D f
  rw [← hreflect, hpair, hpair]

/-- Measure-level evenness: both canonical Jordan parts of a linearly growing
Fourier-self-dual Jordan pair are invariant under x ↦ -x. -/
theorem jordan_even_of_selfdual (ν : LocallyFiniteSignedMeasure)
    (hν : ν.HasLinearGrowth) (hself : ν.FourierSelfdual hν) :
    Measure.map (fun x : ℝ => -x) ν.positive = ν.positive ∧
      Measure.map (fun x : ℝ => -x) ν.negative = ν.negative := by
  have hdist : (jordanReflect ν).distributionOfLinearGrowth (jordanReflect_growth ν hν) =
      ν.distributionOfLinearGrowth hν := by
    ext f
    rw [← even_schwartz_of_selfdual ν hν hself f,
      LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply,
      LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply]
    change (∫ x, f x ∂Measure.map (fun x : ℝ => -x) ν.positive) -
        (∫ x, f x ∂Measure.map (fun x : ℝ => -x) ν.negative) = _
    rw [integral_map measurable_neg.aemeasurable f.continuous.aestronglyMeasurable,
      integral_map measurable_neg.aemeasurable f.continuous.aestronglyMeasurable]
    rfl
  exact (ν.parts_eq_of_distribution_eq _ hν (jordanReflect_growth ν hν) hdist.symm).imp
    (fun h => h.symm) (fun h => h.symm)

/-- The CT1 family is even at the level of its genuine canonical Jordan
measures, as the paper's CT1 statement requires. -/
theorem nearGapCombFamily_jordan_even (L : ℝ) :
    Measure.map (fun x : ℝ => -x) (nearGapCombFamily L).positive =
        (nearGapCombFamily L).positive ∧
      Measure.map (fun x : ℝ => -x) (nearGapCombFamily L).negative =
        (nearGapCombFamily L).negative :=
  jordan_even_of_selfdual _ (nearGapCombFamily_growth L)
    (nearGapCombFamily_fourier_selfdual L)

lemma nearGap_origin_zero (mu : Measure ℝ) {a : ℝ} (ha : 0<a)
    (hgap : mu (Ioo (-a) a)=0) : mu {0}=0 := by
  apply measure_mono_null _ hgap
  intro x hx
  simp only [mem_singleton_iff] at hx
  subst x
  exact ⟨by linarith, ha⟩

lemma nearGap_triangle_bound (mu : Measure ℝ) [IsLocallyFiniteMeasure mu]
    {a : ℝ} (ha : a≤1) (hgap : mu (Ioo (-a) a)=0) :
    (∫ x, unitTriangle x ∂mu)≤(1-a)*mu.real (Icc (-1) 1) := by
  let g : ℝ→ℝ := (Icc (-1) 1).indicator (fun _ => 1-a)
  have hg : Integrable g mu :=
    (integrableOn_const isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc
  have hae : ∀ᵐ x ∂mu, x∉Ioo (-a) a := by
    apply ae_iff.mpr
    simpa only [not_not, ofPred_mem_eq] using hgap
  have hle : ∀ᵐ x ∂mu, unitTriangle x≤g x := by
    filter_upwards [hae] with x hx
    have habs : a≤|x| := by
      by_contra h
      exact hx (abs_lt.mp (lt_of_not_ge h))
    by_cases hbox : x∈Icc (-1) 1
    · dsimp only [g]
      rw [indicator_of_mem hbox]
      exact max_le (by linarith) (by linarith)
    · dsimp only [g]
      rw [indicator_of_notMem hbox]
      have hxabs : 1≤|x| := by
        by_contra h
        have hh := abs_lt.mp (lt_of_not_ge h)
        exact hbox ⟨hh.1.le,hh.2.le⟩
      rw [unitTriangle_eq_zero_of_one_le_abs hxabs]
  have ht : Integrable unitTriangle mu := hg.mono'
    unitTriangle_continuous.aestronglyMeasurable (hle.mono fun x hx => by
      rwa [Real.norm_of_nonneg (unitTriangle_nonneg x)])
  calc
    _ ≤ ∫ x, g x ∂mu := integral_mono_ae ht hg hle
    _ = _ := by
      rw [integral_indicator measurableSet_Icc,setIntegral_const]
      simp [smul_eq_mul,mul_comm]

lemma nearGap_sinc_negative_zero (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth) {a : ℝ} (ha : 0<a)
    (hgap : hasNearGap nu a) (hoff : nu.OffLatticeNonnegative) :
    (∫ x, sincSquared x ∂nu.negative)=0 := by
  rw [←sincSquared_integral_compl_lattice nu.negative (nu.negative_hasLinearGrowth hnu)
    (nearGap_origin_zero nu.negative ha hgap.2)]
  rw [show nu.negative.restrict integerLatticeᶜ=0 from Measure.restrict_eq_zero.mpr hoff]
  simp

/-- Exact HT2 measure budget, with actual Jordan parts and literal variation.
The proof does not require evenness, so in particular covers the paper's even measures. -/
theorem near_gap_mass_bound (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth) (hself : nu.FourierSelfdual hnu)
    {a R d : ℝ} (ha : 0<a) (ha1 : a≤1) (hgap : hasNearGap nu a)
    (hoff : nu.OffLatticeNonnegative) (hR : 1≤R) (hd : 0<d) (_hdhalf : d≤1/2) :
    nu.negative (signedBudgetRegion R d)=0 ∧
    nu.positive.real (signedBudgetRegion R d)≤
      (Real.pi^2*R^2/(4*d^2))*(1-a)*nu.totalVariation.real (Icc (-1) 1) := by
  have hE : signedBudgetRegion R d⊆integerLatticeᶜ := by
    intro x hx hn
    obtain ⟨n,hn⟩ := hn
    have hh := signedBudgetRegion_integer_distance hx n
    change (n:ℝ)=x at hn
    rw [←hn,sub_self,abs_zero] at hh
    linarith
  refine ⟨measure_mono_null hE hoff,?_⟩
  have hpair := signed_sinc_triangle_pairing nu hnu hself
  change (∫ x, sincSquared x ∂nu.positive)-(∫ x, sincSquared x ∂nu.negative)=
    (∫ x, unitTriangle x ∂nu.positive)-(∫ x, unitTriangle x ∂nu.negative) at hpair
  rw [nearGap_sinc_negative_zero nu hnu ha hgap hoff,sub_zero] at hpair
  have htriangle := nearGap_triangle_bound nu.positive ha1 hgap.1
  have htri_nonneg : 0≤∫ x, unitTriangle x ∂nu.negative :=
    integral_nonneg unitTriangle_nonneg
  have htv : nu.positive.real (Icc (-1) 1)≤nu.totalVariation.real (Icc (-1) 1) := by
    apply ENNReal.toReal_mono isCompact_Icc.measure_lt_top.ne
    change nu.positive _≤(nu.positive+nu.negative) _
    rw [Measure.add_apply]
    exact le_add_of_nonneg_right (by positivity)
  have hupper : (∫ x, sincSquared x ∂nu.positive)≤
      (1-a)*nu.totalVariation.real (Icc (-1) 1) := by
    rw [hpair]
    exact (sub_le_self _ htri_nonneg).trans (htriangle.trans
      (mul_le_mul_of_nonneg_left htv (by linarith)))
  have hi := sincSquared_integrable_of_linear_growth nu.positive (nu.positive_hasLinearGrowth hnu)
  have hlower : (4*d^2/(Real.pi^2*R^2))*nu.positive.real (signedBudgetRegion R d)≤
      ∫ x, sincSquared x ∂nu.positive := by
    calc
      _ = ∫ _x in signedBudgetRegion R d, (4*d^2/(Real.pi^2*R^2)) ∂nu.positive := by
        rw [setIntegral_const,smul_eq_mul,mul_comm]
      _ ≤ ∫ x in signedBudgetRegion R d, sincSquared x ∂nu.positive := by
        apply setIntegral_mono_on
        · exact integrableOn_const (signedBudgetRegion_finite nu.positive R d).ne
        · exact hi.integrableOn
        · exact signedBudgetRegion_measurable R d
        · intro x hx
          exact sincSquared_lower_on_signedBudgetRegion hR hd hx
      _ ≤ _ := setIntegral_le_integral hi (Eventually.of_forall sincSquared_nonneg)
  have hc : 0<4*d^2/(Real.pi^2*R^2) := by positivity
  have hh : nu.positive.real (signedBudgetRegion R d)≤
      ((1-a)*nu.totalVariation.real (Icc (-1) 1))/(4*d^2/(Real.pi^2*R^2)) :=
    (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hlower.trans hupper)
  convert hh using 1
  field_simp [hd.ne', (show R≠0 by linarith)]

/-- Quantitative CT1 concentration away from the integers.

This specializes the existing source-bound near-gap mass inequality
to the *actual* canonical dilated-comb Jordan carrier, using its
unconditional Fourier bridge, physical gap, off-lattice support,
and uniform variation bound. As L tends to zero the right side
vanishes at fixed finite R and d. It is not a total-variation
convergence theorem and does not substitute for the original
general controlled-limit root. -/
theorem nearGapCombFamily_offinteger_mass_budget
    {L R d : ℝ}
    (hL : 0 < L) (hu : L < Real.log 2)
    (hR : 1 ≤ R) (hd : 0 < d) (hdhalf : d ≤ 1 / 2) :
    (nearGapCombFamily L).negative (signedBudgetRegion R d) = 0 ∧
    (nearGapCombFamily L).positive.real (signedBudgetRegion R d) ≤
      (Real.pi ^ 2 * R ^ 2 / (4 * d ^ 2)) *
        (1 - Real.exp (-L)) * 36 := by
  have he : Real.exp (-L) ≤ (1 : ℝ) := by
    have h := Real.exp_le_exp.mpr
      (show -L ≤ (0 : ℝ) by linarith)
    simpa only [Real.exp_zero] using h
  have hgap := nearGapCombFamily_actual_gap hL.le
  have hmass := near_gap_mass_bound
    (nearGapCombFamily L) (nearGapCombFamily_growth L)
    (nearGapCombFamily_fourier_selfdual L)
    (Real.exp_pos (-L)) he hgap
    (nearGapCombFamily_offlattice_nonnegative L) hR hd hdhalf
  have htv :
      (nearGapCombFamily L).totalVariation.real
        (Icc (-(1 : ℝ)) 1) ≤ 36 := by
    have h := nearGapCombFamily_uniform_variation
      hL.le hu.le (R := 1) (by norm_num)
    norm_num at h ⊢
    exact h
  have hweight : 0 ≤
      (Real.pi ^ 2 * R ^ 2 / (4 * d ^ 2)) *
        (1 - Real.exp (-L)) := by
    have hnonneg : 0 ≤ 1 - Real.exp (-L) := sub_nonneg.mpr he
    positivity
  refine ⟨hmass.1, ?_⟩
  exact hmass.2.trans (mul_le_mul_of_nonneg_left htv hweight)

/-- Original CT1 (R1-CT1) actual dilation-near-gap family, with all
physical source and domain clauses in the theorem type.

No hypotheses give the conclusion: the only premises restrict the genuine
dilation parameter to 0 < L < log 2. Evenness is stated both for Schwartz
pairings and for the canonical Jordan measures themselves; the signed
compact-identity component prevents substitution of an unrelated self-dual
distribution. Uniform variation, canonical Jordan gap/origin, integer support
of negative mass, the nonzero positive part and the paper's exact gap-edge
atom exp(-L/2) at exp(-L) are all carried by the exact same source measure.
Aggregate registration and full release remain separate gates. -/
theorem dilation_near_gap_family
    (L : ℝ) (hL : 0 < L) (hu : L < Real.log 2) :
    (∀ K : Set ℝ, ∀ hK : IsCompact K,
      localSignedCompactRestriction (nearGapCombFamily L) K hK =
        localSignedCompactRestriction (dilatedCombJordan L) K hK +
        localSignedCompactRestriction (dilatedCombJordan (-L)) K hK -
        (2 * Real.cosh (L / 2)) •
          localSignedCompactRestriction (dilatedCombJordan 0) K hK) ∧
    (nearGapCombFamily L).HasLinearGrowth ∧
    CommonLinearMassBound 18 (nearGapCombFamily L).totalVariation ∧
    (nearGapCombFamily L).FourierSelfdual (nearGapCombFamily_growth L) ∧
    (∀ f : SchwartzMap ℝ ℂ,
      nearGapCombDistribution L
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (LinearIsometryEquiv.neg ℝ (E := ℝ)) f) =
        nearGapCombDistribution L f) ∧
    hasNearGap (nearGapCombFamily L) (Real.exp (-L)) ∧
    ((1 / 2 : ℝ) < Real.exp (-L) ∧ Real.exp (-L) < 1) ∧
    (nearGapCombFamily L).OffLatticeNonnegative ∧
    ((nearGapCombFamily L).positive ({0} : Set ℝ) = 0 ∧
      (nearGapCombFamily L).negative ({0} : Set ℝ) = 0) ∧
    (nearGapCombFamily L).positive ≠ 0 ∧
    (Measure.map (fun x : ℝ => -x) (nearGapCombFamily L).positive =
        (nearGapCombFamily L).positive ∧
      Measure.map (fun x : ℝ => -x) (nearGapCombFamily L).negative =
        (nearGapCombFamily L).negative) ∧
    ((nearGapCombFamily L).positive.real ({Real.exp (-L)} : Set ℝ) =
        Real.exp (-L / 2) ∧
      (nearGapCombFamily L).negative ({Real.exp (-L)} : Set ℝ) = 0) := by
  exact ⟨fun K hK => nearGapCombFamily_compactRestriction L K hK,
    nearGapCombFamily_growth L,
    nearGapCombFamily_common_growth hL.le hu.le,
    nearGapCombFamily_fourier_selfdual L,
    fun f => nearGapCombDistribution_even_schwartz L f,
    nearGapCombFamily_actual_gap hL.le,
    nearGapComb_radius_bounds hL hu,
    nearGapCombFamily_offlattice_nonnegative L,
    nearGapCombFamily_origin_jordan_zero L,
    nearGapCombFamily_positive_nonzero hL hu,
    nearGapCombFamily_jordan_even L,
    nearGapCombFamily_gap_edge_atom hL hu⟩


/-! ## R1-HT2 controlled limit (quantitative, compactness-free) -/

/-- Fourier transform of a real translate of a genuine Schwartz test: the
translation becomes the exact phase exp(-2πi y ξ). -/
theorem nearGap_fourier_translate (test : SchwartzMap ℝ ℂ) (y ξ : ℝ) :
    (𝓕 (test.compSubConstCLM ℂ y)) ξ =
      Complex.exp (((-2 * Real.pi * y * ξ) : ℝ) * Complex.I) * (𝓕 test) ξ := by
  change 𝓕 (test.compSubConstCLM ℂ y : ℝ → ℂ) ξ = _
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul, SchwartzMap.compSubConstCLM_apply]
  let F := fun x : ℝ => Complex.exp (((-2 * Real.pi * x * ξ) : ℝ) * Complex.I) *
    test (x - y)
  change (∫ x : ℝ, F x) = _
  rw [← integral_add_right_eq_self F y, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [F]
  rw [add_sub_cancel_right, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Translated sinc/triangle identity for every linearly growing
Fourier-self-dual Jordan pair and every real shift y. It is the parent H1
regularization argument applied to the translated regularized triangle. -/
theorem translated_sinc_triangle_pairing (ν : LocallyFiniteSignedMeasure)
    (hν : ν.HasLinearGrowth) (hself : ν.FourierSelfdual hν) (y : ℝ) :
    (∫ x, Complex.exp (((-2 * Real.pi * y * x) : ℝ) * Complex.I) * (sincSquared x : ℂ)
        ∂ν.positive) -
      (∫ x, Complex.exp (((-2 * Real.pi * y * x) : ℝ) * Complex.I) * (sincSquared x : ℂ)
        ∂ν.negative) =
    (∫ x, (unitTriangle (x - y) : ℂ) ∂ν.positive) -
      (∫ x, (unitTriangle (x - y) : ℂ) ∂ν.negative) := by
  let e : ℝ → ℂ := fun x => Complex.exp (((-2 * Real.pi * y * x) : ℝ) * Complex.I)
  have he (x : ℝ) : ‖e x‖ = 1 := by
    simp only [e]
    exact Complex.norm_exp_ofReal_mul_I _
  let T : ℕ → SchwartzMap ℝ ℂ := fun n =>
    (regularizedTriangle (separatorBump n)).compSubConstCLM ℂ y
  have hleft (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] (hμ : LinearMassGrowth μ) :
      Tendsto (fun n => ∫ x, 𝓕 (T n : ℝ → ℂ) x ∂μ) atTop
        (𝓝 (∫ x, e x * (sincSquared x : ℂ) ∂μ)) := by
    have hrw (n : ℕ) (x : ℝ) : 𝓕 (T n : ℝ → ℂ) x =
        e x * 𝓕 (regularizedTriangle (separatorBump n) : ℝ → ℂ) x := by
      have h := nearGap_fourier_translate (regularizedTriangle (separatorBump n)) y x
      simpa only [T, e, SchwartzMap.fourier_coe] using h
    simp_rw [hrw]
    apply tendsto_integral_of_dominated_convergence sincSquared
    · intro n
      have hc : Continuous e := by simp only [e]; fun_prop
      exact (hc.mul (𝓕 (regularizedTriangle (separatorBump n))).continuous).aestronglyMeasurable
    · exact sincSquared_integrable_of_linear_growth μ hμ
    · intro n
      refine Eventually.of_forall (fun x => ?_)
      rw [norm_mul, he, one_mul]
      exact regularizedTriangle_fourier_norm_le _ x
    · refine Eventually.of_forall (fun x => ?_)
      exact (regularizedTriangle_fourier_tendsto x).const_mul (e x)
  have hright (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
      Tendsto (fun n => ∫ x, T n x ∂μ) atTop
        (𝓝 (∫ x, (unitTriangle (x - y) : ℂ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => (Icc (-2 : ℝ) 2).indicator (fun _ => (1 : ℝ)) (x - y))
    · intro n
      exact (T n).continuous.aestronglyMeasurable
    · have hK : IsCompact (Icc (y - 2) (y + 2)) := isCompact_Icc
      have hind : (fun x => (Icc (-2 : ℝ) 2).indicator (fun _ => (1 : ℝ)) (x - y)) =
          (Icc (y - 2) (y + 2)).indicator (fun _ => (1 : ℝ)) := by
        funext x
        by_cases hx : x ∈ Icc (y - 2) (y + 2)
        · rw [indicator_of_mem hx, indicator_of_mem]
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
        · rw [indicator_of_notMem hx, indicator_of_notMem]
          intro h
          exact hx ⟨by linarith [h.1], by linarith [h.2]⟩
      rw [hind]
      exact (integrableOn_const (μ := μ) (s := Icc (y - 2) (y + 2)) (C := (1 : ℝ))
        hK.measure_lt_top.ne).integrable_indicator measurableSet_Icc
    · intro n
      refine Eventually.of_forall (fun x => ?_)
      simpa only [T, SchwartzMap.compSubConstCLM_apply] using
        regularizedTriangle_norm_le_indicator n (x - y)
    · refine Eventually.of_forall (fun x => ?_)
      simpa only [T, SchwartzMap.compSubConstCLM_apply] using
        regularizedTriangle_tendsto (x - y)
  have hL := (hleft ν.positive (ν.positive_hasLinearGrowth hν)).sub
    (hleft ν.negative (ν.negative_hasLinearGrowth hν))
  have hR := (hright ν.positive).sub (hright ν.negative)
  have heq (n : ℕ) :
      (∫ x, 𝓕 (T n : ℝ → ℂ) x ∂ν.positive) - (∫ x, 𝓕 (T n : ℝ → ℂ) x ∂ν.negative) =
      (∫ x, T n x ∂ν.positive) - (∫ x, T n x ∂ν.negative) := by
    exact congrArg (fun D : TemperedDistribution ℝ ℂ => D (T n)) hself
  exact tendsto_nhds_unique hL (hR.congr' (Eventually.of_forall (fun n => (heq n).symm)))


/-- Positive sinc mass of a near-gapped self-dual off-lattice-nonnegative
Jordan pair is bounded by the gap deficit times the local variation. -/
theorem nearGap_sinc_positive_le (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth) (hself : nu.FourierSelfdual hnu)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hgap : hasNearGap nu a)
    (hoff : nu.OffLatticeNonnegative) :
    (∫ x, sincSquared x ∂nu.positive) ≤ (1 - a) * nu.totalVariation.real (Icc (-1) 1) := by
  have hpair := signed_sinc_triangle_pairing nu hnu hself
  change (∫ x, sincSquared x ∂nu.positive) - (∫ x, sincSquared x ∂nu.negative) =
    (∫ x, unitTriangle x ∂nu.positive) - (∫ x, unitTriangle x ∂nu.negative) at hpair
  rw [nearGap_sinc_negative_zero nu hnu ha hgap hoff, sub_zero] at hpair
  have htriangle := nearGap_triangle_bound nu.positive ha1 hgap.1
  have htri_nonneg : 0 ≤ ∫ x, unitTriangle x ∂nu.negative :=
    integral_nonneg unitTriangle_nonneg
  have htv : nu.positive.real (Icc (-1) 1) ≤ nu.totalVariation.real (Icc (-1) 1) := by
    apply ENNReal.toReal_mono isCompact_Icc.measure_lt_top.ne
    change nu.positive _ ≤ (nu.positive + nu.negative) _
    rw [Measure.add_apply]
    exact le_add_of_nonneg_right (by positivity)
  rw [hpair]
  exact (sub_le_self _ htri_nonneg).trans (htriangle.trans
    (mul_le_mul_of_nonneg_left htv (by linarith)))

/-- Uniform translated-triangle bound: for every real shift y, the actual
signed triangle mass around y is at most the gap deficit times the local
variation. No compactness or limiting measure is used. -/
theorem nearGap_translated_triangle_bound (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth) (hself : nu.FourierSelfdual hnu)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hgap : hasNearGap nu a)
    (hoff : nu.OffLatticeNonnegative) (y : ℝ) :
    |(∫ x, unitTriangle (x - y) ∂nu.positive) - (∫ x, unitTriangle (x - y) ∂nu.negative)| ≤
      (1 - a) * nu.totalVariation.real (Icc (-1) 1) := by
  let e : ℝ → ℂ := fun x => Complex.exp (((-2 * Real.pi * y * x) : ℝ) * Complex.I)
  have he (x : ℝ) : ‖e x‖ = 1 := by
    simp only [e]
    exact Complex.norm_exp_ofReal_mul_I _
  have hid := translated_sinc_triangle_pairing nu hnu hself y
  have hneg0 : (∫ x, sincSquared x ∂nu.negative) = 0 :=
    nearGap_sinc_negative_zero nu hnu ha hgap hoff
  have hsi : Integrable sincSquared nu.negative :=
    sincSquared_integrable_of_linear_growth nu.negative (nu.negative_hasLinearGrowth hnu)
  have hae : sincSquared =ᵐ[nu.negative] 0 :=
    (integral_eq_zero_iff_of_nonneg sincSquared_nonneg hsi).mp hneg0
  have hnegE : (∫ x, e x * (sincSquared x : ℂ) ∂nu.negative) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hae] with x hx
    simp only [Pi.zero_apply] at hx
    simp [hx]
  have hpos_le : ‖∫ x, e x * (sincSquared x : ℂ) ∂nu.positive‖ ≤
      ∫ x, sincSquared x ∂nu.positive := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    apply integral_congr_ae
    filter_upwards with x
    rw [norm_mul, he, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sincSquared_nonneg x)]
  have hcomplex : ((∫ x, unitTriangle (x - y) ∂nu.positive) -
      (∫ x, unitTriangle (x - y) ∂nu.negative) : ℝ) =
      (∫ x, e x * (sincSquared x : ℂ) ∂nu.positive) := by
    push_cast
    rw [← integral_complex_ofReal, ← integral_complex_ofReal]
    rw [← hid, hnegE, sub_zero]
  have habs : |(∫ x, unitTriangle (x - y) ∂nu.positive) -
      (∫ x, unitTriangle (x - y) ∂nu.negative)| =
      ‖∫ x, e x * (sincSquared x : ℂ) ∂nu.positive‖ := by
    rw [← hcomplex, Complex.norm_real, Real.norm_eq_abs]
  rw [habs]
  exact hpos_le.trans (nearGap_sinc_positive_le nu hnu hself ha ha1 hgap hoff)

/-! ## Integer tent interpolation -/

theorem unitTriangle_sub_floor (x : ℝ) :
    unitTriangle (x - (⌊x⌋ : ℝ)) = 1 - Int.fract x := by
  rw [Int.self_sub_floor, unitTriangle, abs_of_nonneg (Int.fract_nonneg x)]
  exact max_eq_left (by linarith [Int.fract_lt_one x])

theorem unitTriangle_sub_floor_succ (x : ℝ) :
    unitTriangle (x - ((⌊x⌋ + 1 : ℤ) : ℝ)) = Int.fract x := by
  have h : x - ((⌊x⌋ + 1 : ℤ) : ℝ) = Int.fract x - 1 := by
    rw [← Int.self_sub_floor]; push_cast; ring
  have hneg : Int.fract x - 1 < 0 := by linarith [Int.fract_lt_one x]
  rw [h, unitTriangle, abs_of_neg hneg, max_eq_left] <;> linarith [Int.fract_nonneg x]

theorem unitTriangle_sub_int_eq_zero (x : ℝ) (j : ℤ)
    (h1 : j ≠ ⌊x⌋) (h2 : j ≠ ⌊x⌋ + 1) : unitTriangle (x - j) = 0 := by
  apply unitTriangle_eq_zero_of_one_le_abs
  have hfl := Int.floor_le x
  have hlt := Int.lt_floor_add_one x
  rcases lt_or_gt_of_ne h1 with hj | hj
  · have hj' : (j : ℝ) ≤ (⌊x⌋ : ℝ) - 1 := by
      have : j ≤ ⌊x⌋ - 1 := by omega
      exact_mod_cast this
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hj2 : ⌊x⌋ + 2 ≤ j := by omega
    have hj' : (⌊x⌋ : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hj2
    rw [abs_of_neg (by linarith)]
    linarith

/-- Closed form of any finite tent sum: only the two lattice points ⌊x⌋ and
⌊x⌋ + 1 can contribute, with the piecewise-linear weights. -/
theorem tent_sum_eq (S : Finset ℤ) (c : ℤ → ℂ) (x : ℝ) :
    ∑ j ∈ S, c j * (unitTriangle (x - j) : ℂ) =
      (if ⌊x⌋ ∈ S then c ⌊x⌋ * ((1 - Int.fract x : ℝ) : ℂ) else 0) +
      (if ⌊x⌋ + 1 ∈ S then c (⌊x⌋ + 1) * ((Int.fract x : ℝ) : ℂ) else 0) := by
  classical
  let k := ⌊x⌋
  let T : Finset ℤ := {k, k + 1}
  let F : ℤ → ℂ := fun j => c j * (unitTriangle (x - j) : ℂ)
  have hsub : ∑ j ∈ S, F j = ∑ j ∈ T.filter (· ∈ S), F j := by
    symm
    apply Finset.sum_subset
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
    · intro j hjS hjT
      have hnot : j ≠ k ∧ j ≠ k + 1 := by
        constructor
        · rintro rfl
          exact hjT (Finset.mem_filter.mpr ⟨by simp [T], hjS⟩)
        · rintro rfl
          exact hjT (Finset.mem_filter.mpr ⟨by simp [T], hjS⟩)
      simp only [F, unitTriangle_sub_int_eq_zero x j hnot.1 hnot.2, Complex.ofReal_zero, mul_zero]
  rw [show (∑ j ∈ S, c j * (unitTriangle (x - j) : ℂ)) = ∑ j ∈ S, F j from rfl, hsub,
    Finset.sum_filter, Finset.sum_pair (by omega : k ≠ k + 1)]
  simp only [F, k, unitTriangle_sub_floor, unitTriangle_sub_floor_succ]

/-- Finite tent interpolant of a test at the integers in [-(N+1), N+1]. -/
def tentInterpolant (φ : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1), φ j * (unitTriangle (x - j) : ℂ)

theorem tentInterpolant_continuous (φ : ℝ → ℂ) (N : ℕ) :
    Continuous (tentInterpolant φ N) := by
  unfold tentInterpolant
  refine continuous_finsetSum _ (fun j _ => ?_)
  exact continuous_const.mul (Complex.continuous_ofReal.comp
    (unitTriangle_continuous.comp (continuous_id.sub continuous_const)))

theorem unitTriangle_shift_integrable (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] (y : ℝ) :
    Integrable (fun x => (unitTriangle (x - y) : ℂ)) μ := by
  have hK : IsCompact (Icc (y - 1) (y + 1)) := isCompact_Icc
  refine Integrable.mono' ((integrableOn_const (μ := μ) (s := Icc (y - 1) (y + 1))
      (C := (1 : ℝ)) hK.measure_lt_top.ne).integrable_indicator measurableSet_Icc)
    (Complex.continuous_ofReal.comp
      (unitTriangle_continuous.comp (continuous_id.sub continuous_const))).aestronglyMeasurable ?_
  refine Eventually.of_forall (fun x => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (unitTriangle_nonneg _)]
  by_cases hx : x ∈ Icc (y - 1) (y + 1)
  · rw [indicator_of_mem hx]
    exact max_le (by linarith [abs_nonneg (x - y)]) (by norm_num)
  · rw [indicator_of_notMem hx, unitTriangle_eq_zero_of_one_le_abs]
    by_contra h
    have h' := abs_lt.mp (lt_of_not_ge h)
    exact hx ⟨by linarith [h'.1], by linarith [h'.2]⟩

theorem tentInterpolant_integrable (φ : ℝ → ℂ) (N : ℕ) (μ : Measure ℝ)
    [IsLocallyFiniteMeasure μ] : Integrable (tentInterpolant φ N) μ := by
  unfold tentInterpolant
  exact integrable_finsetSum _ (fun j _ => (unitTriangle_shift_integrable μ j).const_mul _)

theorem tentInterpolant_integral (φ : ℝ → ℂ) (N : ℕ) (μ : Measure ℝ)
    [IsLocallyFiniteMeasure μ] :
    (∫ x, tentInterpolant φ N x ∂μ) =
      ∑ j ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1),
        φ j * (((∫ x, unitTriangle (x - j) ∂μ) : ℝ) : ℂ) := by
  unfold tentInterpolant
  rw [integral_finsetSum (Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1))
    (f := fun (j : ℤ) (x : ℝ) => φ j * (unitTriangle (x - j) : ℂ))
    (fun j _ => (unitTriangle_shift_integrable μ j).const_mul _)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_const_mul, integral_complex_ofReal]

/-- On [-N, N] the interpolant is the genuine piecewise-linear interpolant. -/
theorem tentInterpolant_interior (φ : ℝ → ℂ) (N : ℕ) {x : ℝ} (hx : |x| ≤ N) :
    tentInterpolant φ N x =
      φ ⌊x⌋ * ((1 - Int.fract x : ℝ) : ℂ) + φ (⌊x⌋ + 1 : ℤ) * ((Int.fract x : ℝ) : ℂ) := by
  have hb := abs_le.mp hx
  have hlo : -(N : ℤ) ≤ ⌊x⌋ := Int.le_floor.mpr (by push_cast; linarith)
  have hhi : ⌊x⌋ ≤ (N : ℤ) := by
    have h2 : (⌊x⌋ : ℝ) ≤ N := (Int.floor_le x).trans hb.2
    exact_mod_cast h2
  unfold tentInterpolant
  rw [tent_sum_eq, if_pos (Finset.mem_Icc.mpr ⟨by omega, by omega⟩),
    if_pos (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]

/-- Pointwise size of the interpolant by its two active nodes. -/
theorem tentInterpolant_norm_le (φ : ℝ → ℂ) (N : ℕ) (x : ℝ) :
    ‖tentInterpolant φ N x‖ ≤
      ‖φ ⌊x⌋‖ * (1 - Int.fract x) + ‖φ (⌊x⌋ + 1 : ℤ)‖ * Int.fract x := by
  have ht0 := Int.fract_nonneg x
  have ht1 := Int.fract_lt_one x
  unfold tentInterpolant
  rw [tent_sum_eq]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · split_ifs
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    · simp only [norm_zero]; exact mul_nonneg (norm_nonneg _) (by linarith)
  · split_ifs
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    · simp only [norm_zero]; exact mul_nonneg (norm_nonneg _) ht0

/-- The fractional weight product is dominated by the distance to every integer. -/
theorem fract_mul_one_sub_le_abs_sub_int (x : ℝ) (n : ℤ) :
    Int.fract x * (1 - Int.fract x) ≤ |x - n| := by
  have ht0 := Int.fract_nonneg x
  have ht1 := Int.fract_lt_one x
  have hx : x = ⌊x⌋ + Int.fract x := (Int.floor_add_fract x).symm
  rcases le_or_gt n ⌊x⌋ with hn | hn
  · have hn' : (n : ℝ) ≤ ⌊x⌋ := by exact_mod_cast hn
    have : Int.fract x ≤ |x - n| := by rw [abs_of_nonneg (by linarith)]; linarith
    nlinarith
  · have hn2 : ⌊x⌋ + 1 ≤ n := by omega
    have hn' : (⌊x⌋ : ℝ) + 1 ≤ n := by exact_mod_cast hn2
    have : 1 - Int.fract x ≤ |x - n| := by rw [abs_of_neg (by linarith)]; linarith
    nlinarith

/-! ## Schwartz Lipschitz and decay constants -/

/-- The derivative sup-norm constant of a genuine Schwartz test. -/
def schwartzLipConst (φ : SchwartzMap ℝ ℂ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℂ φ)

theorem schwartz_lipschitz (φ : SchwartzMap ℝ ℂ) (x y : ℝ) :
    ‖φ x - φ y‖ ≤ schwartzLipConst φ * |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := (φ : ℝ → ℂ)) (s := univ)
    (fun z _ => φ.differentiableAt) (fun z _ => by
      have := SchwartzMap.norm_le_seminorm ℝ (SchwartzMap.derivCLM ℝ ℂ φ) z
      simpa [schwartzLipConst] using this) convex_univ (mem_univ y) (mem_univ x)
  simpa [Real.norm_eq_abs, schwartzLipConst] using h

/-- Interior interpolation error: at most twice the Lipschitz constant times the
fractional weight product, which vanishes on the lattice. -/
theorem tentInterpolant_interior_error (φ : SchwartzMap ℝ ℂ) (N : ℕ) {x : ℝ} (hx : |x| ≤ N) :
    ‖φ x - tentInterpolant φ N x‖ ≤
      2 * schwartzLipConst φ * (Int.fract x * (1 - Int.fract x)) := by
  have ht0 := Int.fract_nonneg x
  have ht1 := Int.fract_lt_one x
  have hxk : x - ⌊x⌋ = Int.fract x := Int.self_sub_floor x
  rw [tentInterpolant_interior φ N hx]
  have hsplit : φ x - (φ ⌊x⌋ * ((1 - Int.fract x : ℝ) : ℂ) +
      φ (⌊x⌋ + 1 : ℤ) * ((Int.fract x : ℝ) : ℂ)) =
      (φ x - φ ⌊x⌋) * ((1 - Int.fract x : ℝ) : ℂ) +
        (φ x - φ (⌊x⌋ + 1 : ℤ)) * ((Int.fract x : ℝ) : ℂ) := by
    push_cast; ring
  rw [hsplit]
  have h1 := schwartz_lipschitz φ x ⌊x⌋
  have h2 := schwartz_lipschitz φ x (⌊x⌋ + 1 : ℤ)
  have hd1 : |x - (⌊x⌋ : ℝ)| = Int.fract x := by rw [hxk, abs_of_nonneg ht0]
  have hd2 : |x - ((⌊x⌋ + 1 : ℤ) : ℝ)| = 1 - Int.fract x := by
    push_cast
    rw [show x - ((⌊x⌋ : ℝ) + 1) = Int.fract x - 1 by rw [← hxk]; ring,
      abs_of_neg (by linarith)]
    ring
  rw [hd1] at h1
  rw [hd2] at h2
  have hM : 0 ≤ schwartzLipConst φ := by
    unfold schwartzLipConst; exact apply_nonneg _ _
  calc _ ≤ ‖(φ x - φ ⌊x⌋) * ((1 - Int.fract x : ℝ) : ℂ)‖ +
        ‖(φ x - φ (⌊x⌋ + 1 : ℤ)) * ((Int.fract x : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = ‖φ x - φ ⌊x⌋‖ * (1 - Int.fract x) + ‖φ x - φ (⌊x⌋ + 1 : ℤ)‖ * Int.fract x := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_nonneg ht0]
    _ ≤ (schwartzLipConst φ * Int.fract x) * (1 - Int.fract x) +
        (schwartzLipConst φ * (1 - Int.fract x)) * Int.fract x := by
        gcongr
    _ = _ := by ring

/-- Cubic decay of the interpolation remainder, uniformly on the whole line. -/
theorem tentInterpolant_remainder_decay (φ : SchwartzMap ℝ ℂ) (N : ℕ) (x : ℝ) :
    |x| ^ 3 * ‖φ x - tentInterpolant φ N x‖ ≤
      9 * SchwartzMap.seminorm ℝ 3 0 φ + 8 * SchwartzMap.seminorm ℝ 0 0 φ := by
  set B := SchwartzMap.seminorm ℝ 3 0 φ
  set K := SchwartzMap.seminorm ℝ 0 0 φ
  have hB (z : ℝ) : |z| ^ 3 * ‖φ z‖ ≤ B := by
    simpa using SchwartzMap.le_seminorm' ℝ 3 0 φ z
  have hK (z : ℝ) : ‖φ z‖ ≤ K := SchwartzMap.norm_le_seminorm ℝ φ z
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hB0 : 0 ≤ B := (mul_nonneg (by positivity) (norm_nonneg _)).trans (hB 0)
  have ht0 := Int.fract_nonneg x
  have ht1 := Int.fract_lt_one x
  have hg := tentInterpolant_norm_le (φ : ℝ → ℂ) N x
  have hx3 : 0 ≤ |x| ^ 3 := by positivity
  have hmain : |x| ^ 3 * ‖tentInterpolant φ N x‖ ≤ 8 * B + 8 * K := by
    by_cases hsmall : |x| ≤ 2
    · have hgK : ‖tentInterpolant φ N x‖ ≤ K := by
        refine hg.trans ?_
        nlinarith [hK ⌊x⌋, hK (⌊x⌋ + 1 : ℤ)]
      have : |x| ^ 3 ≤ 8 := by
        have := pow_le_pow_left₀ (abs_nonneg x) hsmall 3
        norm_num at this ⊢; linarith
      nlinarith [norm_nonneg (tentInterpolant φ N x)]
    · replace hsmall : 2 < |x| := lt_of_not_ge hsmall
      have hnode (j : ℤ) (hj : |x - j| ≤ 1) : |x| ^ 3 * ‖φ j‖ ≤ 8 * B := by
        have hjx : |x| / 2 ≤ |(j : ℝ)| := by
          have := abs_sub_abs_le_abs_sub x j
          linarith
        have hjpow : (|x| / 2) ^ 3 ≤ |(j : ℝ)| ^ 3 :=
          pow_le_pow_left₀ (by positivity) hjx 3
        have := hB j
        nlinarith [norm_nonneg (φ j)]
      have hk : |x - (⌊x⌋ : ℝ)| ≤ 1 := by
        rw [Int.self_sub_floor, abs_of_nonneg ht0]; linarith
      have hk1 : |x - ((⌊x⌋ + 1 : ℤ) : ℝ)| ≤ 1 := by
        push_cast
        rw [show x - ((⌊x⌋ : ℝ) + 1) = Int.fract x - 1 by rw [← Int.self_sub_floor]; ring,
          abs_of_neg (by linarith)]
        linarith
      have h1 := hnode ⌊x⌋ hk
      have h2 := hnode (⌊x⌋ + 1 : ℤ) hk1
      calc |x| ^ 3 * ‖tentInterpolant φ N x‖ ≤
          |x| ^ 3 * (‖φ ⌊x⌋‖ * (1 - Int.fract x) + ‖φ (⌊x⌋ + 1 : ℤ)‖ * Int.fract x) :=
            mul_le_mul_of_nonneg_left hg hx3
        _ = (|x| ^ 3 * ‖φ ⌊x⌋‖) * (1 - Int.fract x) +
            (|x| ^ 3 * ‖φ (⌊x⌋ + 1 : ℤ)‖) * Int.fract x := by ring
        _ ≤ (8 * B) * (1 - Int.fract x) + (8 * B) * Int.fract x := by
            gcongr
        _ = 8 * B := by ring
        _ ≤ 8 * B + 8 * K := by linarith
  calc |x| ^ 3 * ‖φ x - tentInterpolant φ N x‖ ≤
      |x| ^ 3 * ‖φ x‖ + |x| ^ 3 * ‖tentInterpolant φ N x‖ := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hx3
    _ ≤ B + (8 * B + 8 * K) := add_le_add (hB x) hmain
    _ = _ := by ring


/-! ## Quantitative Schwartz pairing bound and the controlled limit -/

/-- Explicit single-measure estimate behind HT2. For a near-gapped Fourier
self-dual off-lattice-nonnegative Jordan pair with common linear variation C,
every Schwartz pairing is controlled by the gap deficit, an interpolation
cost 2·Lip(φ)·d and a uniform cubic tail. Constants depend only on φ, C, N, d. -/
theorem nearGap_schwartz_pairing_bound (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth) (hself : nu.FourierSelfdual hnu)
    {a C : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hgap : hasNearGap nu a)
    (hoff : nu.OffLatticeNonnegative) (hC : CommonLinearMassBound C nu.totalVariation)
    (φ : SchwartzMap ℝ ℂ) {N : ℕ} (hN : 1 ≤ N) {d : ℝ} (hd : 0 < d) (hd2 : d ≤ 1 / 2) :
    ‖nu.distributionOfLinearGrowth hnu φ‖ ≤
      (1 - a) * (2 * C * ((2 * N + 3) * SchwartzMap.seminorm ℝ 0 0 φ)) +
      2 * schwartzLipConst φ * d * (C * (1 + N)) +
      2 * SchwartzMap.seminorm ℝ 0 0 φ *
        ((Real.pi ^ 2 * (N : ℝ) ^ 2 / (4 * d ^ 2)) * (1 - a) * (2 * C)) +
      4 * C * (9 * SchwartzMap.seminorm ℝ 3 0 φ + 8 * SchwartzMap.seminorm ℝ 0 0 φ) /
        (N : ℝ) ^ 2 := by
  set K := SchwartzMap.seminorm ℝ 0 0 φ with hKdef
  set B := SchwartzMap.seminorm ℝ 3 0 φ with hBdef
  set M := schwartzLipConst φ with hMdef
  set V := nu.totalVariation.real (Icc (-1) 1) with hVdef
  have hK (z : ℝ) : ‖φ z‖ ≤ K := SchwartzMap.norm_le_seminorm ℝ φ z
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hM0 : 0 ≤ M := by rw [hMdef]; unfold schwartzLipConst; exact apply_nonneg _ _
  have hC0 : 0 ≤ C := hC.1
  have hV : V ≤ 2 * C := by
    have h1 := hC.2 1 (by norm_num)
    rw [hVdef]; linarith
  have hV0 : 0 ≤ V := measureReal_nonneg
  have h1a : 0 ≤ 1 - a := by linarith
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  -- integrability
  have hφp : Integrable φ nu.positive := by
    let := (nu.parts_temperate_of_linear_growth hnu).1; exact φ.integrable
  have hφn : Integrable φ nu.negative := by
    let := (nu.parts_temperate_of_linear_growth hnu).2; exact φ.integrable
  set g := tentInterpolant (φ : ℝ → ℂ) N with hgdef
  have hgp : Integrable g nu.positive := tentInterpolant_integrable _ N _
  have hgn : Integrable g nu.negative := tentInterpolant_integrable _ N _
  set h : ℝ → ℂ := fun x => φ x - g x with hhdef
  have hhp : Integrable h nu.positive := hφp.sub hgp
  have hhn : Integrable h nu.negative := hφn.sub hgn
  have hsplit (μ : Measure ℝ) (hg' : Integrable g μ) (hh' : Integrable h μ) :
      (∫ x, φ x ∂μ) = (∫ x, g x ∂μ) + ∫ x, h x ∂μ := by
    rw [← integral_add hg' hh']
    congr 1
    funext x
    simp only [hhdef]
    ring
  rw [LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply,
    hsplit _ hgp hhp, hsplit _ hgn hhn]
  -- interpolant part
  have htri (j : ℤ) := nearGap_translated_triangle_bound nu hnu hself ha ha1 hgap hoff (j : ℝ)
  have hgpart : ‖(∫ x, g x ∂nu.positive) - ∫ x, g x ∂nu.negative‖ ≤
      (1 - a) * (2 * C * ((2 * N + 3) * K)) := by
    rw [hgdef, tentInterpolant_integral, tentInterpolant_integral, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ j ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1),
        ‖φ j * (((∫ x, unitTriangle (x - j) ∂nu.positive) : ℝ) : ℂ) -
          φ j * (((∫ x, unitTriangle (x - j) ∂nu.negative) : ℝ) : ℂ)‖ ≤ K * ((1 - a) * (2 * C)) := by
      intro j _
      rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hK j) ((htri j).trans (mul_le_mul_of_nonneg_left hV h1a))
        (abs_nonneg _) hK0
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
    have hcard : ((((N : ℤ) + 1 + 1 - (-(N : ℤ) - 1)).toNat : ℕ) : ℝ) = 2 * N + 3 := by
      have : ((N : ℤ) + 1 + 1 - (-(N : ℤ) - 1)) = ((2 * N + 3 : ℕ) : ℤ) := by push_cast; ring
      rw [this, Int.toNat_natCast]; push_cast; ring
    rw [hcard]
    nlinarith [mul_nonneg h1a hC0]
  -- split h into interior A = {|x| < N} and tail
  set A : Set ℝ := {x | |x| < N} with hAdef
  have hA : MeasurableSet A := measurableSet_lt continuous_abs.measurable measurable_const
  have hAc : Aᶜ = {x : ℝ | (N : ℝ) ≤ |x|} := by
    ext x; simp [hAdef, not_lt]
  have hAsub : A ⊆ Icc (-(N : ℝ)) N := by
    intro x hx
    have hx' : |x| < (N : ℝ) := hx
    have := abs_lt.mp hx'
    exact ⟨this.1.le, this.2.le⟩
  rw [← integral_add_compl hA hhp, ← integral_add_compl hA hhn]
  -- negative interior vanishes: negative mass sits on integers where h = 0
  have hneg_int : (∫ x in A, h x ∂nu.negative) = 0 := by
    apply integral_eq_zero_of_ae
    rw [EventuallyEq, ae_restrict_iff' hA]
    have hlat : ∀ᵐ x ∂nu.negative, x ∈ integerLattice := ae_iff.mpr (show nu.negative integerLatticeᶜ = 0 from hoff)
    filter_upwards [hlat] with x hx hxA
    obtain ⟨n, rfl⟩ := hx
    have herr := tentInterpolant_interior_error φ N (le_of_lt (show |((n : ℤ) : ℝ)| < (N : ℝ) from hxA))
    have hfr : Int.fract ((n : ℤ) : ℝ) = 0 := Int.fract_intCast n
    rw [hfr] at herr
    simp only [zero_mul, mul_zero, sub_zero] at herr
    simpa [hhdef] using norm_le_zero_iff.mp herr
  -- positive interior bound
  set E := signedBudgetRegion (N : ℝ) d with hEdef
  have hE : MeasurableSet E := signedBudgetRegion_measurable _ _
  have hmass := (near_gap_mass_bound nu hnu hself ha ha1 hgap hoff hNr hd hd2).2
  have hAfin : nu.positive A ≠ ∞ :=
    (measure_mono hAsub).trans_lt isCompact_Icc.measure_lt_top |>.ne
  have hpoint : ∀ x ∈ A, ‖h x‖ ≤ 2 * M * d + E.indicator (fun _ => 2 * K) x := by
    intro x hxA
    have hxN : |x| ≤ N := le_of_lt (show |x| < (N : ℝ) from hxA)
    by_cases hxE : x ∈ E
    · rw [indicator_of_mem hxE]
      have hg := tentInterpolant_norm_le (φ : ℝ → ℂ) N x
      have ht0 := Int.fract_nonneg x
      have ht1 := Int.fract_lt_one x
      have hgK : ‖g x‖ ≤ K := by
        refine hg.trans ?_
        nlinarith [hK ⌊x⌋, hK (⌊x⌋ + 1 : ℤ)]
      have : ‖h x‖ ≤ 2 * K := by
        simp only [hhdef]
        exact (norm_sub_le _ _).trans (by linarith [hK x])
      nlinarith [mul_nonneg hM0 hd.le]
    · rw [indicator_of_notMem hxE, add_zero]
      have hlt : Metric.infDist x integerLattice < d := by
        by_contra hge
        exact hxE ⟨hxN, le_of_not_gt hge⟩
      obtain ⟨y, ⟨n, rfl⟩, hdist⟩ :=
        (Metric.infDist_lt_iff (show integerLattice.Nonempty from ⟨(0 : ℝ), ⟨0, by simp⟩⟩)).mp hlt
      rw [Real.dist_eq] at hdist
      have hw := fract_mul_one_sub_le_abs_sub_int x n
      have herr := tentInterpolant_interior_error φ N hxN
      simp only [hhdef]
      calc ‖φ x - g x‖ ≤ 2 * M * (Int.fract x * (1 - Int.fract x)) := herr
        _ ≤ 2 * M * d := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            linarith
  have hpos_int : ‖∫ x in A, h x ∂nu.positive‖ ≤
      2 * M * d * (C * (1 + N)) +
        2 * K * ((Real.pi ^ 2 * (N : ℝ) ^ 2 / (4 * d ^ 2)) * (1 - a) * (2 * C)) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hint1 : IntegrableOn (fun x => ‖h x‖) A nu.positive := hhp.norm.integrableOn
    have hint2 : IntegrableOn (fun x => 2 * M * d + E.indicator (fun _ => 2 * K) x)
        A nu.positive := by
      refine (integrableOn_const (C := 2 * M * d) hAfin).add ?_
      exact ((integrableOn_const (C := 2 * K) hAfin).indicator hE)
    refine (setIntegral_mono_on hint1 hint2 hA hpoint).trans ?_
    rw [integral_add (integrableOn_const (C := 2 * M * d) hAfin)
        ((integrableOn_const (C := 2 * K) hAfin).indicator hE),
      setIntegral_const, setIntegral_indicator hE, setIntegral_const, smul_eq_mul, smul_eq_mul]
    have hAreal : nu.positive.real A ≤ C * (1 + N) := by
      have h1 : nu.positive.real A ≤ nu.positive.real (Icc (-(N : ℝ)) N) :=
        measureReal_mono hAsub isCompact_Icc.measure_lt_top.ne
      have h2 : nu.positive.real (Icc (-(N : ℝ)) N) ≤
          nu.totalVariation.real (Icc (-(N : ℝ)) N) := by
        apply ENNReal.toReal_mono isCompact_Icc.measure_lt_top.ne
        change nu.positive _ ≤ (nu.positive + nu.negative) _
        rw [Measure.add_apply]
        exact le_add_of_nonneg_right (by positivity)
      exact h1.trans (h2.trans (hC.2 N (by positivity)))
    have hAEreal : nu.positive.real (A ∩ E) ≤
        (Real.pi ^ 2 * (N : ℝ) ^ 2 / (4 * d ^ 2)) * (1 - a) * (2 * C) := by
      have h1 : nu.positive.real (A ∩ E) ≤ nu.positive.real E :=
        measureReal_mono inter_subset_right (signedBudgetRegion_finite nu.positive _ _).ne
      refine h1.trans (hmass.trans ?_)
      have hcoef : 0 ≤ Real.pi ^ 2 * (N : ℝ) ^ 2 / (4 * d ^ 2) * (1 - a) := by positivity
      exact mul_le_mul_of_nonneg_left hV hcoef
    have hMd : 0 ≤ 2 * M * d := by positivity
    nlinarith [measureReal_nonneg (μ := nu.positive) (s := A),
      measureReal_nonneg (μ := nu.positive) (s := A ∩ E)]
  -- tail
  have htail : ‖(∫ x in Aᶜ, h x ∂nu.positive) - ∫ x in Aᶜ, h x ∂nu.negative‖ ≤
      4 * C * (9 * B + 8 * K) / (N : ℝ) ^ 2 := by
    have hhc : Continuous h := φ.continuous.sub (tentInterpolant_continuous _ N)
    have hdec := tentInterpolant_remainder_decay φ N
    have ht := common_linear_cubic_tail nu.totalVariation C (9 * B + 8 * K) N hC
      (by positivity) hNr h hhc hdec
    rw [← hAc] at ht
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_integral_le_integral_norm _) (norm_integral_le_integral_norm _)).trans ?_
    have hsum : (∫ x in Aᶜ, ‖h x‖ ∂nu.positive) + (∫ x in Aᶜ, ‖h x‖ ∂nu.negative) =
        ∫ x in Aᶜ, ‖h x‖ ∂nu.totalVariation := by
      rw [LocallyFiniteSignedMeasure.totalVariation, Measure.restrict_add,
        integral_add_measure hhp.norm.integrableOn hhn.norm.integrableOn]
    rw [hsum]
    simpa only [show (4 : ℝ) * C * (9 * B + 8 * K) / (N : ℝ) ^ 2 =
      4 * C * (9 * B + 8 * K) / (N : ℝ) ^ 2 from rfl] using ht.2
  -- assemble
  rw [hneg_int, zero_add]
  calc ‖(∫ x, g x ∂nu.positive) + ((∫ x in A, h x ∂nu.positive) + ∫ x in Aᶜ, h x ∂nu.positive) -
        ((∫ x, g x ∂nu.negative) + ∫ x in Aᶜ, h x ∂nu.negative)‖ =
      ‖((∫ x, g x ∂nu.positive) - ∫ x, g x ∂nu.negative) + (∫ x in A, h x ∂nu.positive) +
        ((∫ x in Aᶜ, h x ∂nu.positive) - ∫ x in Aᶜ, h x ∂nu.negative)‖ := by
          congr 1; ring
    _ ≤ ‖(∫ x, g x ∂nu.positive) - ∫ x, g x ∂nu.negative‖ + ‖∫ x in A, h x ∂nu.positive‖ +
        ‖(∫ x in Aᶜ, h x ∂nu.positive) - ∫ x in Aᶜ, h x ∂nu.negative‖ :=
          norm_add₃_le
    _ ≤ _ := by linarith [hgpart, hpos_int, htail]


/-- Original R1-HT2 controlled limit. Real locally finite Jordan pairs with one
common linear total-variation constant, Fourier self-duality, off-lattice
nonnegativity and gaps a_n → 1 converge to zero on every Schwartz test.
No total-variation convergence, limiting measure or evenness premise is used:
the proof is a quantitative estimate (`nearGap_schwartz_pairing_bound`) built
from translated sinc/triangle identities, integer tent interpolation and the
uniform cubic Schwartz tail of the common growth budget. -/
theorem near_gap_controlled_limit_zero
    (nu : ℕ → LocallyFiniteSignedMeasure) (C : ℝ)
    (hC : ∀ n, CommonLinearMassBound C (nu n).totalVariation)
    (hself : ∀ n, (nu n).FourierSelfdual (hC n).linearGrowth)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n ≤ 1)
    (hgap : ∀ n, hasNearGap (nu n) (a n))
    (hoff : ∀ n, (nu n).OffLatticeNonnegative)
    (hlim : Tendsto a atTop (𝓝 1)) (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun n => (nu n).distributionOfLinearGrowth (hC n).linearGrowth φ)
      atTop (𝓝 0) := by
  set K := SchwartzMap.seminorm ℝ 0 0 φ with hKdef
  set B := SchwartzMap.seminorm ℝ 3 0 φ with hBdef
  set M := schwartzLipConst φ with hMdef
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (SchwartzMap.norm_le_seminorm ℝ φ 0)
  have hB0 : 0 ≤ B := by
    have := SchwartzMap.le_seminorm' ℝ 3 0 φ 0
    exact (mul_nonneg (by positivity) (norm_nonneg _)).trans this
  have hM0 : 0 ≤ M := by rw [hMdef]; unfold schwartzLipConst; exact apply_nonneg _ _
  have hC0 : 0 ≤ C := (hC 0).1
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- tail scale
  obtain ⟨N0, hN0⟩ := exists_nat_gt (12 * C * (9 * B + 8 * K) / ε + 1)
  set N : ℕ := N0 with hNdef
  have hNr : (1 : ℝ) < N := by
    have : 0 ≤ 12 * C * (9 * B + 8 * K) / ε := by positivity
    linarith
  have hN : 1 ≤ N := by exact_mod_cast hNr.le
  have htail : 4 * C * (9 * B + 8 * K) / (N : ℝ) ^ 2 < ε / 3 := by
    have hNpos : (0 : ℝ) < N := by linarith
    have hsq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hT : 0 ≤ 4 * C * (9 * B + 8 * K) := by positivity
    calc 4 * C * (9 * B + 8 * K) / (N : ℝ) ^ 2 ≤ 4 * C * (9 * B + 8 * K) / (N : ℝ) :=
          div_le_div_of_nonneg_left hT hNpos hsq
      _ < ε / 3 := by
          rw [div_lt_iff₀ hNpos]
          have h12 : 12 * C * (9 * B + 8 * K) / ε < N := by linarith
          rw [div_lt_iff₀ hε] at h12
          nlinarith
  -- interpolation scale
  set Lc : ℝ := M * (C * (1 + N)) with hLc
  have hLc0 : 0 ≤ Lc := by positivity
  set d : ℝ := min (1 / 2) (ε / (6 * (Lc + 1))) with hddef
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  have hd2 : d ≤ 1 / 2 := min_le_left _ _
  have hd3 : d ≤ ε / (6 * (Lc + 1)) := min_le_right _ _
  have hinterp : 2 * M * d * (C * (1 + N)) < ε / 3 := by
    have : 2 * M * d * (C * (1 + N)) = 2 * Lc * d := by rw [hLc]; ring
    rw [this]
    have h1 : 2 * Lc * d ≤ 2 * Lc * (ε / (6 * (Lc + 1))) :=
      mul_le_mul_of_nonneg_left hd3 (by positivity)
    have h2 : 2 * Lc * (ε / (6 * (Lc + 1))) < ε / 3 := by
      rw [show 2 * Lc * (ε / (6 * (Lc + 1))) = (ε / 3) * (Lc / (Lc + 1)) by
        field_simp; ring]
      have : Lc / (Lc + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      nlinarith
    linarith
  -- gap-deficit coefficient
  set Q : ℝ := 2 * C * ((2 * N + 3) * K) +
    2 * K * ((Real.pi ^ 2 * (N : ℝ) ^ 2 / (4 * d ^ 2)) * (2 * C)) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp hlim (ε / (3 * (Q + 1))) (by positivity)
  refine ⟨N1, fun n hn => ?_⟩
  have hdist := hN1 n hn
  rw [Real.dist_eq] at hdist
  have hdef : 0 ≤ 1 - a n := by linarith [ha1 n]
  have hgapdef : 1 - a n < ε / (3 * (Q + 1)) := by
    have := abs_lt.mp hdist
    linarith [this.1]
  have hbound := nearGap_schwartz_pairing_bound (nu n) (hC n).linearGrowth (hself n)
    (ha n) (ha1 n) (hgap n) (hoff n) (hC n) φ hN hd hd2
  rw [dist_zero_right]
  have hdeficit : (1 - a n) * (2 * C * ((2 * N + 3) * K)) +
      2 * K * ((Real.pi ^ 2 * (N : ℝ) ^ 2 / (4 * d ^ 2)) * (1 - a n) * (2 * C)) =
      (1 - a n) * Q := by rw [hQ]; ring
  have hQbound : (1 - a n) * Q < ε / 3 := by
    have h1 : (1 - a n) * Q ≤ (ε / (3 * (Q + 1))) * Q :=
      mul_le_mul_of_nonneg_right hgapdef.le hQ0
    have h2 : (ε / (3 * (Q + 1))) * Q < ε / 3 := by
      rw [show (ε / (3 * (Q + 1))) * Q = (ε / 3) * (Q / (Q + 1)) by field_simp]
      have : Q / (Q + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      nlinarith
    linarith
  linarith [hbound, hdeficit, hQbound, hinterp, htail]

/-- Actual-domain instance of the HT2 controlled limit: the genuine CT1 dilation
family along any parameters L_n → 0 with 0 < L_n < log 2 (gaps exp(-L_n) → 1,
common variation constant 18) tends to zero on every Schwartz test. -/
theorem nearGapCombFamily_controlled_limit (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (hu : ∀ n, L n < Real.log 2) (hlim : Tendsto L atTop (𝓝 0))
    (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun n => nearGapCombDistribution (L n) φ) atTop (𝓝 0) := by
  have hC : ∀ n, CommonLinearMassBound 18 (nearGapCombFamily (L n)).totalVariation :=
    fun n => nearGapCombFamily_common_growth (hL n).le (hu n).le
  have ha : Tendsto (fun n => Real.exp (-L n)) atTop (𝓝 1) := by
    have hneg : Tendsto (fun n => -L n) atTop (𝓝 0) := by simpa using hlim.neg
    have := (Real.continuous_exp.tendsto 0).comp hneg
    simpa [Function.comp_def] using this
  have h := near_gap_controlled_limit_zero (fun n => nearGapCombFamily (L n)) 18 hC
    (fun n => nearGapCombFamily_fourier_selfdual (L n))
    (fun n => Real.exp (-L n)) (fun n => Real.exp_pos _)
    (fun n => (nearGapComb_radius_bounds (hL n) (hu n)).2.le)
    (fun n => nearGapCombFamily_actual_gap (hL n).le)
    (fun n => nearGapCombFamily_offlattice_nonnegative (L n)) ha φ
  exact h

#print axioms Zeta23.OPICAFollowup.near_gap_mass_bound
#print axioms Zeta23.OPICAFollowup.near_gap_controlled_limit_zero
end Zeta23.OPICAFollowup
