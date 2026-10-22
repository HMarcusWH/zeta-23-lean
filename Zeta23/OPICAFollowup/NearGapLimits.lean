import Zeta23.OPICAFollowup.DilatedComb
import Zeta23.OPICA.SignedHeatSeparator

/-! Actual near-gap Jordan-measure budget. The controlled weak-limit theorem,
explicit nonzero dilation family and normalized nonmeasure limit remain OPEN. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology FourierTransform SchwartzMap
namespace Zeta23.OPICAFollowup
open Zeta23.OPICA

def hasNearGap (nu : LocallyFiniteSignedMeasure) (a : ℝ) : Prop :=
  nu.positive (Ioo (-a) a)=0 ∧ nu.negative (Ioo (-a) a)=0

/-- The actual canonical Jordan carrier for the CT1 auxiliary dilation defect.
It represents D_L + D_(-L) - 2 cosh(L/2) D_0.  Canonicalization is
necessary: scaled lattice supports can meet the integer lattice, so the
uncancelled positive/negative measures need not be mutually singular.
The nonzero, gap, self-duality and normalized-limit roots are still OPEN. -/
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
  simp only [neg_smul, sub_eq_add_neg]

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
  exact h.trans (nearGapComb_origin_coefficient_zero L)

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
  have hset : K ∩ ({0} : Set ℝ) = ({0} : Set ℝ) := by
    ext x
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · exact And.right
    · intro hx
      subst x
      exact ⟨h0, rfl⟩
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
      exact measure_mono_null inter_subset_right hz
    simp [dilatedCombJordan, localJordanDifference, hrestricted]
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
  simpa [E] using (le_antisymm (by simpa using hbound) (zero_le _))

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
      · exact zero_le _
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
  exact Measure.sub_le _ _

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
    exact le_add_of_nonneg_left (zero_le _)
  exact le_antisymm (hnegative.trans hvar) (zero_le _)

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
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro n hn
    apply hn
    exact ⟨n, by simp [scaledLatticePoint]⟩
  rw [hpre]
  simp

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
  rw [hplus, Measure.zero_apply, hminus, zero_add] at hbound
  exact le_antisymm hbound (zero_le _)

/-- Physical off-lattice nonnegativity of the genuine CT1 canonical
Jordan pair, for every real dilation parameter. -/
theorem nearGapCombFamily_offlattice_nonnegative (L : ℝ) :
    (nearGapCombFamily L).OffLatticeNonnegative :=
  nearGapCombFamily_negative_integer_support L

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
    letI := (mu.parts_temperate_of_linear_growth hmu).1
    exact f.integrable
  have hmm : Integrable f mu.negative := by
    letI := (mu.parts_temperate_of_linear_growth hmu).2
    exact f.integrable
  have hnp : Integrable f nu.positive := by
    letI := (nu.parts_temperate_of_linear_growth hnu).1
    exact f.integrable
  have hnm : Integrable f nu.negative := by
    letI := (nu.parts_temperate_of_linear_growth hnu).2
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
  refine ⟨|a|*A,mul_nonneg (abs_nonneg _) hA,fun R hR => ?_⟩
  have hle := localJordanScale_totalVariation_le a mu (Icc (-R) R)
  rw [Measure.smul_apply,smul_eq_mul] at hle
  have hfin : ENNReal.ofReal |a|*mu.totalVariation (Icc (-R) R) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top isCompact_Icc.measure_lt_top.ne
  have hh := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _)] at hh
  have ha := hAb R hR
  change (mu.totalVariation (Icc (-R) R)).toReal ≤ _ at ha
  change ((localJordanScale a mu).totalVariation (Icc (-R) R)).toReal ≤ _
  nlinarith

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

#print axioms Zeta23.OPICAFollowup.near_gap_mass_bound
end Zeta23.OPICAFollowup
