import Zeta23.OPICA.LocalData
import Mathlib.Topology.Germ
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Localization.FractionRing

/-! The local ring below consists of actual analytic germs, with equality
given by equality on a neighborhood.  It is not the meromorphic fraction
field. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Zeta23.OPICA

def analyticGermRing (center : ℂ) : Subring (Germ (𝓝 center) ℂ) where
  carrier := {g | ∃ f : ℂ → ℂ, AnalyticAt ℂ f center ∧ (f : Germ (𝓝 center) ℂ) = g}
  zero_mem' := ⟨fun _ => 0, analyticAt_const, rfl⟩
  one_mem' := ⟨fun _ => 1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨fun z => f z + g z, hf.add hg, rfl⟩
  mul_mem' := by
    rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨fun z => f z * g z, hf.mul hg, rfl⟩
  neg_mem' := by
    rintro a ⟨f, hf, rfl⟩
    exact ⟨fun z => -f z, hf.neg, rfl⟩

abbrev HolomorphicGerm (center : ℂ) := analyticGermRing center

def holomorphicGermOf (center : ℂ) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f center) :
    HolomorphicGerm center := ⟨(f : Germ (𝓝 center) ℂ), f, hf, rfl⟩

theorem holomorphicGermOf_eq_iff (center : ℂ) (f g : ℂ → ℂ)
    (hf : AnalyticAt ℂ f center) (hg : AnalyticAt ℂ g center) :
    holomorphicGermOf center f hf = holomorphicGermOf center g hg ↔ f =ᶠ[𝓝 center] g := by
  exact Subtype.ext_iff.trans Germ.coe_eq

def coordinateGerm (center : ℂ) : HolomorphicGerm center :=
  holomorphicGermOf center (fun z => z - center) (by fun_prop)

theorem holomorphicGermOf_isUnit (center : ℂ) (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f center) (hne : f center ≠ 0) :
    IsUnit (holomorphicGermOf center f hf) := by
  let g := holomorphicGermOf center (fun z => (f z)⁻¹) (hf.inv hne)
  have hfg : holomorphicGermOf center f hf * g = 1 := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    filter_upwards [hf.continuousAt.eventually_ne hne] with z hz
    exact mul_inv_cancel₀ hz
  exact isUnit_iff_exists_inv.mpr ⟨g, hfg⟩

theorem zero_ideal_eq_coordinate_power (center : ℂ)
    (m : MultiplierOrderData center) :
    Ideal.span ({holomorphicGermOf center m.multiplier (multiplier_analytic m)} :
      Set (HolomorphicGerm center)) =
      Ideal.span ({coordinateGerm center ^ m.order} : Set (HolomorphicGerm center)) := by
  have heq : holomorphicGermOf center m.multiplier (multiplier_analytic m) =
      coordinateGerm center ^ m.order * holomorphicGermOf center m.unit m.unit_analytic := by
    apply Subtype.ext
    exact Germ.coe_eq.mpr m.multiplier_eq
  rw [heq]
  exact Ideal.span_singleton_mul_right_unit
    (holomorphicGermOf_isUnit center m.unit m.unit_analytic m.unit_ne_zero) _

/-- Taylor coordinates give actual analytic representatives modulo a
coordinate power. This is the normal-form input to the quotient theorem. -/
theorem analytic_taylor_normal_form (center : ℂ) (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f center) (n : ℕ) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h center ∧
      ∀ᶠ z in 𝓝 center,
        f z = (∑ i ∈ Finset.range n,
          ((z - center) ^ i / (i.factorial : ℂ)) * iteratedDeriv i f center) +
          (z - center) ^ n * h z := by
  have hf0 : AnalyticAt ℂ (fun w : ℂ => f (w + center)) 0 := by
    have hf' : AnalyticAt ℂ f (0 + center) := by simpa using hf
    exact hf'.comp (f := fun w : ℂ => w + center) (x := 0) (by fun_prop)
  obtain ⟨h, hh, hTaylor⟩ := hf0.exists_eventuallyEq_sum_add_pow_mul n
  have hsub : Tendsto (fun z : ℂ => z - center) (𝓝 center) (𝓝 0) := by
    have hc : ContinuousAt (fun z : ℂ => z - center) center := by fun_prop
    simpa only [sub_self] using hc.tendsto
  refine ⟨fun z => h (z - center), ?_, ?_⟩
  · have hh' : AnalyticAt ℂ h (center - center) := by simpa using hh
    exact hh'.comp (f := fun z : ℂ => z - center) (x := center) (by fun_prop)
  · have hder (i : ℕ) : iteratedDeriv i (fun w : ℂ => f (w + center)) 0 =
        iteratedDeriv i f center := by
      simpa using congrFun (iteratedDeriv_comp_add_const i f center) 0
    filter_upwards [hsub.eventually hTaylor] with z hz
    simpa only [sub_add_cancel, hder, smul_eq_mul] using hz

def localTaylorPolynomial (center : ℂ) (f : ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  fun z => ∑ i ∈ Finset.range n,
    ((z - center) ^ i / (i.factorial : ℂ)) * iteratedDeriv i f center

theorem localTaylorPolynomial_analytic (center : ℂ) (f : ℂ → ℂ) (n : ℕ) :
    AnalyticAt ℂ (localTaylorPolynomial center f n) center := by
  exact Finset.analyticAt_fun_sum _ (fun i hi => by fun_prop)

theorem taylor_remainder_in_coordinate_ideal (center : ℂ) (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f center) (n : ℕ) :
    holomorphicGermOf center f hf -
      holomorphicGermOf center (localTaylorPolynomial center f n)
        (localTaylorPolynomial_analytic center f n) ∈
      Ideal.span ({coordinateGerm center ^ n} : Set (HolomorphicGerm center)) := by
  obtain ⟨h, hh, heq⟩ := analytic_taylor_normal_form center f hf n
  apply Ideal.mem_span_singleton.mpr
  refine ⟨holomorphicGermOf center h hh, ?_⟩
  apply Subtype.ext
  apply Germ.coe_eq.mpr
  filter_upwards [heq] with z hz
  dsimp [coordinateGerm, holomorphicGermOf, localTaylorPolynomial]
  linear_combination hz

theorem coordinate_ideal_iff_lower_jets_zero (center : ℂ) (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f center) (n : ℕ) :
    holomorphicGermOf center f hf ∈
      Ideal.span ({coordinateGerm center ^ n} : Set (HolomorphicGerm center)) ↔
      ∀ j < n, iteratedDeriv j f center = 0 := by
  rw [← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
  constructor
  · intro hmem
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hmem
    obtain ⟨h, hh, hhg⟩ := g.property
    have hgg : g = holomorphicGermOf center h hh := Subtype.ext hhg.symm
    rw [hgg] at hg
    apply (natCast_le_analyticOrderAt hf).mpr
    refine ⟨h, hh, ?_⟩
    have heq : ((fun z => (z - center) ^ n * h z) : Germ (𝓝 center) ℂ) =
        (f : Germ (𝓝 center) ℂ) := (congrArg Subtype.val hg).symm
    filter_upwards [Germ.coe_eq.mp heq] with z hz
    simpa only [smul_eq_mul] using hz.symm
  · intro horder
    obtain ⟨h, hh, hfg⟩ := (natCast_le_analyticOrderAt hf).mp horder
    apply Ideal.mem_span_singleton.mpr
    refine ⟨holomorphicGermOf center h hh, ?_⟩
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    filter_upwards [hfg] with z hz
    simpa only [smul_eq_mul, Function.comp_def] using hz

theorem polynomial_eval_center_analytic (center : ℂ) (p : Polynomial ℂ) :
    AnalyticAt ℂ (fun z => p.eval (z - center)) center := by
  have heq : (fun z : ℂ => p.eval (z - center)) =
      fun z => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (z - center) ^ i := by
    funext z
    exact Polynomial.eval_eq_sum_range _
  rw [heq]
  exact Finset.analyticAt_fun_sum _ (fun i hi => by fun_prop)

def polynomialGerm (center : ℂ) : Polynomial ℂ →+* HolomorphicGerm center where
  toFun p := holomorphicGermOf center (fun z => p.eval (z - center))
    (polynomial_eval_center_analytic center p)
  map_zero' := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun z => by simp)
  map_one' := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun z => by simp)
  map_add' p q := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun z => by simp)
  map_mul' p q := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun z => by simp)

theorem polynomialGerm_X (center : ℂ) :
    polynomialGerm center Polynomial.X = coordinateGerm center := by
  apply Subtype.ext
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall (fun z => by simp)

def coordinatePowerIdeal (center : ℂ) (n : ℕ) : Ideal (HolomorphicGerm center) :=
  Ideal.span {coordinateGerm center ^ n}

def polynomialGermQuotient (center : ℂ) (n : ℕ) :
    Polynomial ℂ →+* (HolomorphicGerm center ⧸ coordinatePowerIdeal center n) :=
  (Ideal.Quotient.mk (coordinatePowerIdeal center n)).comp (polynomialGerm center)

theorem polynomial_iteratedDeriv_zero (p : Polynomial ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => p.eval z) 0 = (n.factorial : ℂ) * p.coeff n := by
  have hder (q : Polynomial ℂ) : deriv (fun z => q.eval z) = fun z => q.derivative.eval z := by
    funext z
    exact q.deriv
  have hiter (q : Polynomial ℂ) (k : ℕ) :
      iteratedDeriv k (fun z => q.eval z) = fun z => (Polynomial.derivative^[k] q).eval z := by
    induction k generalizing q with
    | zero => rfl
    | succ k ih =>
      simp only [iteratedDeriv_succ', hder, ih, Function.iterate_succ_apply]
  rw [hiter]
  change (Polynomial.derivative^[n] p).eval 0 = _
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self, nsmul_eq_mul]

theorem polynomialGermQuotient_kernel (center : ℂ) (n : ℕ) :
    RingHom.ker (polynomialGermQuotient center n) =
      Ideal.span ({Polynomial.X ^ n} : Set (Polynomial ℂ)) := by
  ext p
  change Ideal.Quotient.mk (coordinatePowerIdeal center n) (polynomialGerm center p) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change holomorphicGermOf center (fun z => p.eval (z - center))
      (polynomial_eval_center_analytic center p) ∈
      Ideal.span ({coordinateGerm center ^ n} : Set (HolomorphicGerm center)) ↔ _
  rw [coordinate_ideal_iff_lower_jets_zero, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
  have hjet (j : ℕ) : iteratedDeriv j (fun z => p.eval (z - center)) center =
      (j.factorial : ℂ) * p.coeff j := by
    have h := congrFun (iteratedDeriv_comp_sub_const j (fun z => p.eval z) center) center
    simpa only [sub_self, polynomial_iteratedDeriv_zero] using h
  simp only [hjet, mul_eq_zero]
  simp [Nat.factorial_ne_zero]

theorem polynomialGermQuotient_surjective (center : ℂ) (n : ℕ) :
    Function.Surjective (polynomialGermQuotient center n) := by
  intro y
  refine Quotient.inductionOn' y (fun g => ?_)
  obtain ⟨f, hf, hfg⟩ := g.property
  have hg : g = holomorphicGermOf center f hf := Subtype.ext hfg.symm
  let p : Polynomial ℂ := ∑ i ∈ Finset.range n,
    Polynomial.C (iteratedDeriv i f center / (i.factorial : ℂ)) * Polynomial.X ^ i
  refine ⟨p, ?_⟩
  have hp : polynomialGerm center p =
      holomorphicGermOf center (localTaylorPolynomial center f n)
        (localTaylorPolynomial_analytic center f n) := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    apply Filter.Eventually.of_forall
    intro z
    change p.eval (z - center) = localTaylorPolynomial center f n z
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, localTaylorPolynomial]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change Ideal.Quotient.mk (coordinatePowerIdeal center n) (polynomialGerm center p) =
    Ideal.Quotient.mk (coordinatePowerIdeal center n) g
  rw [hp, hg, Ideal.Quotient.eq]
  have hm := (coordinatePowerIdeal center n).neg_mem
    (taylor_remainder_in_coordinate_ideal center f hf n)
  simpa only [neg_sub] using hm

theorem truncated_taylor_quotient_equiv (center : ℂ) (m : MultiplierOrderData center) :
    ∃ e : (HolomorphicGerm center ⧸
        Ideal.span ({holomorphicGermOf center m.multiplier (multiplier_analytic m)} :
          Set (HolomorphicGerm center))) ≃+*
      (Polynomial ℂ ⧸ Ideal.span ({Polynomial.X ^ m.order} : Set (Polynomial ℂ))),
      ∀ p : Polynomial ℂ,
        e (Ideal.Quotient.mk _ (polynomialGerm center p)) = Ideal.Quotient.mk _ p := by
  let F := polynomialGermQuotient center m.order
  have hsurj : Function.Surjective F := polynomialGermQuotient_surjective center m.order
  have hker := polynomialGermQuotient_kernel center m.order
  let e := (Ideal.quotEquivOfEq (zero_ideal_eq_coordinate_power center m)).trans
    ((F.quotientKerEquivOfSurjective hsurj).symm.trans (Ideal.quotEquivOfEq hker))
  refine ⟨e, ?_⟩
  intro p
  change (Ideal.quotEquivOfEq hker) ((F.quotientKerEquivOfSurjective hsurj).symm (F p)) = _
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.quotEquivOfEq_mk]

theorem holomorphicGermOf_eq_zero_iff (center : ℂ) (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f center) :
    holomorphicGermOf center f hf = 0 ↔ f =ᶠ[𝓝 center] 0 := by
  constructor
  · intro h
    exact Germ.coe_eq.mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (Germ.coe_eq.mpr h)

instance holomorphicGerm_nontrivial (center : ℂ) : Nontrivial (HolomorphicGerm center) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have hval := congrArg (fun g : HolomorphicGerm center => Germ.value g.val) h
  change (0 : ℂ) = 1 at hval
  exact zero_ne_one hval

instance holomorphicGerm_noZeroDivisors (center : ℂ) : NoZeroDivisors (HolomorphicGerm center) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    obtain ⟨f, hf, hfa⟩ := a.property
    obtain ⟨g, hg, hgb⟩ := b.property
    have ha : holomorphicGermOf center f hf = a := Subtype.ext hfa
    have hb : holomorphicGermOf center g hg = b := Subtype.ext hgb
    rw [← ha, ← hb] at hab
    have hzero : (f * g) =ᶠ[𝓝 center] 0 :=
      (holomorphicGermOf_eq_zero_iff center (f * g) (hf.mul hg)).mp hab
    have horder : analyticOrderAt f center + analyticOrderAt g center = ⊤ := by
      rw [← analyticOrderAt_mul hf hg]
      exact analyticOrderAt_eq_top.mpr hzero
    rcases ENat.add_eq_top.mp horder with htop | htop
    · left
      rw [← ha]
      exact (holomorphicGermOf_eq_zero_iff center f hf).mpr (analyticOrderAt_eq_top.mp htop)
    · right
      rw [← hb]
      exact (holomorphicGermOf_eq_zero_iff center g hg).mpr (analyticOrderAt_eq_top.mp htop)

instance holomorphicGerm_isDomain (center : ℂ) : IsDomain (HolomorphicGerm center) :=
  NoZeroDivisors.to_isDomain (HolomorphicGerm center)

/-- The meromorphic germ field is the fraction field of the actual local
analytic ring, rather than the ring of arbitrary functions on a punctured set. -/
abbrev MeromorphicGerm (center : ℂ) := FractionRing (HolomorphicGerm center)

theorem coordinateGerm_ne_zero (center : ℂ) : coordinateGerm center ≠ 0 := by
  intro hzero
  have ht : analyticOrderAt (fun z : ℂ => z - center) center = ⊤ :=
    analyticOrderAt_eq_top.mpr
      ((holomorphicGermOf_eq_zero_iff center (fun z => z - center)
        (by fun_prop)).mp hzero)
  have ho : analyticOrderAt (fun z : ℂ => z - center) center = (1 : ℕ∞) :=
    (analyticAt_id.sub analyticAt_const).analyticOrderAt_eq_natCast.mpr
      ⟨fun _ => 1, analyticAt_const, one_ne_zero, by simp⟩
  rw [ho] at ht
  norm_num at ht

def meromorphicCoordinate (center : ℂ) : MeromorphicGerm center :=
  algebraMap (HolomorphicGerm center) (MeromorphicGerm center) (coordinateGerm center)

theorem meromorphicCoordinate_ne_zero (center : ℂ) : meromorphicCoordinate center ≠ 0 := by
  intro h
  apply coordinateGerm_ne_zero center
  apply IsFractionRing.injective (HolomorphicGerm center) (MeromorphicGerm center)
  simpa only [meromorphicCoordinate, map_zero] using h

def meromorphicPrincipalSpan (center : ℂ) (v : MeromorphicGerm center) :
    Submodule (HolomorphicGerm center) (MeromorphicGerm center) :=
  Submodule.span (HolomorphicGerm center) {v}

def meromorphicSpanLinearMap (center : ℂ) (v : MeromorphicGerm center) :
    HolomorphicGerm center →ₗ[HolomorphicGerm center] meromorphicPrincipalSpan center v where
  toFun a := ⟨a • v, Submodule.smul_mem _ a (Submodule.subset_span (by simp))⟩
  map_add' a b := by apply Subtype.ext; exact add_smul a b v
  map_smul' a b := by apply Subtype.ext; exact mul_smul a b v

def meromorphicSpanEquiv (center : ℂ) (v : MeromorphicGerm center) (hv : v ≠ 0) :
    HolomorphicGerm center ≃ₗ[HolomorphicGerm center] meromorphicPrincipalSpan center v :=
  LinearEquiv.ofBijective (meromorphicSpanLinearMap center v) (by
    constructor
    · intro a b hab
      have hm : algebraMap (HolomorphicGerm center) (MeromorphicGerm center) a * v =
          algebraMap (HolomorphicGerm center) (MeromorphicGerm center) b * v := by
        have hval := congrArg Subtype.val hab
        change a • v = b • v at hval
        simpa only [Algebra.smul_def] using hval
      exact IsFractionRing.injective (HolomorphicGerm center) (MeromorphicGerm center)
        (mul_right_cancel₀ hv hm)
    · intro y
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp y.property
      exact ⟨a, Subtype.ext ha⟩)

def coordinateModuleIdeal (center : ℂ) : Submodule (HolomorphicGerm center) (HolomorphicGerm center) :=
  Submodule.span (HolomorphicGerm center) {coordinateGerm center}

def meromorphicPrincipalBackground (center : ℂ) (v : MeromorphicGerm center) (hv : v ≠ 0) :
    Submodule (HolomorphicGerm center) (meromorphicPrincipalSpan center v) :=
  (coordinateModuleIdeal center).map (meromorphicSpanEquiv center v hv).toLinearMap

theorem meromorphicPrincipalBackground_ambient (center : ℂ)
    (v : MeromorphicGerm center) (hv : v ≠ 0) :
    (meromorphicPrincipalBackground center v hv).map
      (meromorphicPrincipalSpan center v).subtype =
      meromorphicPrincipalSpan center (meromorphicCoordinate center * v) := by
  change ((Submodule.span (HolomorphicGerm center) {coordinateGerm center}).map
    (meromorphicSpanEquiv center v hv).toLinearMap).map _ = _
  rw [← Submodule.map_comp, Submodule.map_span, Set.image_singleton]
  apply congrArg (fun q : MeromorphicGerm center =>
    Submodule.span (HolomorphicGerm center) ({q} : Set (MeromorphicGerm center)))
  change (coordinateGerm center) • v = meromorphicCoordinate center * v
  exact Algebra.smul_def _ _

def meromorphicPrincipalQuotientEquiv (center : ℂ) (v : MeromorphicGerm center) (hv : v ≠ 0) :
    (HolomorphicGerm center ⧸ coordinateModuleIdeal center) ≃ₗ[HolomorphicGerm center]
      (meromorphicPrincipalSpan center v ⧸ meromorphicPrincipalBackground center v hv) :=
  Submodule.Quotient.equiv _ _ (meromorphicSpanEquiv center v hv) rfl

abbrev LocalPoleCarrier (center : ℂ) :=
  meromorphicPrincipalSpan center (meromorphicCoordinate center)⁻¹

def LocalPoleBackground (center : ℂ) : Submodule (HolomorphicGerm center) (LocalPoleCarrier center) :=
  meromorphicPrincipalBackground center (meromorphicCoordinate center)⁻¹
    (inv_ne_zero (meromorphicCoordinate_ne_zero center))

theorem localPoleBackground_is_holomorphic (center : ℂ) :
    (LocalPoleBackground center).map (LocalPoleCarrier center).subtype =
      meromorphicPrincipalSpan center 1 := by
  rw [LocalPoleBackground, meromorphicPrincipalBackground_ambient]
  rw [mul_inv_cancel₀ (meromorphicCoordinate_ne_zero center)]

abbrev LocalCompletedCarrier (center : ℂ) (k : ℕ) :=
  meromorphicPrincipalSpan center (meromorphicCoordinate center ^ (k - 1))

def LocalCompletedBackground (center : ℂ) (k : ℕ) :
    Submodule (HolomorphicGerm center) (LocalCompletedCarrier center k) :=
  meromorphicPrincipalBackground center (meromorphicCoordinate center ^ (k - 1))
    (pow_ne_zero _ (meromorphicCoordinate_ne_zero center))

theorem localCompletedBackground_is_coordinate_power (center : ℂ) (k : ℕ) (hk : 0 < k) :
    (LocalCompletedBackground center k).map (LocalCompletedCarrier center k).subtype =
      meromorphicPrincipalSpan center (meromorphicCoordinate center ^ k) := by
  rw [LocalCompletedBackground, meromorphicPrincipalBackground_ambient, ← pow_succ']
  congr 2
  omega

def localUnitMulEquiv {R : Type*} [CommRing R] (u : Rˣ) : R ≃ₗ[R] R where
  toFun a := (u : R) * a
  invFun a := ((u⁻¹ : Rˣ) : R) * a
  left_inv a := by simp [← mul_assoc]
  right_inv a := by simp [← mul_assoc]
  map_add' a b := mul_add _ _ _
  map_smul' a b := by
    change (u : R) * (a * b) = a * ((u : R) * b)
    ring

theorem localUnitMulEquiv_preserves_coordinate_ideal (center : ℂ)
    (u : (HolomorphicGerm center)ˣ) :
    (coordinateModuleIdeal center).map (localUnitMulEquiv u).toLinearMap =
      coordinateModuleIdeal center := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    exact (coordinateModuleIdeal center).smul_mem (u : HolomorphicGerm center) hx
  · intro y hy
    apply Submodule.mem_map.mpr
    refine ⟨((u⁻¹ : (HolomorphicGerm center)ˣ) : HolomorphicGerm center) * y,
      (coordinateModuleIdeal center).smul_mem _ hy, ?_⟩
    simp [localUnitMulEquiv, ← mul_assoc]

def localUnitQuotientEquiv (center : ℂ) (u : (HolomorphicGerm center)ˣ) :
    (HolomorphicGerm center ⧸ coordinateModuleIdeal center) ≃ₗ[HolomorphicGerm center]
      (HolomorphicGerm center ⧸ coordinateModuleIdeal center) :=
  Submodule.Quotient.equiv _ _ (localUnitMulEquiv u)
    (localUnitMulEquiv_preserves_coordinate_ideal center u)

theorem meromorphicPrincipalQuotientEquiv_mk (center : ℂ)
    (v : MeromorphicGerm center) (hv : v ≠ 0) (a : HolomorphicGerm center) :
    meromorphicPrincipalQuotientEquiv center v hv (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (meromorphicSpanEquiv center v hv a) := rfl

theorem localUnitQuotientEquiv_mk (center : ℂ) (u : (HolomorphicGerm center)ˣ)
    (a : HolomorphicGerm center) :
    localUnitQuotientEquiv center u (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk ((u : HolomorphicGerm center) * a) := rfl

def localCompletionUnit (center : ℂ) (m : MultiplierOrderData center) : (HolomorphicGerm center)ˣ :=
  (holomorphicGermOf_isUnit center m.unit m.unit_analytic m.unit_ne_zero).unit

theorem localCompletionUnit_value (center : ℂ) (m : MultiplierOrderData center) :
    (localCompletionUnit center m : HolomorphicGerm center) =
      holomorphicGermOf center m.unit m.unit_analytic :=
  (holomorphicGermOf_isUnit center m.unit m.unit_analytic m.unit_ne_zero).unit_spec

theorem completion_fraction_identity (center : ℂ) (m : MultiplierOrderData center)
    (hm : 0 < m.order) (a : HolomorphicGerm center) :
    algebraMap (HolomorphicGerm center) (MeromorphicGerm center)
        (holomorphicGermOf center m.multiplier (multiplier_analytic m)) *
        (algebraMap (HolomorphicGerm center) (MeromorphicGerm center) a *
          (meromorphicCoordinate center)⁻¹) =
      algebraMap (HolomorphicGerm center) (MeromorphicGerm center)
        (holomorphicGermOf center m.unit m.unit_analytic * a) *
          meromorphicCoordinate center ^ (m.order - 1) := by
  have hfactor : holomorphicGermOf center m.multiplier (multiplier_analytic m) =
      coordinateGerm center ^ m.order * holomorphicGermOf center m.unit m.unit_analytic := by
    apply Subtype.ext
    exact Germ.coe_eq.mpr m.multiplier_eq
  rw [hfactor, map_mul, map_pow, map_mul]
  change (meromorphicCoordinate center ^ m.order * _) *
    (_ * (meromorphicCoordinate center)⁻¹) = _
  have hpow : meromorphicCoordinate center ^ m.order =
      meromorphicCoordinate center ^ (m.order - 1) * meromorphicCoordinate center := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow]
  field_simp [meromorphicCoordinate_ne_zero center]

theorem completion_quotient_equiv_coordinates (center : ℂ) (m : MultiplierOrderData center) :
    ∃ e : (LocalPoleCarrier center ⧸ LocalPoleBackground center) ≃ₗ[HolomorphicGerm center]
        (LocalCompletedCarrier center m.order ⧸ LocalCompletedBackground center m.order),
      ∀ a : HolomorphicGerm center,
        e (Submodule.Quotient.mk
          (meromorphicSpanEquiv center (meromorphicCoordinate center)⁻¹
            (inv_ne_zero (meromorphicCoordinate_ne_zero center)) a)) =
          Submodule.Quotient.mk
            (meromorphicSpanEquiv center (meromorphicCoordinate center ^ (m.order - 1))
              (pow_ne_zero _ (meromorphicCoordinate_ne_zero center))
              (holomorphicGermOf center m.unit m.unit_analytic * a)) := by
  let P := meromorphicPrincipalQuotientEquiv center (meromorphicCoordinate center)⁻¹
    (inv_ne_zero (meromorphicCoordinate_ne_zero center))
  let J := meromorphicPrincipalQuotientEquiv center (meromorphicCoordinate center ^ (m.order - 1))
    (pow_ne_zero _ (meromorphicCoordinate_ne_zero center))
  let U := localCompletionUnit center m
  let e := P.symm.trans ((localUnitQuotientEquiv center U).trans J)
  refine ⟨e, ?_⟩
  intro a
  change J (localUnitQuotientEquiv center U (P.symm
    (Submodule.Quotient.mk (meromorphicSpanEquiv center (meromorphicCoordinate center)⁻¹
      (inv_ne_zero (meromorphicCoordinate_ne_zero center)) a)))) = _
  rw [← meromorphicPrincipalQuotientEquiv_mk, LinearEquiv.symm_apply_apply,
    localUnitQuotientEquiv_mk, meromorphicPrincipalQuotientEquiv_mk]
  rw [show (U : HolomorphicGerm center) = holomorphicGermOf center m.unit m.unit_analytic from
    localCompletionUnit_value center m]
  rfl

/-- Literal multiplication by the multiplier, on the actual fraction-field
pole and completed carriers. The membership proof uses its germ factorization. -/
def localCompletionMap (center : ℂ) (m : MultiplierOrderData center) (hm : 0 < m.order) :
    LocalPoleCarrier center →ₗ[HolomorphicGerm center] LocalCompletedCarrier center m.order where
  toFun f := ⟨algebraMap (HolomorphicGerm center) (MeromorphicGerm center)
      (holomorphicGermOf center m.multiplier (multiplier_analytic m)) * (f : MeromorphicGerm center), by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp f.property
    rw [← ha]
    rw [Algebra.smul_def]
    change algebraMap (HolomorphicGerm center) (MeromorphicGerm center)
      (holomorphicGermOf center m.multiplier (multiplier_analytic m)) *
      (algebraMap (HolomorphicGerm center) (MeromorphicGerm center) a *
        (meromorphicCoordinate center)⁻¹) ∈
        meromorphicPrincipalSpan center (meromorphicCoordinate center ^ (m.order - 1))
    rw [completion_fraction_identity center m hm a]
    simpa only [Algebra.smul_def] using
      Submodule.smul_mem (LocalCompletedCarrier center m.order)
        (holomorphicGermOf center m.unit m.unit_analytic * a)
        (Submodule.subset_span (by simp))⟩
  map_add' f g := by
    apply Subtype.ext
    exact mul_add _ _ _
  map_smul' a f := by
    apply Subtype.ext
    change _ * (a • (f : MeromorphicGerm center)) = a • (_ * (f : MeromorphicGerm center))
    simp only [Algebra.smul_def]
    ring

theorem localCompletionMap_span (center : ℂ) (m : MultiplierOrderData center)
    (hm : 0 < m.order) (a : HolomorphicGerm center) :
    localCompletionMap center m hm
      (meromorphicSpanEquiv center (meromorphicCoordinate center)⁻¹
        (inv_ne_zero (meromorphicCoordinate_ne_zero center)) a) =
      meromorphicSpanEquiv center (meromorphicCoordinate center ^ (m.order - 1))
        (pow_ne_zero _ (meromorphicCoordinate_ne_zero center))
        (holomorphicGermOf center m.unit m.unit_analytic * a) := by
  apply Subtype.ext
  change algebraMap (HolomorphicGerm center) (MeromorphicGerm center)
      (holomorphicGermOf center m.multiplier (multiplier_analytic m)) *
      (a • (meromorphicCoordinate center)⁻¹) =
    (holomorphicGermOf center m.unit m.unit_analytic * a) •
      meromorphicCoordinate center ^ (m.order - 1)
  simpa only [Algebra.smul_def] using completion_fraction_identity center m hm a

theorem completion_quotient_equiv (center : ℂ) (m : MultiplierOrderData center)
    (hm : 0 < m.order) :
    ∃ e : (LocalPoleCarrier center ⧸ LocalPoleBackground center) ≃ₗ[HolomorphicGerm center]
        (LocalCompletedCarrier center m.order ⧸ LocalCompletedBackground center m.order),
      (∀ f : LocalPoleCarrier center,
        e (Submodule.Quotient.mk f) = Submodule.Quotient.mk (localCompletionMap center m hm f)) ∧
      ∀ a : HolomorphicGerm center,
        e (Submodule.Quotient.mk
          (meromorphicSpanEquiv center (meromorphicCoordinate center)⁻¹
            (inv_ne_zero (meromorphicCoordinate_ne_zero center)) a)) =
          Submodule.Quotient.mk
            (meromorphicSpanEquiv center (meromorphicCoordinate center ^ (m.order - 1))
              (pow_ne_zero _ (meromorphicCoordinate_ne_zero center))
              (holomorphicGermOf center m.unit m.unit_analytic * a)) := by
  obtain ⟨e, he⟩ := completion_quotient_equiv_coordinates center m
  refine ⟨e, ?_, he⟩
  intro f
  obtain ⟨a, rfl⟩ := (meromorphicSpanEquiv center (meromorphicCoordinate center)⁻¹
    (inv_ne_zero (meromorphicCoordinate_ne_zero center))).surjective f
  rw [he, localCompletionMap_span]

end Zeta23.OPICA
