import Zeta23.OPICAFollowup.WeightedMixing
open Filter MeasureTheory Set
open scoped ENNReal Topology FourierTransform
open Zeta23.OPICA Zeta23.OPICAFollowup
-- (1) the leakage constant is ζ(2a+1)/ζ(a+1/2), not its inverse
theorem bad_inverted_ratio (σ : LocallyFiniteComplexMeasure) (a : ℝ) (ha : 1 / 2 < a)
    (hm : mixingExponentialMoment a σ < ∞) :
    ENNReal.ofReal ((riemannZeta ((a + 1 / 2 : ℝ) : ℂ) / riemannZeta ((2 * a + 1 : ℝ) : ℂ)).re) *
        ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂σ.totalVariation ≤
      ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
        ∂(weightedDilationMixture σ a ha.le hm).totalVariation :=
  (weighted_gap_leakage.1 σ a ha hm).1
-- (2) the Möbius lattice identity needs the M⁻ ∗ N term
theorem bad_no_minus_term (σ : LocallyFiniteComplexMeasure) (a : ℝ) (ha : 1 / 2 < a)
    (hm : mixingExponentialMoment a σ < ∞) :
    moebiusPlusComb ∗ integerLogComb = Measure.dirac 0 :=
  (weighted_mobius_inverse σ a ha hm).2.2.2.1
-- (3) the sharp gap needs canonical Fourier self-duality
theorem bad_no_selfdual (σ : LocallyFiniteComplexMeasure) (a : ℝ) (ha : 1 / 2 < a)
    (hm : mixingExponentialMoment a σ < ∞)
    (hgap : (weightedDilationMixture σ a ha.le hm).variationControl (Ioo (-1) 1 \ {0}) = 0) :
    σ.variationControl ({0}ᶜ) = 0 :=
  (weighted_mixture_sharp_gap σ a ha hm (by assumption) hgap).2.1
-- (4) the endpoint a = 1/2 is excluded
theorem bad_endpoint (σ : LocallyFiniteComplexMeasure) (a : ℝ) (ha : 1 / 2 ≤ a)
    (hm : mixingExponentialMoment a σ < ∞) :
    ENNReal.ofReal ((riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re) *
        ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂σ.totalVariation ≤
      ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
        ∂(weightedDilationMixture σ a ha hm).totalVariation :=
  (weighted_gap_leakage.1 σ a ha hm).1
-- (5) the weighted norm of N is ζ(a + 1/2), not ζ(a)
theorem bad_zeta_shift (σ : LocallyFiniteComplexMeasure) (a : ℝ) (ha : 1 / 2 < a)
    (hm : mixingExponentialMoment a σ < ∞) :
    ((∑' n : ℕ, (n : ℝ) ^ (-(a + 1 / 2)) : ℝ) : ℂ) = riemannZeta (a : ℂ) :=
  (weighted_mobius_inverse σ a ha hm).2.2.2.2.2.2.2.2.2.1.2
-- (6) the gap hypothesis must cover the punctured interval, not only (0,1)
theorem bad_one_sided_gap (σ : LocallyFiniteComplexMeasure) (a : ℝ) (ha : 1 / 2 < a)
    (hm : mixingExponentialMoment a σ < ∞)
    (hself : 𝓕 ((weightedDilationMixture σ a ha.le hm).distributionOfLinearGrowth
        (weightedDilationMixture_growth σ a ha.le hm)) =
      (weightedDilationMixture σ a ha.le hm).distributionOfLinearGrowth
        (weightedDilationMixture_growth σ a ha.le hm))
    (hgap : (weightedDilationMixture σ a ha.le hm).variationControl (Ioo 0 1) = 0) :
    σ.variationControl ({0}ᶜ) = 0 :=
  (weighted_mixture_sharp_gap σ a ha hm hself hgap).2.1
-- (7) the density identification needs decay rate b > 1/2
theorem bad_slow_decay_density (h : ℝ → ℂ) (hc : Continuous h) (H b : ℝ) (hb : 0 < b)
    (hd : ∀ t, ‖h t‖ ≤ H * Real.exp (-b * |t|)) (x : ℝ) (hx : 0 < x) :
    positiveMixtureDensity (fun t => ENNReal.ofReal (densityCoordinate h 0 t)) x < ⊤ :=
  (weighted_gap_leakage.2.2.2.2 h hc H b hb hd).2.2.1 0 x hx
-- (8) M⁺ and M⁻ are mutually singular; they are not claimed equal
theorem bad_moebius_combs_equal (σ : LocallyFiniteComplexMeasure) (a : ℝ) (ha : 1 / 2 < a)
    (hm : mixingExponentialMoment a σ < ∞) :
    moebiusPlusComb = moebiusMinusComb :=
  (weighted_mobius_inverse σ a ha hm).2.2.2.2.2.2.2.2.2.2.1
