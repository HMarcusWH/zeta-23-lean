import Zeta23.OPICARound6.PrimeFactorPaths.FiniteWeightedGram
import Zeta23.OPICARound6.PrimeFactorPaths.TwoShellCalibration
import Zeta23.OPICARound6.PrimeFactorPaths.FiniteSelectorEnergy
import Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges
import Zeta23.OPICARound6.PrimeFactorPaths.DivisorStrip
import Zeta23.OPICARound6.PrimeFactorPaths.FactorialKnot
import Zeta23.OPICARound6.PrimeFactorPaths.FinitePairKernel
import Zeta23.OPICARound6.PrimeFactorPaths.FiniteRenewal
import Zeta23.OPICARound6.PrimeFactorPaths.PrimitiveEulerMultiplier
import Zeta23.OPICARound6.PrimeFactorPaths.StoppedPrimeArea
import Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost
import Zeta23.OPICARound6.PrimeFactorPaths.PrimeAreaIntegral
import Zeta23.OPICARound6.PrimeFactorPaths.ParityDeficitProduct

/-! Independent import checks for the public finite arithmetic and algebraic statements. -/

open scoped ArithmeticFunction.Moebius

section
open Zeta23.OPICARound6.PrimeFactorPaths.FiniteWeightedGram

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FiniteWeightedGram.scalar_factorization :
    ∀ (A B g : ℝ),
    (A - B)^2 + 4 * (A * B - g^2) = (A + B + 2*g) * (A + B - 2*g))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FiniteWeightedGram.scalar_factorization

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FiniteWeightedGram.signed_energy :
    ∀ {ι : Type*} (s : Finset ι) (w l h : ι → ℝ) (c : ℝ),
    energy s w (fun i => l i + c * h i) =
      energy s w l + c^2 * energy s w h + (2*c) * cross s w l h)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FiniteWeightedGram.signed_energy

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FiniteWeightedGram.ordered_minors :
    ∀ {ι : Type*} (s : Finset ι) (w l h : ι → ℝ),
    2 * (energy s w l * energy s w h - (cross s w l h)^2) =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * (l i * h j - l j * h i)^2)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FiniteWeightedGram.ordered_minors

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FiniteWeightedGram.determinant_nonneg :
    ∀ {ι : Type*} (s : Finset ι) (w l h : ι → ℝ)
    (_hw : ∀ i ∈ s, 0 ≤ w i),
    0 ≤ energy s w l * energy s w h - (cross s w l h)^2)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FiniteWeightedGram.determinant_nonneg

end

section
open Zeta23.OPICARound6.PrimeFactorPaths.TwoShellCalibration

#check (@Zeta23.OPICARound6.PrimeFactorPaths.TwoShellCalibration.two_shell :
    ∀ (p₁ a₁ p₂ a₂ p a f u₁ u₂ : ℝ),
    (det p₁ a₁ p₂ a₂)^2 * f^2 ≤
    traceEnergy p₁ a₁ p₂ a₂ * (residual p a f u₁ p₁ a₁ + residual p a f u₂ p₂ a₂))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.TwoShellCalibration.two_shell

#check (@Zeta23.OPICARound6.PrimeFactorPaths.TwoShellCalibration.weighted_finite :
    ∀ {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (_hw : ∀ i ∈ s, 0 ≤ w i) (p₁ a₁ p₂ a₂ : ℝ) (p a f u₁ u₂ : ι → ℝ),
    (det p₁ a₁ p₂ a₂)^2 * (∑ i ∈ s, w i * (f i)^2) ≤
      traceEnergy p₁ a₁ p₂ a₂ * ∑ i ∈ s, w i *
        (residual (p i) (a i) (f i) (u₁ i) p₁ a₁ +
         residual (p i) (a i) (f i) (u₂ i) p₂ a₂))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.TwoShellCalibration.weighted_finite

end

section
open Zeta23.OPICARound6.PrimeFactorPaths.FiniteSelectorEnergy

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FiniteSelectorEnergy.posSq_sub_le :
    ∀ (u v H : ℝ) (_hu : |u| ≤ H) (_hv : |v| ≤ H),
    |(max u 0) ^ 2 - (max v 0) ^ 2| ≤ 2 * H * |u - v|)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FiniteSelectorEnergy.posSq_sub_le

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FiniteSelectorEnergy.signed_weight_energy_comparison :
    ∀ {ι : Type*} (s : Finset ι) (w u v H : ι → ℝ)
    (pol : ℝ) (_hpol : |pol| = 1) (_hu : ∀ i ∈ s, |u i| ≤ H i)
    (_hv : ∀ i ∈ s, |v i| ≤ H i),
    |(∑ i ∈ s, w i * (max (pol * u i) 0)^2) -
      (∑ i ∈ s, w i * (max (pol * v i) 0)^2)| ≤
      ∑ i ∈ s, |w i| * (2 * H i * |u i-v i|))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FiniteSelectorEnergy.signed_weight_energy_comparison

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FiniteSelectorEnergy.weighted_energy_comparison :
    ∀ {ι : Type*} (s : Finset ι) (w u v H : ι → ℝ)
    (pol : ℝ) (_hpol : |pol| = 1) (_hw : ∀ i ∈ s, 0 ≤ w i)
    (_hu : ∀ i ∈ s, |u i| ≤ H i) (_hv : ∀ i ∈ s, |v i| ≤ H i),
    |(∑ i ∈ s, w i * (max (pol * u i) 0)^2) -
      (∑ i ∈ s, w i * (max (pol * v i) 0)^2)| ≤
      ∑ i ∈ s, w i * (2 * H i * |u i-v i|))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FiniteSelectorEnergy.weighted_energy_comparison

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FiniteSelectorEnergy.weighted_sq_distance_le :
    ∀ {ι : Type*} (s : Finset ι) (w u v : ι → ℝ)
    (pol : ℝ) (_hpol : |pol| = 1) (_hw : ∀ i ∈ s, 0 ≤ w i),
    (∑ i ∈ s, w i * (max (pol * u i) 0 - max (pol * v i) 0)^2) ≤
      ∑ i ∈ s, w i * (u i-v i)^2)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FiniteSelectorEnergy.weighted_sq_distance_le

end

section
open Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges

#check (@Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges.contingency_covariance :
    ∀ (a b c d : ℝ),
    (a+b+c+d)*(a-b-c+d) - (a+b-c-d)*(a-b+c-d) = 4*(a*d-b*c))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges.contingency_covariance

#check (@Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges.roughSign_factor :
    ∀ {y d m : ℕ} (_hcop : Nat.Coprime d m)
    (_hrough : ∀ p ∈ (d * m).primeFactors, y < p),
    roughSign y (d * m) = (μ d : ℝ) * (μ m : ℝ))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges.roughSign_factor

#check (@Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges.roughSign_split_parity :
    ∀ {y n : ℕ} (z : ℕ) (_hsq : Squarefree n)
    (_hrough : ∀ p ∈ n.primeFactors, y < p),
    roughSign y n = (-1 : ℝ) ^ (n.primeFactors.filter (· ≤ z)).card *
      (-1 : ℝ) ^ (n.primeFactors.filter (z < ·)).card)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges.roughSign_split_parity

#check (@Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges.abs_roughSign_le_one :
    ∀ (y n : ℕ),
    |roughSign y n| ≤ 1)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges.abs_roughSign_le_one

#check (@Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges.abs_charge_le_card :
    ∀ (y : ℕ) (labels : Finset ℕ),
    |charge y labels| ≤ labels.card)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges.abs_charge_le_card

#check (@Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges.charge_sub_survivors :
    ∀ (y : ℕ) (labels removed : Finset ℕ),
    charge y labels - charge y (labels \ removed) = charge y (labels ∩ removed))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges.charge_sub_survivors

#check (@Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges.selector_energy_loss :
    ∀ {ι : Type*} (nodes : Finset ι) (labels : ι → Finset ℕ)
    (removed : Finset ℕ) (y : ℕ) (w : ι → ℝ) (_hw : ∀ j ∈ nodes, 0 ≤ w j)
    (pol : ℝ) (_hpol : |pol| = 1),
    ∑ j ∈ nodes, w j *
      |(max (pol * charge y (labels j)) 0)^2 -
       (max (pol * charge y (labels j \ removed)) 0)^2| ≤
    ∑ j ∈ nodes, w j * (2 * (labels j).card * |charge y (labels j ∩ removed)|))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.RoughNodeCharges.selector_energy_loss

end

section
open Zeta23.OPICARound6.PrimeFactorPaths.DivisorStrip
open ArithmeticFunction

#check (@Zeta23.OPICARound6.PrimeFactorPaths.DivisorStrip.residual_prime_mul :
    ∀ {p n : ℕ} (_hp : p.Prime) (_hc : p.Coprime n) (L : ℕ),
    residual L (p * n) =
      -(∑ d ∈ n.divisors, if d ≤ L ∧ L < p * d then μ d else 0))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.DivisorStrip.residual_prime_mul

#check (@Zeta23.OPICARound6.PrimeFactorPaths.DivisorStrip.exists_divisor_of_residual_ne_zero :
    ∀ {p n L : ℕ} (_hp : p.Prime) (_hc : p.Coprime n)
    (_h : residual L (p * n) ≠ 0),
    ∃ d ∈ n.divisors, d ≤ L ∧ L < p * d ∧ μ d ≠ 0)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.DivisorStrip.exists_divisor_of_residual_ne_zero

end

section
open Zeta23.OPICARound6.PrimeFactorPaths.FactorialKnot

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FactorialKnot.weight_prefix :
    ∀ (m n : ℕ) (_hm : 0 < m),
    (∑ k ∈ Finset.range n, weight m (k+1)) = (n % m : ℕ))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FactorialKnot.weight_prefix

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FactorialKnot.ramp_increment :
    ∀ (m n : ℕ) (_hm : 0 < m),
    ramp m (n+1) = ramp m n + (n % m : ℕ))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FactorialKnot.ramp_increment

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FactorialKnot.twice_ramp_at_knot :
    ∀ (m n : ℕ) (_hm : 0 < m),
    2 * ramp m n = ((m : ℤ)-1) * n - (n % m : ℕ) * ((m : ℤ) - (n % m : ℕ)))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FactorialKnot.twice_ramp_at_knot

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FactorialKnot.calibrated_residue :
    ∀ {ι : Type*} (s : Finset ι) (a : ι → ℝ) (m : ι → ℕ)
    (n : ℕ) (_hm : ∀ i ∈ s, 0 < m i)
    (_hcal : (∑ i ∈ s, a i * ((m i : ℝ) - 1)) = 2),
    (n : ℝ) - 1 - (∑ i ∈ s, a i * (ramp (m i) n : ℝ)) =
      -1 + (1/2 : ℝ) * ∑ i ∈ s, a i * (n % m i : ℕ) * ((m i : ℝ) - (n % m i : ℕ)))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FactorialKnot.calibrated_residue

end

section
open Zeta23.OPICARound6.PrimeFactorPaths.FinitePairKernel

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FinitePairKernel.one_moment :
    ∀ {ι : Type*} (s : Finset ι) (a z : ι → ℝ) (k : ℕ),
    (2 : ℝ)^k * (∑ i ∈ s, a i * z i ^ k)^2 =
      ∑ i ∈ s, ∑ j ∈ s, (a i * a j) * (2 * z i * z j)^k)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FinitePairKernel.one_moment

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FinitePairKernel.geometric_moments :
    ∀ {ι : Type*} (s : Finset ι) (a z : ι → ℝ) (N : ℕ),
    (∑ k ∈ Finset.range N, (2 : ℝ)^k * (∑ i ∈ s, a i * z i ^ k)^2) =
      ∑ i ∈ s, ∑ j ∈ s, (a i * a j) * ∑ k ∈ Finset.range N, (2 * z i * z j)^k)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FinitePairKernel.geometric_moments

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FinitePairKernel.geometric_remainder :
    ∀ (x : ℝ) (N : ℕ) (_hx : x ≠ 1),
    1 / (1 - x) = (∑ k ∈ Finset.range N, x^k) + x^N / (1 - x))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FinitePairKernel.geometric_remainder

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FinitePairKernel.rational_pair_remainder :
    ∀ {ι : Type*} (s : Finset ι) (a z : ι → ℝ) (N : ℕ)
    (_h : ∀ i ∈ s, ∀ j ∈ s, 2 * z i * z j ≠ 1),
    (∑ i ∈ s, ∑ j ∈ s, (a i * a j) * (1 / (1 - 2 * z i * z j))) =
      (∑ k ∈ Finset.range N, (2 : ℝ)^k * (∑ i ∈ s, a i * z i ^ k)^2) +
        ∑ i ∈ s, ∑ j ∈ s, (a i * a j) * ((2 * z i * z j)^N / (1 - 2 * z i * z j)))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FinitePairKernel.rational_pair_remainder

end

section
open Zeta23.OPICARound6.PrimeFactorPaths.FiniteRenewal

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FiniteRenewal.abel_history :
    ∀ (w A : ℕ → ℝ) {r L : ℕ} (_h : r < L),
    (∑ j ∈ Finset.Ioc r L, w j * (A j - A (j - 1))) =
      w L * A L - w (r + 1) * A r -
        ∑ j ∈ Finset.Ico (r + 1) L, (w (j + 1) - w j) * A j)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FiniteRenewal.abel_history

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FiniteRenewal.history_weight_total :
    ∀ (w : ℕ → ℝ) {r L : ℕ} (_h : r < L),
    w (r + 1) + (∑ j ∈ Finset.Ico (r + 1) L, (w (j + 1) - w j)) = w L)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FiniteRenewal.history_weight_total

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FiniteRenewal.history_upper :
    ∀ (w A : ℕ → ℝ) (bound : ℝ) {r L : ℕ} (_h : r < L)
    (_hbase : 0 ≤ w (r + 1)) (_hsteps : ∀ j ∈ Finset.Ico (r + 1) L, w j ≤ w (j + 1))
    (_hA : ∀ j ∈ Finset.Ico r L, A j ≤ bound),
    w (r + 1) * A r + (∑ j ∈ Finset.Ico (r + 1) L, (w (j + 1) - w j) * A j)
      ≤ w L * bound)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FiniteRenewal.history_upper

#check (@Zeta23.OPICARound6.PrimeFactorPaths.FiniteRenewal.renewal_upper :
    ∀ (a error : ℕ → ℝ) (kernel : ℕ → ℕ → ℝ) (bound : ℝ)
    (_hrec : ∀ n, a n ≤ error n + ∑ j ∈ Finset.range n, kernel n j * a j)
    (_hpos : ∀ n j, j < n → 0 ≤ kernel n j)
    (_hbudget : ∀ n, error n + (∑ j ∈ Finset.range n, kernel n j) * bound ≤ bound),
    ∀ n, a n ≤ bound)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.FiniteRenewal.renewal_upper

end

section
open Zeta23.OPICARound6.PrimeFactorPaths.PrimitiveEulerMultiplier

#check (@Zeta23.OPICARound6.PrimeFactorPaths.PrimitiveEulerMultiplier.cosineFactor_pos :
    ∀ {q : ℝ} (_hq : 1 < q) (ξ : ℝ),
    0 < cosineFactor q ξ)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.PrimitiveEulerMultiplier.cosineFactor_pos

#check (@Zeta23.OPICARound6.PrimeFactorPaths.PrimitiveEulerMultiplier.cosineFactor_eq_euler :
    ∀ {q : ℝ} (_hq : 1 < q) (ξ : ℝ),
    cosineFactor q ξ = ‖1 - (q : ℂ) ^ (-(1/2 : ℂ) - (ξ : ℂ)*Complex.I)‖ ^ 2 / (1 + 1/q))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.PrimitiveEulerMultiplier.cosineFactor_eq_euler

#check (@Zeta23.OPICARound6.PrimeFactorPaths.PrimitiveEulerMultiplier.finite_primitive_euler_identity_and_pos :
    ∀ {ι : Type*} (A : Finset ι) (q : ι → ℝ)
    (_hq : ∀ i ∈ A, 1 < q i) (ξ : ℝ),
    (∏ i ∈ A, cosineFactor (q i) ξ) =
      (∏ i ∈ A, ‖1 - (q i : ℂ) ^ (-(1/2 : ℂ) - (ξ : ℂ)*Complex.I)‖ ^ 2 / (1 + 1/q i)) ∧
    0 < ∏ i ∈ A, cosineFactor (q i) ξ)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.PrimitiveEulerMultiplier.finite_primitive_euler_identity_and_pos

end

section
open Zeta23.OPICARound6.PrimeFactorPaths.StoppedPrimeArea

#check (@Zeta23.OPICARound6.PrimeFactorPaths.StoppedPrimeArea.active_primes_in_gap :
    ∀ {p r : ℕ} (_gap : PrimeGap p r) {x : ℝ}
    (_hpx : (p : ℝ) ≤ x) (_hxr : x < (r : ℝ)),
    Nat.primesLE ⌊x⌋₊ = Nat.primesLE p)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.StoppedPrimeArea.active_primes_in_gap

#check (@Zeta23.OPICARound6.PrimeFactorPaths.StoppedPrimeArea.completed_square_in_gap :
    ∀ {p r : ℕ} (_gap : PrimeGap p r) {x : ℝ}
    (_hpx : (p : ℝ) ≤ x) (_hxr : x < (r : ℝ)),
    rampArea x = score p - (x - Chebyshev.theta p) ^ 2 / 2)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.StoppedPrimeArea.completed_square_in_gap

#check (@Zeta23.OPICARound6.PrimeFactorPaths.StoppedPrimeArea.stopping_point_unique_max :
    ∀ {p r : ℕ} (_gap : PrimeGap p r)
    (_hleft : (p : ℝ) < Chebyshev.theta p) (_hright : Chebyshev.theta p < r),
    rampArea (Chebyshev.theta p) = score p ∧
      ∀ x : ℝ, (p : ℝ) ≤ x → x < r → x ≠ Chebyshev.theta p →
        rampArea x < rampArea (Chebyshev.theta p))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.StoppedPrimeArea.stopping_point_unique_max

end

section
open Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost
open Zeta23.OPICARound6.PrimeFactorPaths.StoppedPrimeArea

#check (@Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost.log_eq_sum_primeFactors :
    ∀ {n : ℕ} (_hn : Squarefree n),
    Real.log n = ∑ q ∈ n.primeFactors, Real.log q)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost.log_eq_sum_primeFactors

#check (@Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost.mismatch_identity :
    ∀ {n : ℕ} (_hn : Squarefree n) {x : ℝ} (_hx : 0 ≤ x),
    rampArea x - integerScore n + (x - Real.log n) ^ 2 / 2 =
      (∑ q ∈ Nat.primesLE ⌊x⌋₊ \ n.primeFactors, (x - q) * Real.log q) +
      ∑ q ∈ n.primeFactors \ Nat.primesLE ⌊x⌋₊, ((q : ℝ) - x) * Real.log q)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost.mismatch_identity

#check (@Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost.squarefree_score_le_ramp :
    ∀ {n : ℕ} (_hn : Squarefree n),
    integerScore n ≤ rampArea (Real.log n))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost.squarefree_score_le_ramp

#check (@Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost.primorial_recovers_ramp :
    ∀ {x : ℝ} (_hx : 0 ≤ x),
    rampArea x = integerScore (primorial ⌊x⌋₊) - (x - Real.log (primorial ⌊x⌋₊)) ^ 2 / 2)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost.primorial_recovers_ramp

#check (@Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost.negative_ramp_of_integer_inequality :
    ∀ (_h : ∀ n : ℕ, 8 ≤ n → Squarefree n → (Real.log n) ^ 2 + 4 < 2 * cost n)
    {x : ℝ} (_hx : 5 ≤ x),
    rampArea x < 0)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost.negative_ramp_of_integer_inequality

#check (@Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost.negative_ramp_below_five :
    ∀ {x : ℝ} (_hx : 2 < x) (_h5 : x < 5),
    rampArea x < 0)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost.negative_ramp_below_five

#check (@Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost.negative_ramp_iff_integer_inequality :
    (∀ x : ℝ, 2 < x → rampArea x < 0) ↔
    (∀ n : ℕ, 8 ≤ n → Squarefree n → (Real.log n) ^ 2 + 4 < 2 * cost n))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost.negative_ramp_iff_integer_inequality

end

section
open Zeta23.OPICARound6.PrimeFactorPaths.PrimeAreaIntegral
open Zeta23.OPICARound6.PrimeFactorPaths.StoppedPrimeArea Zeta23.OPICARound6.PrimeFactorPaths.SquarefreePrimeCost
open MeasureTheory

#check (@Zeta23.OPICARound6.PrimeFactorPaths.PrimeAreaIntegral.integral_theta_eq_first_moment :
    ∀ {x : ℝ} (_hx : 2 ≤ x),
    (∫ u in 2..x, Chebyshev.theta u) =
      x * Chebyshev.theta x - weightedPosition ⌊x⌋₊)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.PrimeAreaIntegral.integral_theta_eq_first_moment

#check (@Zeta23.OPICARound6.PrimeFactorPaths.PrimeAreaIntegral.integral_theta_sub_id_eq_rampArea :
    ∀ {x : ℝ} (_hx : 2 ≤ x),
    (∫ u in 2..x, (Chebyshev.theta u - u)) = rampArea x)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.PrimeAreaIntegral.integral_theta_sub_id_eq_rampArea

#check (@Zeta23.OPICARound6.PrimeFactorPaths.PrimeAreaIntegral.integral_negative_iff_squarefree_prime_cost :
    (∀ x : ℝ, 2 < x → (∫ u in 2..x, (Chebyshev.theta u - u)) < 0) ↔
    (∀ n : ℕ, 8 ≤ n → Squarefree n → (Real.log n) ^ 2 + 4 < 2 * cost n))
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.PrimeAreaIntegral.integral_negative_iff_squarefree_prime_cost

end

section

#check (@Zeta23.OPICARound6.PrimeFactorPaths.ParityDeficitProduct.quadrant_remainder :
    ∀ x y : ℝ, 0 ≤ (max (x-y) 0)^2 - 4 * max x 0 * max (-y) 0 ∧
      (max (x-y) 0)^2 - 4 * max x 0 * max (-y) 0 ≤ (x+y)^2)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.ParityDeficitProduct.quadrant_remainder

#check (@Zeta23.OPICARound6.PrimeFactorPaths.ParityDeficitProduct.weighted_absolute_remainder :
    ∀ {ι : Type*} (nodes : Finset ι) (x y weight : ι → ℝ),
      (∀ i ∈ nodes, 0 ≤ weight i) →
      (∑ i ∈ nodes, weight i * |(max (x i - y i) 0)^2 - 4 * max (x i) 0 * max (-y i) 0|) ≤
        ∑ i ∈ nodes, weight i * (x i + y i)^2)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.ParityDeficitProduct.weighted_absolute_remainder

#check (@Zeta23.OPICARound6.PrimeFactorPaths.ParityDeficitProduct.forced_coefficient :
    ∀ a : ℝ, (∀ x y : ℝ, 0 ≤ (max (x-y) 0)^2 - a * max x 0 * max (-y) 0 ∧
      (max (x-y) 0)^2 - a * max x 0 * max (-y) 0 ≤ (x+y)^2) → a = 4)
#print axioms Zeta23.OPICARound6.PrimeFactorPaths.ParityDeficitProduct.forced_coefficient

end
