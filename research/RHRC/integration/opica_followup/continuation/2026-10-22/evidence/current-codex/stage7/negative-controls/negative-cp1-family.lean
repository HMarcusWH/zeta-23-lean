import Zeta23.OPICAFollowup.RenormalizedCoPoisson
open MeasureTheory Set Complex
open scoped FourierTransform SchwartzMap
open Zeta23.OPICAFollowup
-- (1) the kernel is D_t + D_(-t), not D_t - D_(-t)
theorem bad_kernel_sign (t : ℝ) : renormalizedCombKernel t = dilatedCombDistribution t -
    dilatedCombDistribution (-t) - ((Real.exp (t / 2) : ℝ) : ℂ) •
      (TemperedDistribution.delta (0 : ℝ) + 𝓕 (TemperedDistribution.delta (0 : ℝ))) :=
  renormalized_copoisson_tempered_family.1 t
-- (2) the origin atom must be subtracted, not only the continuum
theorem bad_no_origin_atom (t : ℝ) : renormalizedCombKernel t = dilatedCombDistribution t +
    dilatedCombDistribution (-t) - ((Real.exp (t / 2) : ℝ) : ℂ) •
      𝓕 (TemperedDistribution.delta (0 : ℝ)) :=
  renormalized_copoisson_tempered_family.1 t
-- (3) the decay rate is e^((1/2-k) t); the stronger rate e^(-k t) is not claimed
theorem bad_decay_rate (t : ℝ) (φ : 𝓢(ℝ, ℂ)) (k : ℕ) (hk : 2 ≤ k) :
    ‖coPoissonA t φ‖ ≤ latticeZetaConst k * SchwartzMap.seminorm ℂ k 0 φ *
      Real.exp ((-k : ℝ) * t) :=
  renormalized_copoisson_tempered_family.2.2.2.1 t φ k hk
-- (4) self-duality, not anti-self-duality
theorem bad_antiselfdual (lam : ℂ) : 𝓕 (coPoissonFamily lam) = -coPoissonFamily lam :=
  renormalized_copoisson_tempered_family.2.2.2.2.2.2.2.2.2.2.1 lam
-- (5) the lattice constant is 2ζ(k), not ζ(k)
theorem bad_constant (k : ℕ) (hk : 2 ≤ k) : ((latticeZetaConst k : ℝ) : ℂ) = riemannZeta k :=
  renormalized_copoisson_tempered_family.2.2.2.2.1 k hk
