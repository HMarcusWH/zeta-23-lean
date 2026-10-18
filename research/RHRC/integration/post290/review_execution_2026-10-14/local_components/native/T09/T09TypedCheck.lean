import Zeta23.CCM.NativeWeilResponse

open MeasureTheory Complex
open scoped ComplexConjugate

set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs.withType true
set_option pp.maxSteps 1000000

#print Zeta23.CCM.nativeWeilArchResponse
#print Zeta23.CCM.nativeWeilPoleResponse
#print Zeta23.CCM.nativeWeilPrimeResponse
#print Zeta23.CCM.nativeWeilResponse
#print Zeta23.CCM.nativePhysicalH1Norm

#check @Zeta23.CCM.nativeWeilResponse_decomposition
#check @Zeta23.CCM.nativeGammaBracket_quadratic_bound
#check @Zeta23.CCM.nativeWeilArch_fourier_integrable
#check @Zeta23.CCM.nativeWeilArchResponse_pairing
#check @Zeta23.CCM.nativePaperFT_imaginary
#check @Zeta23.CCM.nativeWeilPoleResponse_pairing
#check @Zeta23.CCM.nativeWeilPrimeResponse_eq_history_sum
#check @Zeta23.CCM.nativeWeilPrimeResponse_continuous
#check @Zeta23.CCM.nativeWeilPoleResponse_continuous
#check @Zeta23.CCM.nativeWeilPrimeResponse_pairing
#check @Zeta23.CCM.nativeWeilArchResponse_continuous
#check @Zeta23.CCM.nativeWeilResponse_continuous
#check @Zeta23.CCM.nativeWeilResponse_memLp_two_on_interval
#check @Zeta23.CCM.nativeWeilResponse_indicator_memLp_two
#check @Zeta23.CCM.nativeWeilResponse_pairing
#check @Zeta23.CCM.nativeWeilArch_fourier_memLp_two
#check @Zeta23.CCM.nativeWeilArchResponse_memLp_two

example {f v : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hv : Continuous v) (hvc : HasCompactSupport v) :
    Zeta23.zetaZeroConfig.W f v =
      ∫ x : ℝ, Zeta23.CCM.nativeWeilResponse f x * conj (v x) :=
  Zeta23.CCM.nativeWeilResponse_pairing hf hfc hv hvc

example {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (a b : ℝ) :
    MemLp ((Set.Icc a b).indicator (Zeta23.CCM.nativeWeilResponse f)) 2 volume :=
  Zeta23.CCM.nativeWeilResponse_indicator_memLp_two hf hfc a b

example {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    MemLp (Zeta23.CCM.nativeWeilArchResponse f) 2 volume :=
  Zeta23.CCM.nativeWeilArchResponse_memLp_two hf hfc
