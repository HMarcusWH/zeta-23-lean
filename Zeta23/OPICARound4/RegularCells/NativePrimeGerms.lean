import Zeta23.OPICARound4.RegularCells.NativePrimeExpansion
import Zeta23.OPICARound4.RegularCells.NativePrimeIsolation
import Zeta23.OPICARound4.RegularCells.FrozenSourceContinuation

noncomputable section
namespace Zeta23.OPICARound4.PrimeSourceGerms
open CCM RegularCells PrimeSourceLaurent PrimeIsolation Filter
open scoped BigOperators Topology

theorem analyticAt_formalScaledSourceMatrix (Q K : ℕ)
    (X : boundedPrimeSet Q → ℂˣ) (i j : Fin (2*K+1))
    {z : ℂ} (hz : z ∈ complexArchSafeStrip) :
    AnalyticAt ℂ (fun w => formalScaledSourceMatrix Q w X K i j) z := by
  have ha := analyticOnNhd_complexCanonicalArchWithoutWMatrix_apply_strip K i j z hz
  have hp := analyticAt_scaledFrozenPrimeMatrix Q (fun q => integerFormalPhase Q q X) K i j z
  exact (analyticAt_id.neg.mul ha).sub hp

theorem analyticAt_rawPhysicalDiagonal (K : ℕ) (i j : Fin (2*K+1)) (z : ℂ) :
    AnalyticAt ℂ (fun w => rawPhysicalDiagonal K w i j) z := by
  simp only [rawPhysicalDiagonal,Matrix.diagonal_apply]
  split_ifs <;> fun_prop

private theorem analyticAt_matrix_mul {m n k : Type*} [Fintype n]
    (A : ℂ → Matrix m n ℂ) (B : ℂ → Matrix n k ℂ) (z : ℂ)
    (hA : ∀ i j, AnalyticAt ℂ (fun w => A w i j) z)
    (hB : ∀ i j, AnalyticAt ℂ (fun w => B w i j) z) :
    ∀ i j, AnalyticAt ℂ (fun w => (A w * B w) i j) z := by
  intro i j
  exact Finset.analyticAt_fun_sum Finset.univ (fun l _ => (hA i l).mul (hB l j))

private theorem analyticAt_frameEnergy_of_source {ι : Type*} (Q K : ℕ)
    (C : Matrix (Fin (2*K+1)) ι ℂ) (X : ℂ → boundedPrimeSet Q → ℂˣ) (z : ℂ)
    (hS : ∀ i j, AnalyticAt ℂ (fun w => formalScaledSourceMatrix Q w (X w) K i j) z) :
    ∀ i j, AnalyticAt ℂ (fun w => formalRawFrameEnergy Q K C w (X w) i j) z := by
  have hc : ∀ i j, AnalyticAt ℂ (fun (_ : ℂ) => C i j) z := fun _ _ => analyticAt_const
  have hct : ∀ i j, AnalyticAt ℂ (fun (_ : ℂ) => C.conjTranspose i j) z :=
    fun _ _ => analyticAt_const
  exact analyticAt_matrix_mul _ _ z
    (analyticAt_matrix_mul _ _ z
      (analyticAt_matrix_mul _ _ z
        (analyticAt_matrix_mul _ _ z hct (fun i j => analyticAt_rawPhysicalDiagonal K i j z)) hS)
      (fun i j => analyticAt_rawPhysicalDiagonal K i j z)) hc

theorem analyticAt_formalRawFrameGram {ι : Type*} (K : ℕ)
    (C : Matrix (Fin (2*K+1)) ι ℂ) (z : ℂ) :
    ∀ i j, AnalyticAt ℂ (fun w => formalRawFrameGram K C w i j) z := by
  have hc : ∀ i j, AnalyticAt ℂ (fun (_ : ℂ) => C i j) z := fun _ _ => analyticAt_const
  have hct : ∀ i j, AnalyticAt ℂ (fun (_ : ℂ) => C.conjTranspose i j) z :=
    fun _ _ => analyticAt_const
  exact analyticAt_matrix_mul _ _ z
    (analyticAt_matrix_mul _ _ z
      (analyticAt_matrix_mul _ _ z hct (fun i j => analyticAt_rawPhysicalDiagonal K i j z))
      (fun i j => analyticAt_rawPhysicalDiagonal K i j z)) hc

private theorem analyticAt_frameSylvesterDet_of_source {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (Q K : ℕ)
    (Ce : Matrix (Fin (2*K+1)) ι ℂ) (Co : Matrix (Fin (2*K+1)) κ ℂ)
    (X : ℂ → boundedPrimeSet Q → ℂˣ) (z : ℂ)
    (hS : ∀ i j, AnalyticAt ℂ (fun w => formalScaledSourceMatrix Q w (X w) K i j) z) :
    AnalyticAt ℂ (fun w => (formalRawFrameSylvester Q K Ce Co w (X w)).det) z := by
  have he := analyticAt_frameEnergy_of_source Q K Ce X z hS
  have ho := analyticAt_frameEnergy_of_source Q K Co X z hS
  have hge := analyticAt_formalRawFrameGram K Ce z
  have hgo := analyticAt_formalRawFrameGram K Co z
  have hm (i j : κ × ι) :
      AnalyticAt ℂ (fun w => formalRawFrameSylvester Q K Ce Co w (X w) i j) z :=
    ((ho i.1 j.1).mul (hge j.2 i.2)).sub ((hgo i.1 j.1).mul (he j.2 i.2))
  simp_rw [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply analyticAt_const.mul
  exact Finset.analyticAt_fun_prod Finset.univ (fun i _ => hm (σ i) i)

theorem analyticAt_formalRawFrameSylvesterDet {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (Q K : ℕ)
    (Ce : Matrix (Fin (2*K+1)) ι ℂ) (Co : Matrix (Fin (2*K+1)) κ ℂ)
    (X : boundedPrimeSet Q → ℂˣ) {z : ℂ} (hz : z ∈ complexArchSafeStrip) :
    AnalyticAt ℂ (fun w => (formalRawFrameSylvester Q K Ce Co w X).det) z :=
  analyticAt_frameSylvesterDet_of_source Q K Ce Co (fun _ => X) z
    (fun i j => analyticAt_formalScaledSourceMatrix Q K X i j hz)

theorem actual_sylvester_germ_nonzero_of_formal_anchor {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (Q K : ℕ)
    (Ce : Matrix (Fin (2*K+1)) ι ℂ) (Co : Matrix (Fin (2*K+1)) κ ℂ)
    (X : boundedPrimeSet Q → ℂˣ)
    (h0 : (formalRawFrameSylvester Q K Ce Co 0 X).det ≠ 0) :
    ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      (formalRawFrameSylvester Q K Ce Co z (primePhaseUnits (boundedPrimeSet Q) z)).det = 0 := by
  apply HasPrimeLaurentExpansion.actual_germ_nonzero (boundedPrimeSet_prime Q)
    (formalRawFrameSylvester_det_expansion Q K Ce Co) (fun _ => X)
  have h := (analyticAt_formalRawFrameSylvesterDet Q K Ce Co X (by simp : (0 : ℂ) ∈ complexArchSafeStrip)).continuousAt.eventually_ne h0
  have hp : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (formalRawFrameSylvester Q K Ce Co z X).det ≠ 0 :=
    h.filter_mono nhdsWithin_le_nhds
  intro hz
  obtain ⟨z,hzn,hzz⟩ := (hp.and hz).exists
  exact hzn hzz

theorem formalScaledSourceMatrix_single_zero (Q K : ℕ) (p : boundedPrimeSet Q)
    (hQ : Q < p.val^2) (theta : ℝ) :
    formalScaledSourceMatrix Q 0
      (singlePrimePhase (boundedPrimeSet Q) p (circlePhase theta)) K =
        (isolatedPrimeCoefficient p.val : ℂ) •
          (Matrix.diagonal (fun i : Fin (2*K+1) =>
            (Real.cos ((centeredIndex K i : ℝ)*theta) : ℂ)) - 1) := by
  have hp := boundedPrimeSet_prime Q p.val p.property
  have hpQ : p.val ≤ Q := by
    have hh := (Finset.mem_filter.mp p.property).1
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hh)
  have hExp (q : ℕ) : integerFormalExponent Q q =
      (fun r : boundedPrimeSet Q => (q.factorization r.val : ℤ)) := rfl
  simpa only [formalScaledSourceMatrix,neg_zero,zero_smul,zero_sub,
    factoredScaledPrimeMatrix,integerFormalPhase,hExp] using
    neg_scaledFrozen_single_zero Q (boundedPrimeSet Q) p hp hpQ hQ theta K

theorem analyticAt_primeCommonScalar (Q : ℕ) {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ (primeCommonScalar Q) z := by
  unfold primeCommonScalar
  apply Finset.analyticAt_fun_sum
  intro q hq
  exact analyticAt_const.mul (analyticAt_const.mul
    (analyticAt_const.sub (analyticAt_const.div analyticAt_id hz)))

theorem analyticOnNhd_actualScaledSourceMatrix (Q K : ℕ)
    (i j : Fin (2*K+1)) :
    AnalyticOnNhd ℂ (fun z => formalScaledSourceMatrix Q z
      (primePhaseUnits (boundedPrimeSet Q) z) K i j) complexFrozenSourceDomain := by
  intro z hz
  have hz0 : z ≠ 0 := by simpa using hz.2
  have ha := analyticOnNhd_complexCanonicalArchWithoutWMatrix_apply_sourceDomain K i j z hz
  have hp := analyticOnNhd_complexFrozenCanonicalPrimeMatrix_apply_sourceDomain Q K i j z hz
  have hc := analyticAt_primeCommonScalar Q hz0
  have hh : AnalyticAt ℂ (fun w => w *
      (-complexCanonicalArchWithoutWMatrix w K i j - complexFrozenCanonicalPrimeMatrix Q w K i j +
        primeCommonScalar Q w * (1 : Matrix (Fin (2*K+1)) (Fin (2*K+1)) ℂ) i j)) z :=
    analyticAt_id.mul ((ha.neg.sub hp).add (hc.mul analyticAt_const))
  apply hh.congr
  filter_upwards [eventually_ne_nhds hz0] with w hw
  rw [formalScaledSourceMatrix_eq Q K hw,formalWFreeSourceMatrix_actual]
  rfl

theorem analyticOnNhd_actualRawFrameSylvesterDet {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (Q K : ℕ)
    (Ce : Matrix (Fin (2*K+1)) ι ℂ) (Co : Matrix (Fin (2*K+1)) κ ℂ) :
    AnalyticOnNhd ℂ (fun z => (formalRawFrameSylvester Q K Ce Co z
      (primePhaseUnits (boundedPrimeSet Q) z)).det) complexFrozenSourceDomain := by
  intro z hz
  exact analyticAt_frameSylvesterDet_of_source Q K Ce Co
    (primePhaseUnits (boundedPrimeSet Q)) z
    (fun i j => analyticOnNhd_actualScaledSourceMatrix Q K i j z hz)

theorem exists_actual_sylvester_nonzero_in_open_positive_of_anchor {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (Q K : ℕ)
    (Ce : Matrix (Fin (2*K+1)) ι ℂ) (Co : Matrix (Fin (2*K+1)) κ ℂ)
    (X : boundedPrimeSet Q → ℂˣ)
    (h0 : (formalRawFrameSylvester Q K Ce Co 0 X).det ≠ 0)
    {J : Set ℝ} (hJopen : IsOpen J) (hJne : J.Nonempty) (hJpos : J ⊆ Set.Ioi 0) :
    ∃ L ∈ J, (formalRawFrameSylvester Q K Ce Co (L : ℂ)
      (primePhaseUnits (boundedPrimeSet Q) (L : ℂ))).det ≠ 0 :=
  exists_source_nonzero_in_open_positive_of_germ _
    (analyticOnNhd_actualRawFrameSylvesterDet Q K Ce Co)
    (actual_sylvester_germ_nonzero_of_formal_anchor Q K Ce Co X h0)
    hJopen hJne hJpos

end Zeta23.OPICARound4.PrimeSourceGerms
