import Zeta23.OPICARound6.PrimeFactorPaths.NativeCells
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Tactic.NormNum.NatSqrt

namespace Zeta23.OPICARound6.PrimeFactorPaths.NativeGeometry
open Zeta23.OPICARound6.PrimeFactorPaths.NativeCells

/-- On opposite sides of 2^16 the generator changes its roughness but keeps its base shift. -/
theorem square_log_boundary :
    roughCutoff (2^16) = 256 ∧ roughCutoff (2^16+1) = 289 ∧
    baseShift (2^16+1) = 4 ∧ width (2^16+1) 16 0 = 4096 ∧
    ¬completeShell (2^16+1) 16 := by
  have hlog : ((2:ℕ)^16+1).log2 = 16 := by decide
  have hs : baseShift (2^16+1) = 4 := by
    unfold baseShift
    rw [hlog]
    norm_num
  refine ⟨by decide, by decide, hs, ?_, ?_⟩
  · unfold width
    rw [hs]
    decide
  · unfold completeShell
    decide

private theorem whole_of_label (X n k : ℕ) (ht : n ∈ terminalLabels X)
    (hl : k + baseShift X ≤ n.log2) (hc : coarse X (keyOf X n k))
    (hw : completeShell X n.log2) : keyOf X n k ∈ wholeCoarseKeys X := by
  classical
  apply Finset.mem_filter.mpr
  exact ⟨(mem_occupiedKeys X _).mpr ⟨n,(mem_rawLabels X _ n).mpr ⟨ht, hl, rfl⟩⟩, hc, hw⟩

-- Keep elaboration of the large witness symbolic. Its primality and every grid index
-- are computed by the kernel; the exponentially long finite set is never enumerated.
attribute [local irreducible] terminalLabels wholeCoarseKeys
/-- A genuine prime label lies in an occupied coarse base of a complete terminal shell. -/
theorem mersenne_whole_base :
    keyOf (2^127) (mersenne 127) 0 ∈ wholeCoarseKeys (2^127) := by
  have hp : (mersenne 127).Prime :=
    lucas_lehmer_sufficiency _ (by simp) (by norm_num)
  have ht : mersenne 127 ∈ terminalLabels (2^127) := by
    rw [mem_terminalLabels]
    refine ⟨by decide, by decide, hp.squarefree, ?_⟩
    rw [hp.primeFactors]
    intro p h
    have heq := Finset.mem_singleton.mp h
    subst p
    decide
  have hlog : ((2:ℕ)^127).log2 = 127 := by decide
  have hj : (mersenne 127).log2 = 126 := by decide
  have hs : baseShift (2^127) = 12 := by
    unfold baseShift
    rw [hlog]
    norm_num
  have hl : 0 + baseShift (2^127) ≤ (mersenne 127).log2 := by
    rw [hs,hj]
    decide
  have hc : coarse (2^127) (keyOf (2^127) (mersenne 127) 0) := by
    change 2*0 < (mersenne 127).log2 - baseShift (2^127)
    rw [hs,hj]
    decide
  have hw : completeShell (2^127) (mersenne 127).log2 := by
    rw [hj]
    unfold completeShell
    decide
  exact whole_of_label (2^127) (mersenne 127) 0 ht hl hc hw

end Zeta23.OPICARound6.PrimeFactorPaths.NativeGeometry
