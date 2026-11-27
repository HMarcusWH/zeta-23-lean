/-
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
Adapted from the Alpoge/Claude/Anthropic proof, lsernau/grh-lean,
commit 72fead102f663d5c7a407964a13dc0cf9d977207.
Modified: relocated module imports into Zeta23Arithmetic; declarations and
proof bodies retained. ArithmeticOnly additionally omits the final endpoints.
Original license, notice, and attribution in this directory tree.
-/
import Zeta23Arithmetic.Lib.Weil.Construction.FockThetaFunctions
import Zeta23Arithmetic.Lib.CM.FormalGroup.FormalHeight
import Zeta23Arithmetic.Lib.LocalGL.Green.LabelIdempotents
import Zeta23Arithmetic.Lib.SiegelWeil.Formula.ZeroTermHeight
import Zeta23Arithmetic.Lib.ClassField.HeckeCharacter.LevelModulus
import Zeta23Arithmetic.Lib.Cohomology.Etale.TestRings

/-! Part of: Abstract Hecke operators of a pair (G,K), level eigenspaces, weighted class sums (known
result; see Lib.Adelic.Hecke.ClassMean).

This file: Class sums stay integral after clearing automorphism orders; triangle inequality for
their norms. -/


open NumberField HasFiniteType Nat
variable {E V} [Field E] [CMType E] [Fintype V] {p} [Fact (Nat.Prime p)] {κ : InfinitePlace E → _}
  {G} [Group G] [TopologicalSpace G] {Γ K} [@HasFiniteType G _ Γ K _] {B} {f : G →
  WeylIndex V κ → ℂ}

lemma weylGauge_classSum_le_one g {e A} [PadicPlace p] (hA : ∀ x,
  Nat.card (classAut Γ K x) ∣ A) {c : ℂ} (h : ∀ x, weylGauge κ e g (c • f x) ≤ 1) : weylGauge κ e g
  ((A * c) • classSum Γ K f) ≤ 1 := by simpa [mul_smul,
  cast_smul_eq_nsmul] using! smul_classSum_mem (AddSubmonoid.mk ⟨{x | weylGauge .. ≤ 1},
  by simp_all [weylGauge, (IsUltrametricDist.norm_add_le_max ..).trans]⟩ (by simp [weylGauge])) hA h

lemma sqrt_weylNormSq_classSum_le (σ : ℂ ≃+* ℂ) (h : ∀ x, √(weylNormSq (σ ∘ f x)) ≤
  B) : √(weylNormSq (σ ∘ classSum Γ K f)) ≤ Nat.card (DoubleCosets Γ K) * B := by
  simp [classSum]; grw [sqrt_weylNormSq_sum_le]
  simp [← algebraMap_smul ℂ]; grw [cast_inv_le_one, h]; simp
