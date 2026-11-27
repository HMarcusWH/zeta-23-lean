/-
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
Adapted from the Alpoge/Claude/Anthropic proof, lsernau/grh-lean,
commit 72fead102f663d5c7a407964a13dc0cf9d977207.
Modified: relocated module imports into Zeta23Arithmetic; declarations and
proof bodies retained. ArithmeticOnly additionally omits the final endpoints.
Original license, notice, and attribution in this directory tree.
-/
import Zeta23Arithmetic.Lib.Adelic.Adeles.CoprimeValuation

/-! General lemmas of algebraic number theory (textbook or folklore).

This file: Complex embeddings of a totally complex field come in conjugate pairs. -/

open NumberField Polynomial ComplexEmbedding InfinitePlace Finset IsTotallyComplex


variable {E} [Field E] [IsTotallyComplex E]

@[simp, grind] lemma conjugate_ne_self σ : @conjugate E _ σ ≠ σ := complexEmbedding_not_isReal _

@[to_additive] lemma prod_embeddings_eq_prod_pairs [NumberField E]
  [PlaceEmbedding E] {M} [CommMonoid M] (F : (E →+* ℂ) → M) : ∏ σ, F σ = ∏ v, F (Φ v) * F (conjugate
  (Φ v)) := prod_fiberwise _ mk F ▸ by congr!; apply prod_eq_mul <;> grind [mk_Φ, mk_eq_iff]

omit [IsTotallyComplex E] in
lemma roots_map_conjugate (P : E[X]) σ : (P.map (conjugate σ)).roots = (P.map σ).roots.map star :=
  (P.map_map ..).rec ((IsAlgClosed.splits _).roots_map _)
