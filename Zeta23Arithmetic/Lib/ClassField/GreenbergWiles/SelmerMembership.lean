/-
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
Adapted from the Alpoge/Claude/Anthropic proof, lsernau/grh-lean,
commit 72fead102f663d5c7a407964a13dc0cf9d977207.
Modified: relocated module imports into Zeta23Arithmetic; declarations and
proof bodies retained. ArithmeticOnly additionally omits the final endpoints.
Original license, notice, and attribution in this directory tree.
-/
import Zeta23Arithmetic.Lib.Cyclotomic.Stickelberger.GaussSums
import Zeta23Arithmetic.Lib.ClassField.GreenbergWiles.SelmerRelations

/-! Part of: Greenberg–Wiles formula, as a lower bound for the dual side (known result; see
Lib.ClassField.GreenbergWiles.GreenbergWilesBound).

Set-up used by: Greenberg–Wiles formula, as a lower bound for the dual side.

This file: Membership in Selmer groups of cocycles; dropping conditions and places where
unramified. -/


open Matrix.Module
variable {E : Type} {Λ n B} [Field E] [EmbeddedNumberField E] [CommRing Λ] [Fintype n]
  [AddCommGroup B] [Module Λ B] {ρ : Gal(Ω/E) → Matrix n n Λ} {S T L K c}

lemma mem_selmerModule_iff : c ∈ selmerModule ρ S L B ↔ (∀ g h, c (g * h) = c g + ρ g • c h) ∧
  (∀ g ∈ inertiaAbove Sᶜ, c g = 0) ∧ c ∈ obeying L B ∧ IsLocallyConstant
  c := by simp [selmerModule, obeying, ↓iInf_union, ← mem_obeying_cocycleRels]; tauto

/-- A member c of the Selmer module for (S, L) lies in that for (T, K) if K ⊆ L and c vanishes
on inertia at all places of S outside T. -/
lemma selmerModule_mono (k : c ∈ selmerModule ρ S L B) (l : K ⊆ L) (h : ∀ v ∈ S \ T,
  ∀ g ∈ inertiaAbove {v}, c g = 0 := by simp) :
  c ∈ selmerModule ρ T K B := by simp_all [mem_selmerModule_iff, obeying, inertiaAbove]; grind
