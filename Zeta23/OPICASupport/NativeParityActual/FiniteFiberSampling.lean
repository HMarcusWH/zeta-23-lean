import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Card

/-!
Finite-fiber maps preserve infinite images. Choosing representatives in that
image produces samples with distinct mapped coordinates while avoiding any
finite set of forbidden values. This does not infer mapped injectivity from
ordinary distinctness of an arbitrary previously chosen family.
-/

noncomputable section

namespace Zeta23.OPICARound21.NativeParityActual

theorem infinite_image_of_finite_fibers {α β : Type*} (f : α → β)
    [Filter.TendstoCofinite f] {s : Set α} (hs : s.Infinite) :
    (f '' s).Infinite := by
  intro h
  apply hs
  exact (Filter.TendstoCofinite.finite_preimage f h).subset (fun x hx => ⟨x, hx, rfl⟩)

theorem exists_samples_with_distinct_images {α β : Type*} (f : α → β)
    [Filter.TendstoCofinite f] {s : Set α} (hs : s.Infinite)
    (bad : Set β) (hbad : bad.Finite) (n : ℕ) :
    ∃ x : Fin n → α, (∀ j, x j ∈ s) ∧ Function.Injective (fun j => f (x j)) ∧
      ∀ j, f (x j) ∉ bad := by
  classical
  let e := Set.Infinite.natEmbedding ((f '' s) \ bad)
    ((infinite_image_of_finite_fibers f hs).sdiff hbad)
  have hw (j : Fin n) : ∃ x, x ∈ s ∧ f x = (e j).val := (e j).property.1
  choose x hx hfx using hw
  refine ⟨x, hx, ?_, ?_⟩
  · intro i j hij
    apply Fin.val_injective
    apply e.injective
    apply Subtype.ext
    rw [← hfx i, ← hfx j]
    exact hij
  · intro j
    rw [hfx j]
    exact (e j).property.2

end Zeta23.OPICARound21.NativeParityActual
