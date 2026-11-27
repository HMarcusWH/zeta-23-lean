/-
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
Adapted from the Alpoge/Claude/Anthropic proof, lsernau/grh-lean,
commit 72fead102f663d5c7a407964a13dc0cf9d977207.
Modified: relocated module imports into Zeta23Arithmetic; declarations and
proof bodies retained. ArithmeticOnly additionally omits the final endpoints.
Original license, notice, and attribution in this directory tree.
-/
import Zeta23Arithmetic.Lib.Weil.DualPair.PairReal
import Zeta23Arithmetic.Lib.ClassField.HeckeCharacter.LineParabolic

/-! Part of: Algebraic Hecke characters (type A₀); extension of the quadratic character of a CM
field (known result; see Lib.ClassField.HeckeCharacter.SplittingCharExists).

This file: Tame Hecke character on determinants of integral adelic points is product of residue
characters. -/

namespace AutChar.HasWeight

open Matrix Prod IsIntMatrix
variable {E n} [Field E] [CMType E] [Fintype n] {μ : AutChar E} {e ψ} {s : n → _}

/-- Let μ have weight e and tame part ψ, trivial outside finitely many distinct places w_i. For
k in the stabiliser K₀ of the standard lattice, μ(det k) = ∏_i ψ_{w_i}(det(k mod w_i)). -/
lemma apply_det_eq_prod (h : μ.HasWeight e ψ) {ι} [Fintype ι] {w : ι → _} (hw : w.Injective) (hψ :
  ∀ u ∉ Set.range w, ψ u = 1) k : μ.1 (detFin s k.1) = ∏ i, ψ (w i) (Kf.reduceAt _ k).1.det := by
  simp +contextual [h.2,
    det_mem (mem_Kf.1 k.2), ↓finprod_tame_eq_prod_reduceU1 (S := .map ⟨w, hw⟩ ⊤), *, reduceU1]
  congr!; convert! RingHom.map_det ..
  simp [det_apply', snd_sum, snd_prod]; rfl

lemma apply_det_eq_one (h : μ.HasWeight e 1) {k} (hk : k ∈ Kf ..) : μ.1 (detFin s k) = 1 := by
  ext; simp [h.2, det_mem (mem_Kf.1 hk), ↓finprod_tame_eq_prod_reduceU1 (S := ∅)]
