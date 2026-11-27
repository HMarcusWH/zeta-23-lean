/-
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
Adapted from the Alpoge/Claude/Anthropic proof, lsernau/grh-lean,
commit 72fead102f663d5c7a407964a13dc0cf9d977207.
Modified: relocated module imports into Zeta23Arithmetic; declarations and
proof bodies retained. ArithmeticOnly additionally omits the final endpoints.
Original license, notice, and attribution in this directory tree.
-/
import Zeta23Arithmetic.Lib.Weil.Construction.Projections

/-! Part of: Bargmann–Fock model of the harmonic (oscillator) representation of U(p,q) (known
result; see Lib.Weil.Fock.OscillatorPair). -/

variable {E n s} [Field E] [CMType E] [WeilData E] [Fintype n] (V : Space E n s) (v w f f')

namespace Space

/-- For v, w in the Fock space and f, f′ in 𝒮(V), ⟨v⊗f, w⊗f′⟩ = ⟨v,w⟩·⟨Pf, Pf′⟩, where
v⊗f = ∫v(y)ϱ(y)f dy over real vectors y and P is this operator for the Gaussian. -/
lemma dataInner_integrated : V.dataInner (V.integrated v f) (V.integrated w f') =
  realInner v w * V.dataInner (V.projReal f) (V.projReal f') := by
    simpa [mul_comm] using
      Heisenberg.IsVacuum.integral_form_eq_mul_modelInner (ν := .dirac ()) (fun _ ↦ .bilinearComp _
    (.flip _ f) (.flip _ f')) (by simp) (by simp [integrated_realHeisOp]) ..

/-- For v in the Fock space and f in 𝒮(V), θ(v ⊗ f) = ∫ v(y) f̃(y) dy, with f̃(x) = θ(ϱ(x)f), y
over real vectors in Fock coordinates with the measure `realMeasure`. -/
lemma theta_integrated : V.θ (V.integrated v f) = ∫ y, v y * f (realVec y) ∂realMeasure
  _ := by simp [integrated, Heisenberg.Rep.map_integrated_eq_integral]
