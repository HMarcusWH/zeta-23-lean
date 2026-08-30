import Zeta23.ZeroSide

noncomputable section

namespace Zeta23.ExceptionalZero

open Matrix
open scoped BigOperators

/-!
# D0-R: R002 taper-grid / CCM representation audit

This module supplies theorem-level firewalls for comparing the generic R002
taper-grid zero-side matrices with the theorem-authoritative finite CCM object.

The purpose is deliberately narrower than a positivity or RH argument:

* distinguish the global R002 zero-side matrix `Gz` from its finite-window
  block `Az = blockA`;
* record that the current production `Params.Valid` envelope excludes the
  exploratory oversampled regime `lambda > 1`;
* provide a response-family change-of-coordinates lemma that any claimed exact
  R002 -> CCM congruence must satisfy.

No theorem in this file identifies the generic taper-grid `Gz` with
`Zeta23.CCM.zeroSideMatrix` or `cutoffFreeMatrix`.
-/

section ResponseMap

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Apply a finite linear coordinate map to a response vector. -/
def mapResponse (C : Matrix β α ℂ) (v : α → ℂ) : β → ℂ :=
  fun i => ∑ j, C i j * v j

@[simp] theorem mapResponse_apply
    (C : Matrix β α ℂ) (v : α → ℂ) (i : β) :
    mapResponse C v i = ∑ j, C i j * v j := rfl

/-- A response-vector coordinate map acts on the symmetric rank-one atom by
ordinary transpose congruence.  R002 uses the symmetric bilinear atom
`vecMulVec v v`, not a Hermitian outer product, so the right factor is
`C.transpose`, not `C.conjTranspose`. -/
theorem vecMulVec_mapResponse
    (C : Matrix β α ℂ) (v : α → ℂ) :
    vecMulVec (mapResponse C v) (mapResponse C v) =
      C * vecMulVec v v * C.transpose := by
  ext i j
  simp only [vecMulVec_apply, mapResponse_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Certificate for an exact response-family change of coordinates.  This is
intentionally stronger than a fitted matrix congruence: the same fixed
coordinate map must carry every response vector in the family. -/
structure ExactResponseMap
    {ι : Type*} (source : ι → α → ℂ) (target : ι → β → ℂ) where
  changeOfBasis : Matrix β α ℂ
  response_eq : ∀ z, target z = mapResponse changeOfBasis (source z)

/-- An exact response-family map automatically gives transpose congruence for
every rank-one response atom. -/
theorem ExactResponseMap.atom_congruence
    {ι : Type*} {source : ι → α → ℂ} {target : ι → β → ℂ}
    (M : ExactResponseMap source target) (z : ι) :
    vecMulVec (target z) (target z) =
      M.changeOfBasis * vecMulVec (source z) (source z) *
        M.changeOfBasis.transpose := by
  rw [M.response_eq z]
  exact vecMulVec_mapResponse M.changeOfBasis (source z)

end ResponseMap

namespace R002CCM

/-- Exact global/window/tail decomposition for the R002 zero-side matrix.
The finite block `Az` used by the off-line-pair decomposition is therefore
not the global `Gz` unless the tail `Ez` vanishes. -/
theorem Gz_eq_Az_add_Ez
    (Z : Zeta23.ZeroConfig) (P : Zeta23.Params) (T : ℝ) :
    Z.Gz P T = Z.Az P T + Z.Ez P T := by
  rw [Zeta23.ZeroConfig.Ez]
  abel

/-- Equality of the global R002 matrix and its finite window is equivalent to
vanishing of the tail matrix.  This is an object-identity firewall for D0-R. -/
theorem Gz_eq_Az_iff_Ez_eq_zero
    (Z : Zeta23.ZeroConfig) (P : Zeta23.Params) (T : ℝ) :
    Z.Gz P T = Z.Az P T ↔ Z.Ez P T = 0 := by
  constructor
  · intro h
    rw [Zeta23.ZeroConfig.Ez, h]
    simp
  · intro h
    rw [Zeta23.ZeroConfig.Ez] at h
    exact sub_eq_zero.mp h

/-- The exploratory oversampled regime `lambda > 1` is outside the current
production R002 validity envelope, whose definition includes `lambda <= 1`. -/
theorem not_valid_of_one_lt_lam
    (P : Zeta23.Params) (h : 1 < P.lam) :
    ¬ P.Valid := by
  intro hP
  linarith [hP.lam_le_one]

/-- The R002 frequency grid is a common carrier `T` plus the lattice offset
`2*pi*k/L`.  This records the translation that must be accounted for by any
purported map to the centered CCM basis. -/
theorem tau_eq_carrier_add_lattice
    (P : Zeta23.Params) (T : ℝ) (k : ℤ) :
    P.tau T k = T + (k : ℝ) * P.hgrid T := rfl

end R002CCM

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.vecMulVec_mapResponse
#print axioms Zeta23.ExceptionalZero.ExactResponseMap.atom_congruence
#print axioms Zeta23.ExceptionalZero.R002CCM.Gz_eq_Az_add_Ez
#print axioms Zeta23.ExceptionalZero.R002CCM.Gz_eq_Az_iff_Ez_eq_zero
#print axioms Zeta23.ExceptionalZero.R002CCM.not_valid_of_one_lt_lam
#print axioms Zeta23.ExceptionalZero.R002CCM.tau_eq_carrier_add_lattice
