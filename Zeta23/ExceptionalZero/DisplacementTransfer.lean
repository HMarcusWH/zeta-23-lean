import Zeta23.ZeroSide
import Zeta23.ExceptionalZero.Defs

noncomputable section

namespace Zeta23.ExceptionalZero

open Matrix

set_option linter.unusedSectionVars false

/-! # Displacement transfer under a diagonal shift

Route R003 asks for an exact identity, intertwiner, or controlled limit
connecting a finite CCM object to a Weil/aperture object.

The R004 finite CCM matrix `M` satisfies the algebraically closed displacement
identity `D * M - M * D = g 1ᵀ - 1 gᵀ` for the index operator
`D = diag(-N, …, N)` and an explicit vector `g`, hence its displacement has rank
at most two.  The R002 diagnostic
(`research/RHRC/routes/R003_ccm_bridge/check_diagonal_shift.py`) then found,
numerically, that `M` and the Weil explicit-formula Gram of the truncated
character family differ only by a scalar multiple of the identity — the pole and
prime channels agree exactly (factor 2), and the archimedean channels differ
only through the regularization constant attached to `K(0)`, which vanishes off
the diagonal.

This file proves the *algebra* that makes such a comparison useful, and nothing
else: a displacement is unchanged by adding a scalar matrix, so any relation of
the displayed form transfers verbatim, together with its rank bound.

Nothing here asserts that the numerically observed relation actually holds: the
hypothesis is carried explicitly by every statement.  In particular no claim is
made about ζ, and no explicit formula is invoked (the truncated character
correlation is only piecewise `C¹`, hence not an admissible `C_c²` Weil test —
see the route README). -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The displacement of `M` with respect to `D`: the commutator `DM - MD`. -/
def displacement (D M : Matrix ι ι ℂ) : Matrix ι ι ℂ := D * M - M * D

/-- Scalar matrices are invisible to a displacement: `⁅D, M + c•1⁆ = ⁅D, M⁆`.
This is the whole reason a diagonal-shift comparison is useful. -/
theorem displacement_add_scalar (D M : Matrix ι ι ℂ) (c : ℂ) :
    displacement D (M + c • (1 : Matrix ι ι ℂ)) = displacement D M := by
  unfold displacement
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul]
  abel

/-- A displacement is linear in its second argument. -/
theorem displacement_smul (D M : Matrix ι ι ℂ) (k : ℂ) :
    displacement D (k • M) = k • displacement D M := by
  unfold displacement
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

/-- A scaled antisymmetric rank-one difference `k • (g uᵀ - u gᵀ)` has rank at
most two. -/
theorem rank_smul_vecMulVec_sub_le_two (k : ℂ) (g u : ι → ℂ) :
    (k • (vecMulVec g u - vecMulVec u g)).rank ≤ 2 := by
  have h : k • (vecMulVec g u - vecMulVec u g)
      = k • vecMulVec g u + (-k) • vecMulVec u g := by
    rw [neg_smul, smul_sub]
    abel
  rw [h]
  refine le_trans (Zeta23.ZeroSide.rank_add_le _ _) ?_
  have h1 : (k • vecMulVec g u).rank ≤ 1 :=
    Zeta23.ZeroSide.rank_smul_vecMulVec_le _ _ _
  have h2 : ((-k) • vecMulVec u g).rank ≤ 1 :=
    Zeta23.ZeroSide.rank_smul_vecMulVec_le _ _ _
  omega

/-- A matrix of the form `g uᵀ - u gᵀ` has rank at most two. -/
theorem rank_vecMulVec_sub_le_two (g u : ι → ℂ) :
    (vecMulVec g u - vecMulVec u g).rank ≤ 2 := by
  simpa using rank_smul_vecMulVec_sub_le_two (1 : ℂ) g u

/-- **Displacement transfer.**  If `A` differs from `M` by a scaling and a
scalar shift, and `M` has the R004 displacement structure, then `A` has the same
structure up to that scaling — in particular its displacement still has rank at
most two.

Applied with `A` the Weil Gram, `k = 2` and `c = c(L)`, this is exactly the
step that would carry R004's exact identity onto the Weil quadratic form.  The
hypothesis `hA` is supplied by nothing in this file; it is an assumption. -/
theorem displacement_eq_of_eq_smul_add_scalar
    {D M A : Matrix ι ι ℂ} {g u : ι → ℂ} {k c : ℂ}
    (hA : A = k • M + c • (1 : Matrix ι ι ℂ))
    (hM : displacement D M = vecMulVec g u - vecMulVec u g) :
    displacement D A = k • (vecMulVec g u - vecMulVec u g) := by
  rw [hA, displacement_add_scalar, displacement_smul, hM]

/-- The rank bound survives the transfer. -/
theorem rank_displacement_le_two_of_eq_smul_add_scalar
    {D M A : Matrix ι ι ℂ} {g u : ι → ℂ} {k c : ℂ}
    (hA : A = k • M + c • (1 : Matrix ι ι ℂ))
    (hM : displacement D M = vecMulVec g u - vecMulVec u g) :
    (displacement D A).rank ≤ 2 := by
  rw [displacement_eq_of_eq_smul_add_scalar hA hM]
  exact rank_smul_vecMulVec_sub_le_two k g u

end Zeta23.ExceptionalZero
