import Zeta23.ZeroSide
import Zeta23.ExceptionalZero.Defs

noncomputable section

namespace Zeta23.ExceptionalZero

open Matrix
open scoped ComplexOrder BigOperators

/-! # The negative-index channel: off-line pairs versus on-line configurations

Route R002 asks for information that separates a tight off-line pair from an
on-line double in a theorem-relevant way **not** reducible to the data visible
to the `TightMult` certificate (trace, Frobenius norm, on-line integer atoms,
positive index; `Zeta23.ZeroSide.TightMult.lemmaR_tight_two`, obstruction
OBS-001).

This file supplies that separation at the level of one zero block, in the form
of a *forbidden direction*.

`Zeta23.ZeroSide.ZeroBlockData.pair_term` proves that an off-line pair
`{ρ, 1−ρ̄}` contributes to the windowed zero-side matrix exactly
`2m • (x xᵀ) − 2m • (y yᵀ)`, where `u = x + iy` is the probe-response vector of
`ρ` and `y = 0` precisely for on-line zeros (`star_v_of_onLine`).  Everything
else in the decomposition `blockA_decomp` is positive semidefinite.

The two theorems below are exactly the discriminating pair:

* `dotProduct_pairBlock_orthoWitness` computes the quadratic form of such a
  block at an explicit witness vector and finds the value
  `-c * (gramDet x y)^2` — strictly negative as soon as `x` and `y` are
  linearly independent;
* `dotProduct_nonneg_of_onLineCombination` shows every nonnegatively weighted
  sum of real rank-one blocks — i.e. every on-line configuration, and also the
  extremal mock `Q` used by `lemmaR_tight` — admits no such direction.

No RH implication is asserted here, and no claim is made that this block-level
separation survives the on-line bulk in a full window; the masking question is
recorded as open in
`research/RHRC/routes/R002_multi_probe/MULTI_PROBE_GRAM_OPERATOR_FEASIBILITY_2026_08_21.md`.
-/

variable {d : Type*} [Fintype d]

/-- The exact off-line pair block of `ZeroSide.ZeroBlockData.pair_term`:
`c • x xᵀ − c • y yᵀ` with `c = 2 m_ρ ≥ 0`. -/
def pairBlock (c : ℝ) (x y : d → ℂ) : Matrix d d ℂ :=
  (c : ℂ) • vecMulVec x x - (c : ℂ) • vecMulVec y y

/-- Gram determinant of the pair `(x, y)`: `⟨x,x⟩⟨y,y⟩ − ⟨x,y⟩²`.  For real
vectors it is nonnegative, and it vanishes exactly when `x` and `y` are
linearly dependent (Cauchy–Schwarz). -/
def gramDet (x y : d → ℂ) : ℂ :=
  (x ⬝ᵥ x) * (y ⬝ᵥ y) - (x ⬝ᵥ y) * (x ⬝ᵥ y)

/-- The component of `y` transverse to `x`, cleared of denominators:
`⟨x,x⟩ • y − ⟨x,y⟩ • x`.  It is orthogonal to `x` unconditionally. -/
def orthoWitness (x y : d → ℂ) : d → ℂ :=
  (x ⬝ᵥ x) • y - (x ⬝ᵥ y) • x

theorem dotProduct_orthoWitness_left (x y : d → ℂ) :
    x ⬝ᵥ orthoWitness x y = 0 := by
  unfold orthoWitness
  rw [dotProduct_sub, dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

theorem dotProduct_orthoWitness_right (x y : d → ℂ) :
    y ⬝ᵥ orthoWitness x y = gramDet x y := by
  unfold orthoWitness gramDet
  rw [dotProduct_sub, dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [dotProduct_comm y x]

/-- Dot products of real vectors are real. -/
theorem star_dotProduct_of_star {x y : d → ℂ} (hx : star x = x) (hy : star y = y) :
    star (x ⬝ᵥ y) = x ⬝ᵥ y := by
  rw [← star_dotProduct_star, hx, hy, dotProduct_comm]

/-- The witness is a real vector whenever `x` and `y` are. -/
theorem star_orthoWitness {x y : d → ℂ} (hx : star x = x) (hy : star y = y) :
    star (orthoWitness x y) = orthoWitness x y := by
  unfold orthoWitness
  rw [star_sub, star_smul, star_smul, hx, hy,
    star_dotProduct_of_star hx hx, star_dotProduct_of_star hx hy]

/-- Quadratic form of a rank-one block at an arbitrary vector. -/
theorem dotProduct_smul_vecMulVec (c : ℝ) (v w : d → ℂ) :
    star w ⬝ᵥ (((c : ℂ) • vecMulVec v v) *ᵥ w) = (c : ℂ) * ((star w ⬝ᵥ v) * (v ⬝ᵥ w)) := by
  rw [Matrix.smul_mulVec, vecMulVec_mulVec, dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

/-- **Forbidden direction of an off-line pair block.**  At the explicit witness
`orthoWitness x y`, the exact pair block `c • x xᵀ − c • y yᵀ` takes the value
`-c · (gramDet x y)²`.

For a genuine off-line zero (`c = 2 m_ρ > 0`, `x` and `y` real and linearly
independent, so `gramDet x y ≠ 0`) this is *strictly negative*: the block has a
direction on which its Hermitian form is negative.  Compare
`dotProduct_nonneg_of_onLineCombination`. -/
theorem dotProduct_pairBlock_orthoWitness {x y : d → ℂ}
    (hx : star x = x) (hy : star y = y) (c : ℝ) :
    star (orthoWitness x y) ⬝ᵥ (pairBlock c x y *ᵥ orthoWitness x y) =
      -(c : ℂ) * (gramDet x y * gramDet x y) := by
  set w := orthoWitness x y with hw
  have hstar : star w = w := star_orthoWitness hx hy
  unfold pairBlock
  rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_smul_vecMulVec,
    dotProduct_smul_vecMulVec, hstar]
  have h1 : w ⬝ᵥ x = 0 := by
    rw [dotProduct_comm w x, hw]
    exact dotProduct_orthoWitness_left x y
  have h2 : w ⬝ᵥ y = gramDet x y := by
    rw [dotProduct_comm w y, hw]
    exact dotProduct_orthoWitness_right x y
  have h3 : y ⬝ᵥ w = gramDet x y := by
    rw [dotProduct_comm y w]
    exact h2
  rw [h1, h2, h3]
  ring

/-- The value is a strictly negative real when the pair is genuinely off-line:
positive weight and linearly independent real parts. -/
theorem dotProduct_pairBlock_orthoWitness_neg {x y : d → ℂ}
    (hx : star x = x) (hy : star y = y) {c : ℝ} (hc : 0 < c)
    (hindep : gramDet x y ≠ 0) :
    (star (orthoWitness x y) ⬝ᵥ (pairBlock c x y *ᵥ orthoWitness x y)).re < 0 := by
  rw [dotProduct_pairBlock_orthoWitness hx hy c]
  have hgr : star (gramDet x y) = gramDet x y := by
    unfold gramDet
    rw [star_sub, star_mul, star_mul, star_dotProduct_of_star hx hx,
      star_dotProduct_of_star hy hy, star_dotProduct_of_star hx hy]
    ring
  have hreal : (gramDet x y).im = 0 := by
    have := Complex.conj_eq_iff_im.mp hgr
    exact this
  have hsq : ((gramDet x y) * (gramDet x y)).re = ((gramDet x y).re) ^ 2 := by
    simp [Complex.mul_re, hreal]
    ring
  have hne : (gramDet x y).re ≠ 0 := by
    intro h
    exact hindep (Complex.ext h hreal)
  rw [show (-(c : ℂ) * (gramDet x y * gramDet x y)) =
      -((c : ℂ) * (gramDet x y * gramDet x y)) by ring]
  rw [Complex.neg_re, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hsq]
  have : 0 < c * ((gramDet x y).re) ^ 2 := by positivity
  linarith

/-- **No forbidden direction in an on-line world.**  Any nonnegatively weighted
sum of rank-one blocks built from *real* vectors — which is exactly the shape of
the on-line contribution `onPart + rePart` of
`ZeroSide.ZeroBlockData.blockA_decomp`, and also of the extremal mock `Q` of
`TightMult.lemmaR_tight` — has nonnegative Hermitian form in every direction.

Together with `dotProduct_pairBlock_orthoWitness_neg` this separates a visible
off-line pair from every on-line configuration by a quantity the `TightMult`
data cannot express. -/
theorem dotProduct_nonneg_of_onLineCombination {ι : Type*} (s : Finset ι)
    (cc : ι → ℝ) (v : ι → d → ℂ) (hcc : ∀ i ∈ s, 0 ≤ cc i)
    (hv : ∀ i ∈ s, star (v i) = v i) (w : d → ℂ) :
    0 ≤ (star w ⬝ᵥ ((∑ i ∈ s, (cc i : ℂ) • vecMulVec (v i) (v i)) *ᵥ w)).re := by
  have hpsd : (∑ i ∈ s, (cc i : ℂ) • vecMulVec (v i) (v i)).PosSemidef := by
    refine Matrix.posSemidef_sum _ fun i hi => ?_
    exact Zeta23.ZeroSide.ZeroBlockData.posSemidef_smul_vecMulVec (hv i hi) (hcc i hi)
  exact hpsd.re_dotProduct_nonneg w

/-- **The separation.**  A block carrying a forbidden direction is not equal to
any nonnegatively weighted sum of real rank-one blocks.  Instantiated at the
off-line pair block of `ZeroSide.ZeroBlockData.pair_term`, this says a visible
off-line pair cannot be reproduced by *any* on-line configuration — including an
on-line double zero and the extremal mock of `TightMult.lemmaR_tight`, both of
which are of that shape.

This is `R002_MULTI_PROBE_SEPARATION` at block level: the separating quantity is
the sign of a Hermitian form in one direction, which is not a function of the
trace / Frobenius / on-line-atom / positive-index data of OBS-001. -/
theorem not_onLineCombination_of_pairBlock {x y : d → ℂ}
    (hx : star x = x) (hy : star y = y) {c : ℝ} (hc : 0 < c)
    (hindep : gramDet x y ≠ 0) {ι : Type*} (s : Finset ι) (cc : ι → ℝ)
    (v : ι → d → ℂ) (hcc : ∀ i ∈ s, 0 ≤ cc i) (hv : ∀ i ∈ s, star (v i) = v i) :
    pairBlock c x y ≠ ∑ i ∈ s, (cc i : ℂ) • vecMulVec (v i) (v i) := by
  intro hEq
  have hneg := dotProduct_pairBlock_orthoWitness_neg hx hy hc hindep
  rw [hEq] at hneg
  exact absurd hneg (not_lt.mpr
    (dotProduct_nonneg_of_onLineCombination s cc v hcc hv (orthoWitness x y)))

end Zeta23.ExceptionalZero
