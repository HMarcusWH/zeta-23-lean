import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Abel

/-!
# The compressed commutator with every leakage term retained

Let `V` be a coordinate map onto a carrier (for a physical orthonormal basis
`Vᴴ V = 1`; the identities below do not need it), `P = V Vᴴ`, let `D₀` be the
geometry operator (for instance `diag(n²)`) and `E` the source operator, both
self-adjoint. Put `J = Vᴴ D₀ V` (compressed geometry) and `H = Vᴴ E V`
(compressed energy). If the geometry leaks out of the carrier through a
finite-rank map, `(1 - P) D₀ V = W Lᴴ`, then with `Z = Vᴴ E W`

`[J, H] = Vᴴ [D₀, E] V + Z Lᴴ - L Zᴴ`.

The rank-one case `W = w`, `L = ℓ` is the one-normal identity of work package F
(§11.3), with the signed numerator `zᵢ conj(ℓⱼ) - ℓᵢ conj(zⱼ)` retained. The
term `Vᴴ [D₀, E] V` is kept: it may be discarded only after its vanishing on the
actual carrier is proved, which this module does not claim. The commutator
controls neither the diagonal nor the absolute energy, and no sign of the
native source follows from it.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier

open Matrix

variable {N k r : Type*} [Fintype N] [DecidableEq N] [Fintype k] [Fintype r]

/-- The adjoint form of the leakage hypothesis: `Vᴴ D₀ (1 - V Vᴴ) = L Wᴴ`. -/
theorem leakage_adjoint (V : Matrix N k ℂ) (D₀ : Matrix N N ℂ) (W : Matrix N r ℂ) (L : Matrix k r ℂ)
    (hD : D₀ᴴ = D₀) (hleak : (1 - V * Vᴴ) * D₀ * V = W * Lᴴ) :
    Vᴴ * D₀ * (1 - V * Vᴴ) = L * Wᴴ := by
  have h := congrArg conjTranspose hleak
  simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, conjTranspose_conjTranspose, hD] at h
  simpa only [Matrix.mul_assoc] using h

/-- Compressed geometry times compressed energy, with the leakage term exposed. -/
theorem compressed_geometry_mul_energy (V : Matrix N k ℂ) (D₀ E : Matrix N N ℂ) (W : Matrix N r ℂ)
    (L : Matrix k r ℂ) (hD : D₀ᴴ = D₀) (hE : Eᴴ = E) (hleak : (1 - V * Vᴴ) * D₀ * V = W * Lᴴ) :
    (Vᴴ * D₀ * V) * (Vᴴ * E * V) = Vᴴ * D₀ * E * V - L * (Vᴴ * E * W)ᴴ := by
  have h1 := leakage_adjoint V D₀ W L hD hleak
  have hz : (Vᴴ * E * W)ᴴ = Wᴴ * E * V := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hE, Matrix.mul_assoc]
  have hsplit : (Vᴴ * D₀ * V) * (Vᴴ * E * V) = Vᴴ * D₀ * E * V - (Vᴴ * D₀ * (1 - V * Vᴴ)) * E * V := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  rw [hsplit, h1, hz]
  simp only [Matrix.mul_assoc]

/-- Compressed energy times compressed geometry, with the leakage term exposed. -/
theorem compressed_energy_mul_geometry (V : Matrix N k ℂ) (D₀ E : Matrix N N ℂ) (W : Matrix N r ℂ)
    (L : Matrix k r ℂ) (hleak : (1 - V * Vᴴ) * D₀ * V = W * Lᴴ) :
    (Vᴴ * E * V) * (Vᴴ * D₀ * V) = Vᴴ * E * D₀ * V - (Vᴴ * E * W) * Lᴴ := by
  have hsplit : (Vᴴ * E * V) * (Vᴴ * D₀ * V) = Vᴴ * E * D₀ * V - Vᴴ * E * ((1 - V * Vᴴ) * D₀ * V) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [hsplit, hleak]
  simp only [Matrix.mul_assoc]

/-- **Compressed commutator identity.** Every term is retained:
`[Vᴴ D₀ V, Vᴴ E V] = Vᴴ [D₀, E] V + Z Lᴴ - L Zᴴ` with `Z = Vᴴ E W`. -/
theorem compressed_commutator_eq (V : Matrix N k ℂ) (D₀ E : Matrix N N ℂ) (W : Matrix N r ℂ)
    (L : Matrix k r ℂ) (hD : D₀ᴴ = D₀) (hE : Eᴴ = E) (hleak : (1 - V * Vᴴ) * D₀ * V = W * Lᴴ) :
    (Vᴴ * D₀ * V) * (Vᴴ * E * V) - (Vᴴ * E * V) * (Vᴴ * D₀ * V)
      = Vᴴ * (D₀ * E - E * D₀) * V + (Vᴴ * E * W) * Lᴴ - L * (Vᴴ * E * W)ᴴ := by
  rw [compressed_geometry_mul_energy V D₀ E W L hD hE hleak, compressed_energy_mul_geometry V D₀ E W L hleak]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-- The one-normal case (rank-one leakage `w ℓᴴ`), with the signed numerator retained. -/
theorem compressed_commutator_eq_one_normal (V : Matrix N k ℂ) (D₀ E : Matrix N N ℂ)
    (w : Matrix N Unit ℂ) (ℓ : Matrix k Unit ℂ) (hD : D₀ᴴ = D₀) (hE : Eᴴ = E)
    (hleak : (1 - V * Vᴴ) * D₀ * V = w * ℓᴴ) :
    (Vᴴ * D₀ * V) * (Vᴴ * E * V) - (Vᴴ * E * V) * (Vᴴ * D₀ * V)
      = Vᴴ * (D₀ * E - E * D₀) * V + (Vᴴ * E * w) * ℓᴴ - ℓ * (Vᴴ * E * w)ᴴ :=
  compressed_commutator_eq V D₀ E w ℓ hD hE hleak

/-- Without leakage the compressed commutator is exactly the compression of `[D₀, E]`. -/
theorem compressed_commutator_eq_of_no_leakage (V : Matrix N k ℂ) (D₀ E : Matrix N N ℂ)
    (hD : D₀ᴴ = D₀) (hE : Eᴴ = E) (hleak : (1 - V * Vᴴ) * D₀ * V = 0) :
    (Vᴴ * D₀ * V) * (Vᴴ * E * V) - (Vᴴ * E * V) * (Vᴴ * D₀ * V) = Vᴴ * (D₀ * E - E * D₀) * V := by
  have h0 : (1 - V * Vᴴ) * D₀ * V = (0 : Matrix N Unit ℂ) * (0 : Matrix k Unit ℂ)ᴴ := by
    rw [hleak, Matrix.zero_mul]
  rw [compressed_commutator_eq V D₀ E 0 0 hD hE h0]
  simp

end Zeta23.OPICARound4.ArithmeticFrontier
