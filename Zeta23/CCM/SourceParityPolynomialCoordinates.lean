import Zeta23.CCM.SourceLatticeCoordinates

noncomputable section

namespace Zeta23.CCM

open Matrix Finset
open scoped BigOperators ComplexConjugate

/-!
# POST284-M17: parity-polynomial coordinates on the integer lattice

For a centered coefficient vector `u`, the trigonometric polynomial
`f_u(t) = ∑ u_n e^{int}` is multiplied by `cos t` and `i sin t` through the
lattice operators

* `latticeCos f n = (f (n-1) + f (n+1)) / 2`,
* `latticeSin f n = (f (n-1) - f (n+1)) / 2`.

The even boundary-flat carrier is the image of `(1 - latticeCos)^2` on
symmetric sequences (the coefficient form of `C_u = (1 - cos t)^2 Q(cos t)`)
and the odd boundary-flat carrier is the image of
`latticeSin ∘ (1 - latticeCos)` (the coefficient form of
`T_u = sin t (1 - cos t) Q(cos t)`).

This module proves the operator identities, support propagation, box
adjointness, injectivity on finitely supported sequences, and the carrier
membership of both parametrizations.  The source-form inertia is in
`SourceParityExactInertia`.  No canonical-operator statement is made.
-/

/-! ## Lattice operators -/

/-- Coefficient form of multiplication by `cos t`. -/
def latticeCos (f : ℤ → ℂ) : ℤ → ℂ :=
  fun n => (f (n - 1) + f (n + 1)) / 2

/-- Coefficient form of multiplication by `i sin t`. -/
def latticeSin (f : ℤ → ℂ) : ℤ → ℂ :=
  fun n => (f (n - 1) - f (n + 1)) / 2

/-- Coefficient form of multiplication by `1 - cos t`. -/
def latticeOneSubCos (f : ℤ → ℂ) : ℤ → ℂ :=
  fun n => f n - latticeCos f n

/-- Coefficient form of multiplication by `1 + cos t`. -/
def latticeOnePlusCos (f : ℤ → ℂ) : ℤ → ℂ :=
  fun n => f n + latticeCos f n

/-- Coefficient form of multiplication by `sin^2 t = 1 - cos^2 t`. -/
def latticeSinSq (f : ℤ → ℂ) : ℤ → ℂ :=
  latticeOneSubCos (latticeOnePlusCos f)

/-- The lattice sign operator (coefficient form of `t ↦ t + π`). -/
def latticeSignOp (f : ℤ → ℂ) : ℤ → ℂ :=
  fun n => latticeSign n * f n

theorem latticeCos_add (f g : ℤ → ℂ) :
    latticeCos (f + g) = latticeCos f + latticeCos g := by
  funext n; simp only [latticeCos, Pi.add_apply]; ring

theorem latticeCos_smul (c : ℂ) (f : ℤ → ℂ) :
    latticeCos (c • f) = c • latticeCos f := by
  funext n; simp only [latticeCos, Pi.smul_apply, smul_eq_mul]; ring

theorem latticeSin_add (f g : ℤ → ℂ) :
    latticeSin (f + g) = latticeSin f + latticeSin g := by
  funext n; simp only [latticeSin, Pi.add_apply]; ring

theorem latticeSin_smul (c : ℂ) (f : ℤ → ℂ) :
    latticeSin (c • f) = c • latticeSin f := by
  funext n; simp only [latticeSin, Pi.smul_apply, smul_eq_mul]; ring

theorem latticeOneSubCos_add (f g : ℤ → ℂ) :
    latticeOneSubCos (f + g) = latticeOneSubCos f + latticeOneSubCos g := by
  funext n; simp only [latticeOneSubCos, latticeCos, Pi.add_apply]; ring

theorem latticeOneSubCos_smul (c : ℂ) (f : ℤ → ℂ) :
    latticeOneSubCos (c • f) = c • latticeOneSubCos f := by
  funext n; simp only [latticeOneSubCos, latticeCos, Pi.smul_apply, smul_eq_mul]; ring

theorem latticeOnePlusCos_add (f g : ℤ → ℂ) :
    latticeOnePlusCos (f + g) = latticeOnePlusCos f + latticeOnePlusCos g := by
  funext n; simp only [latticeOnePlusCos, latticeCos, Pi.add_apply]; ring

theorem latticeOnePlusCos_smul (c : ℂ) (f : ℤ → ℂ) :
    latticeOnePlusCos (c • f) = c • latticeOnePlusCos f := by
  funext n; simp only [latticeOnePlusCos, latticeCos, Pi.smul_apply, smul_eq_mul]; ring

/-- `(1 - cos)(1 + cos) = (1 + cos)(1 - cos)`. -/
theorem latticeOneSubCos_onePlusCos_comm (f : ℤ → ℂ) :
    latticeOneSubCos (latticeOnePlusCos f) =
      latticeOnePlusCos (latticeOneSubCos f) := by
  funext n
  simp only [latticeOneSubCos, latticeOnePlusCos, latticeCos]
  ring

/-- Pointwise form of `sin^2`: `(sin^2 f)(n) = f(n)/2 - (f(n-2) + f(n+2))/4`. -/
theorem latticeSinSq_apply (f : ℤ → ℂ) (n : ℤ) :
    latticeSinSq f n = f n / 2 - (f (n - 2) + f (n + 2)) / 4 := by
  simp only [latticeSinSq, latticeOneSubCos, latticeOnePlusCos, latticeCos]
  rw [show n - 1 - 1 = n - 2 by ring, show n - 1 + 1 = n by ring,
    show n + 1 - 1 = n by ring, show n + 1 + 1 = n + 2 by ring]
  ring

/-- `(i sin)^2 = cos^2 - 1 = -(1 - cos)(1 + cos)`. -/
theorem latticeSin_latticeSin (f : ℤ → ℂ) :
    latticeSin (latticeSin f) = -latticeSinSq f := by
  funext n
  simp only [latticeSinSq, latticeSin, latticeOneSubCos, latticeOnePlusCos,
    latticeCos, Pi.neg_apply]
  rw [show n - 1 - 1 = n - 2 by ring, show n - 1 + 1 = n by ring,
    show n + 1 - 1 = n by ring, show n + 1 + 1 = n + 2 by ring]
  ring

/-- The sign operator anticommutes with `cos`. -/
theorem latticeSignOp_latticeCos (f : ℤ → ℂ) :
    latticeSignOp (latticeCos f) = -latticeCos (latticeSignOp f) := by
  funext n
  simp only [latticeSignOp, latticeCos, Pi.neg_apply, latticeSign_sub_one,
    latticeSign_add_one]
  ring

/-- The sign operator anticommutes with `i sin`. -/
theorem latticeSignOp_latticeSin (f : ℤ → ℂ) :
    latticeSignOp (latticeSin f) = -latticeSin (latticeSignOp f) := by
  funext n
  simp only [latticeSignOp, latticeSin, Pi.neg_apply, latticeSign_sub_one,
    latticeSign_add_one]
  ring

theorem latticeSignOp_oneSubCos (f : ℤ → ℂ) :
    latticeSignOp (latticeOneSubCos f) = latticeOnePlusCos (latticeSignOp f) := by
  funext n
  have h := congrFun (latticeSignOp_latticeCos f) n
  simp only [latticeSignOp, latticeOneSubCos, latticeOnePlusCos, Pi.neg_apply] at h ⊢
  rw [mul_sub, h]
  ring

theorem latticeSignOp_onePlusCos (f : ℤ → ℂ) :
    latticeSignOp (latticeOnePlusCos f) = latticeOneSubCos (latticeSignOp f) := by
  funext n
  have h := congrFun (latticeSignOp_latticeCos f) n
  simp only [latticeSignOp, latticeOneSubCos, latticeOnePlusCos, Pi.neg_apply] at h ⊢
  rw [mul_add, h]
  ring

theorem latticeSignOp_sinSq (f : ℤ → ℂ) :
    latticeSignOp (latticeSinSq f) = latticeSinSq (latticeSignOp f) := by
  unfold latticeSinSq
  rw [latticeSignOp_oneSubCos, latticeSignOp_onePlusCos,
    latticeOneSubCos_onePlusCos_comm]

/-! ## Support propagation -/

theorem LatticeSupported.latticeCos {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) : LatticeSupported (N + 1) (latticeCos f) := by
  intro n hn
  rw [mem_latticeBox] at hn
  simp only [latticeCos]
  rw [hf (n - 1) (by rw [mem_latticeBox]; omega), hf (n + 1) (by rw [mem_latticeBox]; omega)]
  simp

theorem LatticeSupported.latticeSin {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) : LatticeSupported (N + 1) (latticeSin f) := by
  intro n hn
  rw [mem_latticeBox] at hn
  simp only [latticeSin]
  rw [hf (n - 1) (by rw [mem_latticeBox]; omega), hf (n + 1) (by rw [mem_latticeBox]; omega)]
  simp

theorem LatticeSupported.oneSubCos {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) : LatticeSupported (N + 1) (latticeOneSubCos f) := by
  intro n hn
  simp only [latticeOneSubCos]
  rw [(hf.mono (Nat.le_succ N)) n hn, hf.latticeCos n hn, sub_zero]

theorem LatticeSupported.onePlusCos {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) : LatticeSupported (N + 1) (latticeOnePlusCos f) := by
  intro n hn
  simp only [latticeOnePlusCos]
  rw [(hf.mono (Nat.le_succ N)) n hn, hf.latticeCos n hn, add_zero]

theorem LatticeSupported.sinSq {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) : LatticeSupported (N + 2) (latticeSinSq f) :=
  hf.onePlusCos.oneSubCos

theorem LatticeSupported.signOp {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) : LatticeSupported N (latticeSignOp f) := by
  intro n hn
  simp [latticeSignOp, hf n hn]

/-! ## Box shifts and adjointness -/

theorem sum_Icc_comp_add {M : Type*} [AddCommMonoid M] (a b c : ℤ) (F : ℤ → M) :
    ∑ n ∈ Finset.Icc a b, F (n + c) = ∑ n ∈ Finset.Icc (a + c) (b + c), F n := by
  rw [← Finset.map_add_right_Icc, Finset.sum_map]
  rfl

/-- Shifting by `-1` inside a box one larger than the support. -/
theorem sum_latticeBox_succ_comp_sub_one {N : ℕ} {F : ℤ → ℂ}
    (hF : LatticeSupported N F) :
    ∑ n ∈ latticeBox (N + 1), F (n - 1) = ∑ n ∈ latticeBox (N + 1), F n := by
  have hshift :
      ∑ n ∈ latticeBox (N + 1), F (n - 1) =
        ∑ n ∈ Finset.Icc (-((N + 1 : ℕ) : ℤ) + -1) (((N + 1 : ℕ) : ℤ) + -1), F n := by
    rw [latticeBox, ← sum_Icc_comp_add]
    rfl
  rw [hshift, sum_latticeBox_eq_of_vanish (Nat.le_succ N) F hF]
  symm
  apply Finset.sum_subset
  · intro n hn
    rw [mem_latticeBox] at hn
    rw [Finset.mem_Icc]
    push_cast
    omega
  · intro n _ hn
    exact hF n hn

/-- Shifting by `+1` inside a box one larger than the support. -/
theorem sum_latticeBox_succ_comp_add_one {N : ℕ} {F : ℤ → ℂ}
    (hF : LatticeSupported N F) :
    ∑ n ∈ latticeBox (N + 1), F (n + 1) = ∑ n ∈ latticeBox (N + 1), F n := by
  have hshift :
      ∑ n ∈ latticeBox (N + 1), F (n + 1) =
        ∑ n ∈ Finset.Icc (-((N + 1 : ℕ) : ℤ) + 1) (((N + 1 : ℕ) : ℤ) + 1), F n := by
    rw [latticeBox, ← sum_Icc_comp_add]
  rw [hshift, sum_latticeBox_eq_of_vanish (Nat.le_succ N) F hF]
  symm
  apply Finset.sum_subset
  · intro n hn
    rw [mem_latticeBox] at hn
    rw [Finset.mem_Icc]
    push_cast
    omega
  · intro n _ hn
    exact hF n hn

/-- Box sesquilinear pairing `∑ conj(f n) g n`. -/
def latticeInner (N : ℕ) (f g : ℤ → ℂ) : ℂ :=
  ∑ n ∈ latticeBox N, conj (f n) * g n

/-- Bilinear moment pairing `∑ p n * f n`. -/
def latticePair (N : ℕ) (p f : ℤ → ℂ) : ℂ :=
  ∑ n ∈ latticeBox N, p n * f n

/-- Bilinear shift identity: `∑ p(n) f(n-1) = ∑ p(n+1) f(n)`. -/
theorem latticePair_shift_sub_one {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (p : ℤ → ℂ) :
    ∑ n ∈ latticeBox (N + 1), p n * f (n - 1) =
      ∑ n ∈ latticeBox (N + 1), p (n + 1) * f n := by
  have hF : LatticeSupported N (fun m => p (m + 1) * f m) := by
    intro n hn; simp [hf n hn]
  have h := sum_latticeBox_succ_comp_sub_one hF
  simp only [sub_add_cancel] at h
  exact h

/-- Bilinear shift identity: `∑ p(n) f(n+1) = ∑ p(n-1) f(n)`. -/
theorem latticePair_shift_add_one {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (p : ℤ → ℂ) :
    ∑ n ∈ latticeBox (N + 1), p n * f (n + 1) =
      ∑ n ∈ latticeBox (N + 1), p (n - 1) * f n := by
  have hF : LatticeSupported N (fun m => p (m - 1) * f m) := by
    intro n hn; simp [hf n hn]
  have h := sum_latticeBox_succ_comp_add_one hF
  simp only [add_sub_cancel_right] at h
  exact h

/-- Bilinear adjointness of `cos`. -/
theorem latticePair_latticeCos {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (p : ℤ → ℂ) :
    latticePair (N + 1) p (latticeCos f) = latticePair (N + 1) (latticeCos p) f := by
  unfold latticePair latticeCos
  have h1 := latticePair_shift_sub_one hf p
  have h2 := latticePair_shift_add_one hf p
  calc
    ∑ n ∈ latticeBox (N + 1), p n * ((f (n - 1) + f (n + 1)) / 2)
        = (∑ n ∈ latticeBox (N + 1), p n * f (n - 1) +
            ∑ n ∈ latticeBox (N + 1), p n * f (n + 1)) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          apply Finset.sum_congr rfl; intro n _; ring
    _ = (∑ n ∈ latticeBox (N + 1), p (n + 1) * f n +
            ∑ n ∈ latticeBox (N + 1), p (n - 1) * f n) / 2 := by rw [h1, h2]
    _ = ∑ n ∈ latticeBox (N + 1), (p (n - 1) + p (n + 1)) / 2 * f n := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          apply Finset.sum_congr rfl; intro n _; ring

/-- Bilinear antiadjointness of `i sin`. -/
theorem latticePair_latticeSin {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (p : ℤ → ℂ) :
    latticePair (N + 1) p (latticeSin f) = -latticePair (N + 1) (latticeSin p) f := by
  unfold latticePair latticeSin
  have h1 := latticePair_shift_sub_one hf p
  have h2 := latticePair_shift_add_one hf p
  calc
    ∑ n ∈ latticeBox (N + 1), p n * ((f (n - 1) - f (n + 1)) / 2)
        = (∑ n ∈ latticeBox (N + 1), p n * f (n - 1) -
            ∑ n ∈ latticeBox (N + 1), p n * f (n + 1)) / 2 := by
          rw [← Finset.sum_sub_distrib, Finset.sum_div]
          apply Finset.sum_congr rfl; intro n _; ring
    _ = (∑ n ∈ latticeBox (N + 1), p (n + 1) * f n -
            ∑ n ∈ latticeBox (N + 1), p (n - 1) * f n) / 2 := by rw [h1, h2]
    _ = -∑ n ∈ latticeBox (N + 1), (p (n - 1) - p (n + 1)) / 2 * f n := by
          rw [← Finset.sum_sub_distrib, Finset.sum_div, ← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl; intro n _; ring

theorem latticePair_oneSubCos {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (p : ℤ → ℂ) :
    latticePair (N + 1) p (latticeOneSubCos f) =
      latticePair (N + 1) (latticeOneSubCos p) f := by
  have h := latticePair_latticeCos hf p
  unfold latticePair latticeOneSubCos at *
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [h]

theorem latticePair_onePlusCos {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (p : ℤ → ℂ) :
    latticePair (N + 1) p (latticeOnePlusCos f) =
      latticePair (N + 1) (latticeOnePlusCos p) f := by
  have h := latticePair_latticeCos hf p
  unfold latticePair latticeOnePlusCos at *
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  rw [h]

/-- The sesquilinear pairing is the bilinear pairing against `conj ∘ f`. -/
theorem latticeInner_eq_latticePair (N : ℕ) (f g : ℤ → ℂ) :
    latticeInner N f g = latticePair N (fun n => conj (f n)) g := rfl

theorem conj_latticeCos (f : ℤ → ℂ) :
    (fun n => conj (latticeCos f n)) = latticeCos (fun n => conj (f n)) := by
  funext n; simp [latticeCos, map_add, map_div₀]

theorem conj_latticeSin (f : ℤ → ℂ) :
    (fun n => conj (latticeSin f n)) = latticeSin (fun n => conj (f n)) := by
  funext n; simp [latticeSin, map_sub, map_div₀]

theorem conj_latticeOneSubCos (f : ℤ → ℂ) :
    (fun n => conj (latticeOneSubCos f n)) =
      latticeOneSubCos (fun n => conj (f n)) := by
  funext n
  have h := congrFun (conj_latticeCos f) n
  simp only [latticeOneSubCos, map_sub] at h ⊢
  rw [h]

theorem conj_latticeOnePlusCos (f : ℤ → ℂ) :
    (fun n => conj (latticeOnePlusCos f n)) =
      latticeOnePlusCos (fun n => conj (f n)) := by
  funext n
  have h := congrFun (conj_latticeCos f) n
  simp only [latticeOnePlusCos, map_add] at h ⊢
  rw [h]

theorem latticePair_comm (N : ℕ) (p f : ℤ → ℂ) :
    latticePair N p f = latticePair N f p := by
  unfold latticePair
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Sesquilinear adjointness of `cos` (left factor supported one step inside). -/
theorem latticeInner_latticeCos_left {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (g : ℤ → ℂ) :
    latticeInner (N + 1) (latticeCos f) g = latticeInner (N + 1) f (latticeCos g) := by
  have hconj : LatticeSupported N (fun n => conj (f n)) := by
    intro n hn; simp [hf n hn]
  rw [latticeInner_eq_latticePair, latticeInner_eq_latticePair, conj_latticeCos,
    latticePair_comm, latticePair_latticeCos hconj g, latticePair_comm]

theorem latticeInner_oneSubCos_left {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (g : ℤ → ℂ) :
    latticeInner (N + 1) (latticeOneSubCos f) g =
      latticeInner (N + 1) f (latticeOneSubCos g) := by
  have hconj : LatticeSupported N (fun n => conj (f n)) := by
    intro n hn; simp [hf n hn]
  rw [latticeInner_eq_latticePair, latticeInner_eq_latticePair, conj_latticeOneSubCos,
    latticePair_comm, latticePair_oneSubCos hconj g, latticePair_comm]

theorem latticeInner_onePlusCos_left {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (g : ℤ → ℂ) :
    latticeInner (N + 1) (latticeOnePlusCos f) g =
      latticeInner (N + 1) f (latticeOnePlusCos g) := by
  have hconj : LatticeSupported N (fun n => conj (f n)) := by
    intro n hn; simp [hf n hn]
  rw [latticeInner_eq_latticePair, latticeInner_eq_latticePair, conj_latticeOnePlusCos,
    latticePair_comm, latticePair_onePlusCos hconj g, latticePair_comm]

/-- Sesquilinear antiadjointness of `i sin`. -/
theorem latticeInner_latticeSin_left {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (g : ℤ → ℂ) :
    latticeInner (N + 1) (latticeSin f) g = -latticeInner (N + 1) f (latticeSin g) := by
  have hconj : LatticeSupported N (fun n => conj (f n)) := by
    intro n hn; simp [hf n hn]
  rw [latticeInner_eq_latticePair, latticeInner_eq_latticePair, conj_latticeSin,
    latticePair_comm, latticePair_latticeSin hconj g, latticePair_comm]

/-! ## Moments of the operator images -/

/-- `∑ (1 - cos) a = 0` (the coefficient sum is evaluation at `t = 0`). -/
theorem latticePair_one_oneSubCos {N : ℕ} {a : ℤ → ℂ}
    (ha : LatticeSupported N a) :
    latticePair (N + 1) (fun _ => 1) (latticeOneSubCos a) = 0 := by
  rw [latticePair_oneSubCos ha]
  unfold latticePair
  apply Finset.sum_eq_zero
  intro n _
  simp [latticeOneSubCos, latticeCos]

/-- `∑ n (1 - cos) a = 0`. -/
theorem latticePair_id_oneSubCos {N : ℕ} {a : ℤ → ℂ}
    (ha : LatticeSupported N a) :
    latticePair (N + 1) (fun n => (n : ℂ)) (latticeOneSubCos a) = 0 := by
  rw [latticePair_oneSubCos ha]
  unfold latticePair
  apply Finset.sum_eq_zero
  intro n _
  simp only [latticeOneSubCos, latticeCos]
  push_cast
  ring

/-- `∑ n^2 (1 - cos) a = -∑ a`. -/
theorem latticePair_sq_oneSubCos {N : ℕ} {a : ℤ → ℂ}
    (ha : LatticeSupported N a) :
    latticePair (N + 1) (fun n => (n : ℂ) ^ 2) (latticeOneSubCos a) =
      -latticePair (N + 1) (fun _ => 1) a := by
  rw [latticePair_oneSubCos ha]
  unfold latticePair
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [latticeOneSubCos, latticeCos]
  push_cast
  ring

/-- `∑ i sin a = 0`. -/
theorem latticePair_one_latticeSin {N : ℕ} {a : ℤ → ℂ}
    (ha : LatticeSupported N a) :
    latticePair (N + 1) (fun _ => 1) (latticeSin a) = 0 := by
  rw [latticePair_latticeSin ha]
  unfold latticePair
  rw [neg_eq_zero]
  apply Finset.sum_eq_zero
  intro n _
  simp [latticeSin]

/-- `∑ n (i sin a) = ∑ a`. -/
theorem latticePair_id_latticeSin {N : ℕ} {a : ℤ → ℂ}
    (ha : LatticeSupported N a) :
    latticePair (N + 1) (fun n => (n : ℂ)) (latticeSin a) =
      latticePair (N + 1) (fun _ => 1) a := by
  rw [latticePair_latticeSin ha]
  unfold latticePair
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [latticeSin]
  push_cast
  ring

/-- `∑ n^2 (i sin a) = 2 ∑ n a`. -/
theorem latticePair_sq_latticeSin {N : ℕ} {a : ℤ → ℂ}
    (ha : LatticeSupported N a) :
    latticePair (N + 1) (fun n => (n : ℂ) ^ 2) (latticeSin a) =
      2 * latticePair (N + 1) (fun n => (n : ℂ)) a := by
  rw [latticePair_latticeSin ha]
  unfold latticePair
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [latticeSin]
  push_cast
  ring

/-! ## Injectivity on finitely supported sequences -/

/-- A box-supported sequence satisfying a two-step downward recurrence vanishes. -/
theorem eq_zero_of_downward_recurrence {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f)
    (hrec : ∀ n : ℤ, f (n + 1) = 0 → f (n + 2) = 0 → f n = 0) :
    f = 0 := by
  have key : ∀ j : ℕ, f ((N : ℤ) + 1 - j) = 0 ∧ f ((N : ℤ) + 2 - j) = 0 := by
    intro j
    induction j with
    | zero =>
        constructor
        · apply hf; rw [mem_latticeBox]; push_cast; omega
        · apply hf; rw [mem_latticeBox]; push_cast; omega
    | succ j ih =>
        refine ⟨?_, ?_⟩
        · apply hrec
          · have h := ih.1
            convert h using 2
            push_cast
            ring
          · have h := ih.2
            convert h using 2
            push_cast
            ring
        · have h := ih.1
          convert h using 2
          push_cast
          ring
  funext n
  by_cases hn : n ≤ (N : ℤ) + 1
  · have h := (key (N + 1 - n).toNat).1
    convert h using 2
    omega
  · exact hf n (by rw [mem_latticeBox]; omega)

theorem eq_zero_of_latticeOneSubCos_eq_zero {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (h : latticeOneSubCos f = 0) : f = 0 := by
  apply eq_zero_of_downward_recurrence hf
  intro n h1 h2
  have hn := congrFun h (n + 1)
  simp only [latticeOneSubCos, latticeCos, Pi.zero_apply] at hn
  rw [show n + 1 - 1 = n by ring, show n + 1 + 1 = n + 2 by ring, h1, h2] at hn
  linear_combination -2 * hn

theorem eq_zero_of_latticeOnePlusCos_eq_zero {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (h : latticeOnePlusCos f = 0) : f = 0 := by
  apply eq_zero_of_downward_recurrence hf
  intro n h1 h2
  have hn := congrFun h (n + 1)
  simp only [latticeOnePlusCos, latticeCos, Pi.zero_apply] at hn
  rw [show n + 1 - 1 = n by ring, show n + 1 + 1 = n + 2 by ring, h1, h2] at hn
  linear_combination 2 * hn

theorem eq_zero_of_latticeSin_eq_zero {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (h : latticeSin f = 0) : f = 0 := by
  apply eq_zero_of_downward_recurrence hf
  intro n _ h2
  have hn := congrFun h (n + 1)
  simp only [latticeSin, Pi.zero_apply] at hn
  rw [show n + 1 - 1 = n by ring, show n + 1 + 1 = n + 2 by ring, h2] at hn
  linear_combination 2 * hn

theorem eq_zero_of_latticeSinSq_eq_zero {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (h : latticeSinSq f = 0) : f = 0 :=
  eq_zero_of_latticeOnePlusCos_eq_zero hf
    (eq_zero_of_latticeOneSubCos_eq_zero hf.onePlusCos h)

/-! ## Parity of sequences -/

/-- Symmetric lattice sequence (`f (-n) = f n`): coefficient form of an even
trigonometric polynomial. -/
def LatticeSymmetric (f : ℤ → ℂ) : Prop :=
  ∀ n, f (-n) = f n

/-- Antisymmetric lattice sequence (`f (-n) = -f n`). -/
def LatticeAntisymmetric (f : ℤ → ℂ) : Prop :=
  ∀ n, f (-n) = -f n

theorem LatticeSymmetric.latticeCos {f : ℤ → ℂ} (hf : LatticeSymmetric f) :
    LatticeSymmetric (latticeCos f) := by
  intro n
  simp only [latticeCos]
  rw [show -n - 1 = -(n + 1) by ring, show -n + 1 = -(n - 1) by ring, hf, hf]
  ring

theorem LatticeSymmetric.oneSubCos {f : ℤ → ℂ} (hf : LatticeSymmetric f) :
    LatticeSymmetric (latticeOneSubCos f) := by
  intro n
  simp only [latticeOneSubCos]
  rw [hf n, hf.latticeCos n]

theorem LatticeSymmetric.latticeSin {f : ℤ → ℂ} (hf : LatticeSymmetric f) :
    LatticeAntisymmetric (latticeSin f) := by
  intro n
  simp only [latticeSin]
  rw [show -n - 1 = -(n + 1) by ring, show -n + 1 = -(n - 1) by ring, hf, hf]
  ring

/-- Sequences supported on even lattice indices. -/
def EvenIndexSupported (f : ℤ → ℂ) : Prop :=
  ∀ n, Odd n → f n = 0

/-- Sequences supported on odd lattice indices. -/
def OddIndexSupported (f : ℤ → ℂ) : Prop :=
  ∀ n, Even n → f n = 0

theorem EvenIndexSupported.sinSq {f : ℤ → ℂ} (hf : EvenIndexSupported f) :
    EvenIndexSupported (latticeSinSq f) := by
  intro n hn
  rw [latticeSinSq_apply, hf n hn,
    hf (n - 2) (by rcases hn with ⟨k, rfl⟩; exact ⟨k - 1, by ring⟩),
    hf (n + 2) (by rcases hn with ⟨k, rfl⟩; exact ⟨k + 1, by ring⟩)]
  ring

theorem OddIndexSupported.sinSq {f : ℤ → ℂ} (hf : OddIndexSupported f) :
    OddIndexSupported (latticeSinSq f) := by
  intro n hn
  rw [latticeSinSq_apply, hf n hn,
    hf (n - 2) (by rcases hn with ⟨k, rfl⟩; exact ⟨k - 1, by ring⟩),
    hf (n + 2) (by rcases hn with ⟨k, rfl⟩; exact ⟨k + 1, by ring⟩)]
  ring

end Zeta23.CCM
