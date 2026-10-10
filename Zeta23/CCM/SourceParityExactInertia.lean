import Zeta23.CCM.SourceParityPolynomialCoordinates

noncomputable section

namespace Zeta23.CCM

open Matrix Finset Module
open scoped BigOperators ComplexConjugate

/-!
# POST284-M17: exact parity source inertia at the half aperture, every `K`

At `ω = 1/2` the elementary source matrix is `Diag((-1)^n)`
(`sourceEntry_half`).  On the even boundary-flat carrier write
`u = (1 - cos)^2 q` and on the odd carrier `u = (i sin)(1 - cos) q`, with `q`
symmetric and supported in `[-(K-2), K-2]`.  The lattice operator identities
give the exact orthogonal splittings

* even: `B(u₁,u₂) = ⟪sin² q₁, (-1)^n sin² q₂⟫`,
* odd:  `B(u₁,u₂) = -⟪sin² q₁, (-1)^n sin² q₂⟫`,

so the source form is positive (resp. negative) definite on the image of
even-index `q` and negative (resp. positive) definite on the image of
odd-index `q`, and the two images are orthogonal.  Counting indices gives, for
every `K ≥ 2` with `d = K - 1`,

* even carrier: inertia `(⌈d/2⌉, ⌊d/2⌋, 0) = (K/2, (K-1)/2, 0)`;
* odd carrier:  inertia `(⌊d/2⌋, ⌈d/2⌉, 0) = ((K-1)/2, K/2, 0)`.

Scope firewall: this is an exact statement about the elementary
`sourceMatrix (1/2)` restricted to the parity boundary-flat carriers.  The
interior source coordinates `0 < ω < 1/2` (the Andréief signed-minor lemma) are
NOT proved here, and nothing here concerns the canonical source operator, its
ground contacts, or RH.
-/

/-! ## Abstract inertia packaging -/

/-- An orthogonal positive/negative splitting of a subspace determines the
exact inertia: the form is nondegenerate on `V`, and every positive (negative)
definite subspace of `V` has dimension at most `dim P` (`dim N`). -/
theorem exactInertia_of_orthogonal_split
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (B : E → E → ℂ)
    (hBadd : ∀ x y z, B (x + y) z = B x z + B y z)
    (V P N : Submodule ℂ E) (hPN : P ⊔ N = V)
    (horth : ∀ p ∈ P, ∀ n ∈ N, B p n = 0 ∧ B n p = 0)
    (hpos : ∀ p ∈ P, p ≠ 0 → 0 < (B p p).re)
    (hneg : ∀ n ∈ N, n ≠ 0 → (B n n).re < 0) :
    (∀ v ∈ V, (∀ w ∈ V, B v w = 0) → v = 0) ∧
      (∀ W : Submodule ℂ E, W ≤ V →
        (∀ w ∈ W, w ≠ 0 → 0 < (B w w).re) → finrank ℂ W ≤ finrank ℂ P) ∧
      (∀ W : Submodule ℂ E, W ≤ V →
        (∀ w ∈ W, w ≠ 0 → (B w w).re < 0) → finrank ℂ W ≤ finrank ℂ N) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv hrad
    rw [← hPN] at hv
    obtain ⟨p, hp, n, hn, rfl⟩ := Submodule.mem_sup.mp hv
    have hpV : p ∈ V := hPN ▸ Submodule.mem_sup_left hp
    have hnV : n ∈ V := hPN ▸ Submodule.mem_sup_right hn
    have hp0 : p = 0 := by
      by_contra hne
      have h := hrad p hpV
      rw [hBadd, (horth p hp n hn).2, add_zero] at h
      have := hpos p hp hne
      rw [h] at this
      simp at this
    have hn0 : n = 0 := by
      by_contra hne
      have h := hrad n hnV
      rw [hBadd, (horth p hp n hn).1, zero_add] at h
      have := hneg n hn hne
      rw [h] at this
      simp at this
    rw [hp0, hn0, add_zero]
  · intro W hW hWpos
    have hinf : W ⊓ N = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      by_contra hne
      have h1 := hWpos x hx.1 hne
      have h2 := hneg x hx.2 hne
      linarith
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq W N
    rw [hinf, finrank_bot, add_zero] at hdim
    have hsup : finrank ℂ ↥(W ⊔ N) ≤ finrank ℂ V :=
      Submodule.finrank_mono (sup_le hW (hPN ▸ le_sup_right))
    have hV : finrank ℂ V ≤ finrank ℂ P + finrank ℂ N := by
      rw [← hPN]
      exact Submodule.finrank_add_le_finrank_add_finrank P N
    omega
  · intro W hW hWneg
    have hinf : W ⊓ P = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      by_contra hne
      have h1 := hWneg x hx.1 hne
      have h2 := hpos x hx.2 hne
      linarith
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq W P
    rw [hinf, finrank_bot, add_zero] at hdim
    have hsup : finrank ℂ ↥(W ⊔ P) ≤ finrank ℂ V :=
      Submodule.finrank_mono (sup_le hW (hPN ▸ le_sup_left))
    have hV : finrank ℂ V ≤ finrank ℂ P + finrank ℂ N := by
      rw [← hPN]
      exact Submodule.finrank_add_le_finrank_add_finrank P N
    omega

/-! ## Index-parity parameters -/

/-- Symmetric even-index bump `δ_{2k} + δ_{-2k}` (`δ_0` for `k = 0`). -/
def evenIndexBump (k : ℕ) : ℤ → ℂ :=
  fun n => if n = 2 * (k : ℤ) ∨ n = -(2 * (k : ℤ)) then 1 else 0

/-- Symmetric odd-index bump `δ_{2k+1} + δ_{-(2k+1)}`. -/
def oddIndexBump (k : ℕ) : ℤ → ℂ :=
  fun n => if n = 2 * (k : ℤ) + 1 ∨ n = -(2 * (k : ℤ) + 1) then 1 else 0

/-- Symmetric even-index sequence with free parameters `c`. -/
def evenIndexParam {p : ℕ} (c : Fin p → ℂ) : ℤ → ℂ :=
  fun n => ∑ k : Fin p, c k * evenIndexBump k n

/-- Symmetric odd-index sequence with free parameters `c`. -/
def oddIndexParam {p : ℕ} (c : Fin p → ℂ) : ℤ → ℂ :=
  fun n => ∑ k : Fin p, c k * oddIndexBump k n

theorem evenIndexParam_add {p : ℕ} (c c' : Fin p → ℂ) :
    evenIndexParam (c + c') = evenIndexParam c + evenIndexParam c' := by
  funext n
  simp only [evenIndexParam, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem evenIndexParam_smul {p : ℕ} (a : ℂ) (c : Fin p → ℂ) :
    evenIndexParam (a • c) = a • evenIndexParam c := by
  funext n
  simp only [evenIndexParam, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem oddIndexParam_add {p : ℕ} (c c' : Fin p → ℂ) :
    oddIndexParam (c + c') = oddIndexParam c + oddIndexParam c' := by
  funext n
  simp only [oddIndexParam, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem oddIndexParam_smul {p : ℕ} (a : ℂ) (c : Fin p → ℂ) :
    oddIndexParam (a • c) = a • oddIndexParam c := by
  funext n
  simp only [oddIndexParam, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem evenIndexParam_symmetric {p : ℕ} (c : Fin p → ℂ) :
    LatticeSymmetric (evenIndexParam c) := by
  intro n
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  unfold evenIndexBump
  congr 1
  apply propext
  constructor <;> rintro (h | h) <;> omega

theorem oddIndexParam_symmetric {p : ℕ} (c : Fin p → ℂ) :
    LatticeSymmetric (oddIndexParam c) := by
  intro n
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  unfold oddIndexBump
  congr 1
  apply propext
  constructor <;> rintro (h | h) <;> omega

theorem evenIndexParam_evenIndexSupported {p : ℕ} (c : Fin p → ℂ) :
    EvenIndexSupported (evenIndexParam c) := by
  intro n hn
  apply Finset.sum_eq_zero
  intro k _
  have : ¬ (n = 2 * (k : ℤ) ∨ n = -(2 * (k : ℤ))) := by
    rintro (h | h) <;> (rcases hn with ⟨j, rfl⟩; omega)
  simp only [evenIndexBump]
  rw [if_neg this, mul_zero]

theorem oddIndexParam_oddIndexSupported {p : ℕ} (c : Fin p → ℂ) :
    OddIndexSupported (oddIndexParam c) := by
  intro n hn
  apply Finset.sum_eq_zero
  intro k _
  have : ¬ (n = 2 * (k : ℤ) + 1 ∨ n = -(2 * (k : ℤ) + 1)) := by
    rintro (h | h) <;> (rcases hn with ⟨j, rfl⟩; omega)
  simp only [oddIndexBump]
  rw [if_neg this, mul_zero]

theorem evenIndexParam_supported (m : ℕ) (c : Fin (m / 2 + 1) → ℂ) :
    LatticeSupported m (evenIndexParam c) := by
  intro n hn
  rw [mem_latticeBox] at hn
  apply Finset.sum_eq_zero
  intro k _
  have hk := k.2
  have : ¬ (n = 2 * ((k : ℕ) : ℤ) ∨ n = -(2 * ((k : ℕ) : ℤ))) := by
    rintro (h | h) <;> omega
  simp only [evenIndexBump]
  rw [if_neg this, mul_zero]

theorem oddIndexParam_supported (m : ℕ) (c : Fin ((m + 1) / 2) → ℂ) :
    LatticeSupported m (oddIndexParam c) := by
  intro n hn
  rw [mem_latticeBox] at hn
  apply Finset.sum_eq_zero
  intro k _
  have hk := k.2
  have : ¬ (n = 2 * ((k : ℕ) : ℤ) + 1 ∨ n = -(2 * ((k : ℕ) : ℤ) + 1)) := by
    rintro (h | h) <;> omega
  simp only [oddIndexBump]
  rw [if_neg this, mul_zero]

theorem evenIndexParam_at {p : ℕ} (c : Fin p → ℂ) (k : Fin p) :
    evenIndexParam c (2 * ((k : ℕ) : ℤ)) = c k := by
  unfold evenIndexParam
  rw [Finset.sum_eq_single k]
  · simp [evenIndexBump]
  · intro j _ hjk
    have : ¬ (2 * ((k : ℕ) : ℤ) = 2 * ((j : ℕ) : ℤ) ∨
        2 * ((k : ℕ) : ℤ) = -(2 * ((j : ℕ) : ℤ))) := by
      rintro (h | h)
      · exact hjk (Fin.ext (by omega))
      · exact hjk (Fin.ext (by omega))
    simp only [evenIndexBump]
    rw [if_neg this, mul_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

theorem oddIndexParam_at {p : ℕ} (c : Fin p → ℂ) (k : Fin p) :
    oddIndexParam c (2 * ((k : ℕ) : ℤ) + 1) = c k := by
  unfold oddIndexParam
  rw [Finset.sum_eq_single k]
  · simp [oddIndexBump]
  · intro j _ hjk
    have : ¬ (2 * ((k : ℕ) : ℤ) + 1 = 2 * ((j : ℕ) : ℤ) + 1 ∨
        2 * ((k : ℕ) : ℤ) + 1 = -(2 * ((j : ℕ) : ℤ) + 1)) := by
      rintro (h | h)
      · exact hjk (Fin.ext (by omega))
      · omega
    simp only [oddIndexBump]
    rw [if_neg this, mul_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

theorem eq_zero_of_evenIndexParam_eq_zero {p : ℕ} {c : Fin p → ℂ}
    (h : evenIndexParam c = 0) : c = 0 := by
  funext k
  rw [← evenIndexParam_at c k, h]
  rfl

theorem eq_zero_of_oddIndexParam_eq_zero {p : ℕ} {c : Fin p → ℂ}
    (h : oddIndexParam c = 0) : c = 0 := by
  funext k
  rw [← oddIndexParam_at c k, h]
  rfl

/-! ## Carrier maps -/

/-- Coefficient form of `C_u = (1 - cos t)^2 Q(cos t)` on `[-(m+2), m+2]`. -/
def evenCarrierMap (m : ℕ) (q : ℤ → ℂ) : Fin (2 * (m + 2) + 1) → ℂ :=
  ofLattice (m + 2) (latticeOneSubCos (latticeOneSubCos q))

/-- Coefficient form of `T_u = sin t (1 - cos t) Q(cos t)` on `[-(m+2), m+2]`
(up to the harmless constant `i`). -/
def oddCarrierMap (m : ℕ) (q : ℤ → ℂ) : Fin (2 * (m + 2) + 1) → ℂ :=
  ofLattice (m + 2) (latticeSin (latticeOneSubCos q))

theorem evenCarrierMap_add (m : ℕ) (q q' : ℤ → ℂ) :
    evenCarrierMap m (q + q') = evenCarrierMap m q + evenCarrierMap m q' := by
  rw [evenCarrierMap, latticeOneSubCos_add, latticeOneSubCos_add, ofLattice_add]
  rfl

theorem evenCarrierMap_smul (m : ℕ) (a : ℂ) (q : ℤ → ℂ) :
    evenCarrierMap m (a • q) = a • evenCarrierMap m q := by
  rw [evenCarrierMap, latticeOneSubCos_smul, latticeOneSubCos_smul, ofLattice_smul]
  rfl

theorem oddCarrierMap_add (m : ℕ) (q q' : ℤ → ℂ) :
    oddCarrierMap m (q + q') = oddCarrierMap m q + oddCarrierMap m q' := by
  rw [oddCarrierMap, latticeOneSubCos_add, latticeSin_add, ofLattice_add]
  rfl

theorem oddCarrierMap_smul (m : ℕ) (a : ℂ) (q : ℤ → ℂ) :
    oddCarrierMap m (a • q) = a • oddCarrierMap m q := by
  rw [oddCarrierMap, latticeOneSubCos_smul, latticeSin_smul, ofLattice_smul]
  rfl

theorem evenCarrierMap_mem {m : ℕ} {q : ℤ → ℂ}
    (hq : LatticeSupported m q) (hsym : LatticeSymmetric q) :
    evenCarrierMap m q ∈ evenBoundaryFlatSubspace (m + 2) := by
  have ha : LatticeSupported (m + 1) (latticeOneSubCos q) := hq.oneSubCos
  have hq1 : LatticeSupported (m + 1) q := hq.mono (Nat.le_succ m)
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_boundaryFlatSubspace_iff]
    refine ⟨?_, ?_, ?_⟩
    · rw [evenCarrierMap, centeredMoment_ofLattice]
      have h := latticePair_one_oneSubCos ha
      unfold latticePair at h
      simpa using h
    · rw [evenCarrierMap, centeredMoment_ofLattice]
      have h := latticePair_id_oneSubCos ha
      unfold latticePair at h
      simpa using h
    · rw [evenCarrierMap, centeredMoment_ofLattice]
      have h := latticePair_sq_oneSubCos ha
      have h0 := latticePair_one_oneSubCos hq1
      rw [h0, neg_zero] at h
      exact h
  · rw [mem_evenCoefficientSubspace_iff, evenCarrierMap, reverseCoefficients_ofLattice]
    congr 1
    funext n
    exact hsym.oneSubCos.oneSubCos n

theorem oddCarrierMap_mem {m : ℕ} {q : ℤ → ℂ}
    (hq : LatticeSupported m q) (hsym : LatticeSymmetric q) :
    oddCarrierMap m q ∈ oddBoundaryFlatSubspace (m + 2) := by
  have ha : LatticeSupported (m + 1) (latticeOneSubCos q) := hq.oneSubCos
  have hq1 : LatticeSupported (m + 1) q := hq.mono (Nat.le_succ m)
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_boundaryFlatSubspace_iff]
    refine ⟨?_, ?_, ?_⟩
    · rw [oddCarrierMap, centeredMoment_ofLattice]
      have h := latticePair_one_latticeSin ha
      unfold latticePair at h
      simpa using h
    · rw [oddCarrierMap, centeredMoment_ofLattice]
      have h := latticePair_id_latticeSin ha
      rw [latticePair_one_oneSubCos hq1] at h
      unfold latticePair at h
      simpa using h
    · rw [oddCarrierMap, centeredMoment_ofLattice]
      have h := latticePair_sq_latticeSin ha
      rw [latticePair_id_oneSubCos hq1, mul_zero] at h
      exact h
  · rw [mem_oddCoefficientSubspace_iff, oddCarrierMap, reverseCoefficients_ofLattice]
    funext i
    simp only [ofLattice_apply, Pi.neg_apply]
    exact hsym.oneSubCos.latticeSin _

/-! ## The core half-aperture identity -/

theorem latticeInner_neg_right (N : ℕ) (f g : ℤ → ℂ) :
    latticeInner N f (-g) = -latticeInner N f g := by
  unfold latticeInner
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp

/-- The four-factor reduction shared by both parities. -/
theorem latticeInner_core {m : ℕ} {q₁ : ℤ → ℂ} (h₁ : LatticeSupported m q₁)
    (g : ℤ → ℂ) :
    latticeInner (m + 2) q₁
        (latticeOneSubCos (latticeOneSubCos (latticeOnePlusCos (latticeOnePlusCos g)))) =
      latticeInner (m + 2) (latticeSinSq q₁)
        (latticeOneSubCos (latticeOnePlusCos g)) := by
  have hq1 : LatticeSupported (m + 1) q₁ := h₁.mono (Nat.le_succ m)
  have hp1 : LatticeSupported (m + 1) (latticeOnePlusCos q₁) := h₁.onePlusCos
  rw [latticeSinSq, latticeInner_oneSubCos_left hp1, latticeInner_onePlusCos_left hq1]
  congr 1
  rw [latticeOneSubCos_onePlusCos_comm (latticeOnePlusCos g),
    latticeOneSubCos_onePlusCos_comm (latticeOneSubCos (latticeOnePlusCos g))]

/-- Exact even-carrier half-aperture form. -/
theorem sourceSesq_half_evenCarrierMap {m : ℕ} {q₁ q₂ : ℤ → ℂ}
    (h₁ : LatticeSupported m q₁) :
    sourceSesq (1 / 2) (m + 2) (evenCarrierMap m q₁) (evenCarrierMap m q₂) =
      latticeInner (m + 2) (latticeSinSq q₁) (latticeSignOp (latticeSinSq q₂)) := by
  have hq1 : LatticeSupported (m + 1) q₁ := h₁.mono (Nat.le_succ m)
  have ha1 : LatticeSupported (m + 1) (latticeOneSubCos q₁) := h₁.oneSubCos
  rw [evenCarrierMap, evenCarrierMap, sourceSesq_half_ofLattice]
  have hsign :
      ∑ n ∈ latticeBox (m + 2), latticeSign n *
          (conj (latticeOneSubCos (latticeOneSubCos q₁) n) *
            latticeOneSubCos (latticeOneSubCos q₂) n) =
        latticeInner (m + 2) (latticeOneSubCos (latticeOneSubCos q₁))
          (latticeSignOp (latticeOneSubCos (latticeOneSubCos q₂))) := by
    unfold latticeInner latticeSignOp
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hsign, latticeSignOp_oneSubCos, latticeSignOp_oneSubCos,
    latticeInner_oneSubCos_left ha1, latticeInner_oneSubCos_left hq1,
    latticeInner_core h₁, latticeSignOp_sinSq]
  rfl

/-- Exact odd-carrier half-aperture form. -/
theorem sourceSesq_half_oddCarrierMap {m : ℕ} {q₁ q₂ : ℤ → ℂ}
    (h₁ : LatticeSupported m q₁) :
    sourceSesq (1 / 2) (m + 2) (oddCarrierMap m q₁) (oddCarrierMap m q₂) =
      -latticeInner (m + 2) (latticeSinSq q₁) (latticeSignOp (latticeSinSq q₂)) := by
  have hq1 : LatticeSupported (m + 1) q₁ := h₁.mono (Nat.le_succ m)
  have ha1 : LatticeSupported (m + 1) (latticeOneSubCos q₁) := h₁.oneSubCos
  rw [oddCarrierMap, oddCarrierMap, sourceSesq_half_ofLattice]
  have hsign :
      ∑ n ∈ latticeBox (m + 2), latticeSign n *
          (conj (latticeSin (latticeOneSubCos q₁) n) *
            latticeSin (latticeOneSubCos q₂) n) =
        latticeInner (m + 2) (latticeSin (latticeOneSubCos q₁))
          (latticeSignOp (latticeSin (latticeOneSubCos q₂))) := by
    unfold latticeInner latticeSignOp
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hsign, latticeSignOp_latticeSin, latticeInner_neg_right,
    latticeInner_latticeSin_left ha1, neg_neg, latticeSin_latticeSin,
    latticeInner_neg_right, latticeSignOp_oneSubCos]
  rw [show latticeSinSq (latticeOnePlusCos (latticeSignOp q₂)) =
      latticeOneSubCos (latticeOnePlusCos (latticeOnePlusCos (latticeSignOp q₂))) from rfl,
    latticeInner_oneSubCos_left hq1, latticeInner_core h₁, latticeSignOp_sinSq]
  rfl

/-! ## Sign of the core form -/

theorem latticeInner_self_eq (N : ℕ) (w : ℤ → ℂ) :
    latticeInner N w w = ((∑ n ∈ latticeBox N, Complex.normSq (w n) : ℝ) : ℂ) := by
  unfold latticeInner
  push_cast
  apply Finset.sum_congr rfl
  intro n _
  rw [Complex.normSq_eq_conj_mul_self]

theorem latticeInner_self_re_pos {N : ℕ} {w : ℤ → ℂ}
    (hw : LatticeSupported N w) (hne : w ≠ 0) :
    0 < (latticeInner N w w).re := by
  rw [latticeInner_self_eq, Complex.ofReal_re]
  obtain ⟨n, hn⟩ : ∃ n, w n ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hmem : n ∈ latticeBox N := by
    by_contra hnot
    exact hn (hw n hnot)
  exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
    ⟨n, hmem, Complex.normSq_pos.mpr hn⟩

theorem latticeSignOp_of_evenIndexSupported {w : ℤ → ℂ}
    (hw : EvenIndexSupported w) : latticeSignOp w = w := by
  funext n
  rcases Int.even_or_odd n with h | h
  · simp [latticeSignOp, latticeSign_of_even h]
  · simp [latticeSignOp, hw n h]

theorem latticeSignOp_of_oddIndexSupported {w : ℤ → ℂ}
    (hw : OddIndexSupported w) : latticeSignOp w = -w := by
  funext n
  rcases Int.even_or_odd n with h | h
  · simp [latticeSignOp, hw n h]
  · simp [latticeSignOp, latticeSign_of_odd h]

theorem latticeInner_even_odd_eq_zero (N : ℕ) {w₁ w₂ : ℤ → ℂ}
    (h₁ : EvenIndexSupported w₁) (h₂ : OddIndexSupported w₂) :
    latticeInner N w₁ w₂ = 0 := by
  unfold latticeInner
  apply Finset.sum_eq_zero
  intro n _
  rcases Int.even_or_odd n with h | h
  · simp [h₂ n h]
  · simp [h₁ n h]

theorem latticeInner_odd_even_eq_zero (N : ℕ) {w₁ w₂ : ℤ → ℂ}
    (h₁ : OddIndexSupported w₁) (h₂ : EvenIndexSupported w₂) :
    latticeInner N w₁ w₂ = 0 := by
  unfold latticeInner
  apply Finset.sum_eq_zero
  intro n _
  rcases Int.even_or_odd n with h | h
  · simp [h₁ n h]
  · simp [h₂ n h]

/-! ## Parameter linear maps -/

/-- `c ↦ evenCarrierMap m (evenIndexParam c)`. -/
def evenCarrierEvenIndexMap (m : ℕ) :
    (Fin (m / 2 + 1) → ℂ) →ₗ[ℂ] (Fin (2 * (m + 2) + 1) → ℂ) where
  toFun c := evenCarrierMap m (evenIndexParam c)
  map_add' c c' := by rw [evenIndexParam_add, evenCarrierMap_add]
  map_smul' a c := by rw [evenIndexParam_smul, evenCarrierMap_smul]; rfl

/-- `c ↦ evenCarrierMap m (oddIndexParam c)`. -/
def evenCarrierOddIndexMap (m : ℕ) :
    (Fin ((m + 1) / 2) → ℂ) →ₗ[ℂ] (Fin (2 * (m + 2) + 1) → ℂ) where
  toFun c := evenCarrierMap m (oddIndexParam c)
  map_add' c c' := by rw [oddIndexParam_add, evenCarrierMap_add]
  map_smul' a c := by rw [oddIndexParam_smul, evenCarrierMap_smul]; rfl

/-- `c ↦ oddCarrierMap m (evenIndexParam c)`. -/
def oddCarrierEvenIndexMap (m : ℕ) :
    (Fin (m / 2 + 1) → ℂ) →ₗ[ℂ] (Fin (2 * (m + 2) + 1) → ℂ) where
  toFun c := oddCarrierMap m (evenIndexParam c)
  map_add' c c' := by rw [evenIndexParam_add, oddCarrierMap_add]
  map_smul' a c := by rw [evenIndexParam_smul, oddCarrierMap_smul]; rfl

/-- `c ↦ oddCarrierMap m (oddIndexParam c)`. -/
def oddCarrierOddIndexMap (m : ℕ) :
    (Fin ((m + 1) / 2) → ℂ) →ₗ[ℂ] (Fin (2 * (m + 2) + 1) → ℂ) where
  toFun c := oddCarrierMap m (oddIndexParam c)
  map_add' c c' := by rw [oddIndexParam_add, oddCarrierMap_add]
  map_smul' a c := by rw [oddIndexParam_smul, oddCarrierMap_smul]; rfl

theorem evenCarrierMap_zero (m : ℕ) : evenCarrierMap m 0 = 0 := by
  have h := evenCarrierMap_smul m 0 0
  rw [zero_smul, zero_smul] at h
  exact h

theorem oddCarrierMap_zero (m : ℕ) : oddCarrierMap m 0 = 0 := by
  have h := oddCarrierMap_smul m 0 0
  rw [zero_smul, zero_smul] at h
  exact h

theorem eq_zero_of_evenCarrierMap_eq_zero {m : ℕ} {q : ℤ → ℂ}
    (hq : LatticeSupported m q) (h : evenCarrierMap m q = 0) : q = 0 := by
  have h2 := eq_zero_of_ofLattice_eq_zero hq.oneSubCos.oneSubCos h
  have h1 := eq_zero_of_latticeOneSubCos_eq_zero hq.oneSubCos h2
  exact eq_zero_of_latticeOneSubCos_eq_zero hq h1

theorem eq_zero_of_oddCarrierMap_eq_zero {m : ℕ} {q : ℤ → ℂ}
    (hq : LatticeSupported m q) (h : oddCarrierMap m q = 0) : q = 0 := by
  have h2 := eq_zero_of_ofLattice_eq_zero hq.oneSubCos.latticeSin h
  have h1 := eq_zero_of_latticeSin_eq_zero hq.oneSubCos h2
  exact eq_zero_of_latticeOneSubCos_eq_zero hq h1

theorem evenCarrierEvenIndexMap_injective (m : ℕ) :
    Function.Injective (evenCarrierEvenIndexMap m) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro c hc
  exact eq_zero_of_evenIndexParam_eq_zero
    (eq_zero_of_evenCarrierMap_eq_zero (evenIndexParam_supported m c) hc)

theorem evenCarrierOddIndexMap_injective (m : ℕ) :
    Function.Injective (evenCarrierOddIndexMap m) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro c hc
  exact eq_zero_of_oddIndexParam_eq_zero
    (eq_zero_of_evenCarrierMap_eq_zero (oddIndexParam_supported m c) hc)

theorem oddCarrierEvenIndexMap_injective (m : ℕ) :
    Function.Injective (oddCarrierEvenIndexMap m) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro c hc
  exact eq_zero_of_evenIndexParam_eq_zero
    (eq_zero_of_oddCarrierMap_eq_zero (evenIndexParam_supported m c) hc)

theorem oddCarrierOddIndexMap_injective (m : ℕ) :
    Function.Injective (oddCarrierOddIndexMap m) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro c hc
  exact eq_zero_of_oddIndexParam_eq_zero
    (eq_zero_of_oddCarrierMap_eq_zero (oddIndexParam_supported m c) hc)

/-! ## Exact inertia: even carrier -/

/-- Exact half-aperture orthogonal splitting of the even boundary-flat carrier
on `[-(m+2), m+2]`. -/
theorem evenBoundaryFlat_sourceHalf_split (m : ℕ) :
    let P := LinearMap.range (evenCarrierEvenIndexMap m)
    let Nn := LinearMap.range (evenCarrierOddIndexMap m)
    P ⊔ Nn = evenBoundaryFlatSubspace (m + 2) ∧
      finrank ℂ P = m / 2 + 1 ∧ finrank ℂ Nn = (m + 1) / 2 ∧
      (∀ u ∈ P, ∀ v ∈ Nn,
        sourceSesq (1 / 2) (m + 2) u v = 0 ∧ sourceSesq (1 / 2) (m + 2) v u = 0) ∧
      (∀ u ∈ P, u ≠ 0 → 0 < (sourceSesq (1 / 2) (m + 2) u u).re) ∧
      (∀ u ∈ Nn, u ≠ 0 → (sourceSesq (1 / 2) (m + 2) u u).re < 0) := by
  intro P Nn
  have hPdim : finrank ℂ P = m / 2 + 1 := by
    rw [LinearMap.finrank_range_of_inj (evenCarrierEvenIndexMap_injective m),
      Module.finrank_fin_fun]
  have hNdim : finrank ℂ Nn = (m + 1) / 2 := by
    rw [LinearMap.finrank_range_of_inj (evenCarrierOddIndexMap_injective m),
      Module.finrank_fin_fun]
  have horth : ∀ u ∈ P, ∀ v ∈ Nn,
      sourceSesq (1 / 2) (m + 2) u v = 0 ∧ sourceSesq (1 / 2) (m + 2) v u = 0 := by
    intro u hu v hv
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
    obtain ⟨c', rfl⟩ := LinearMap.mem_range.mp hv
    constructor
    · change sourceSesq (1 / 2) (m + 2) (evenCarrierMap m (evenIndexParam c))
        (evenCarrierMap m (oddIndexParam c')) = 0
      rw [sourceSesq_half_evenCarrierMap (evenIndexParam_supported m c),
        latticeSignOp_of_oddIndexSupported (oddIndexParam_oddIndexSupported c').sinSq,
        latticeInner_neg_right,
        latticeInner_even_odd_eq_zero _ (evenIndexParam_evenIndexSupported c).sinSq
          (oddIndexParam_oddIndexSupported c').sinSq, neg_zero]
    · change sourceSesq (1 / 2) (m + 2) (evenCarrierMap m (oddIndexParam c'))
        (evenCarrierMap m (evenIndexParam c)) = 0
      rw [sourceSesq_half_evenCarrierMap (oddIndexParam_supported m c'),
        latticeSignOp_of_evenIndexSupported (evenIndexParam_evenIndexSupported c).sinSq,
        latticeInner_odd_even_eq_zero _ (oddIndexParam_oddIndexSupported c').sinSq
          (evenIndexParam_evenIndexSupported c).sinSq]
  have hpos : ∀ u ∈ P, u ≠ 0 → 0 < (sourceSesq (1 / 2) (m + 2) u u).re := by
    intro u hu hne
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
    change 0 < (sourceSesq (1 / 2) (m + 2) (evenCarrierMap m (evenIndexParam c))
      (evenCarrierMap m (evenIndexParam c))).re
    have hq := evenIndexParam_supported m c
    rw [sourceSesq_half_evenCarrierMap hq,
      latticeSignOp_of_evenIndexSupported (evenIndexParam_evenIndexSupported c).sinSq]
    apply latticeInner_self_re_pos (hq.sinSq)
    intro hw
    apply hne
    change evenCarrierMap m (evenIndexParam c) = 0
    rw [eq_zero_of_latticeSinSq_eq_zero hq hw, evenCarrierMap_zero]
  have hneg : ∀ u ∈ Nn, u ≠ 0 → (sourceSesq (1 / 2) (m + 2) u u).re < 0 := by
    intro u hu hne
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
    change (sourceSesq (1 / 2) (m + 2) (evenCarrierMap m (oddIndexParam c))
      (evenCarrierMap m (oddIndexParam c))).re < 0
    have hq := oddIndexParam_supported m c
    rw [sourceSesq_half_evenCarrierMap hq,
      latticeSignOp_of_oddIndexSupported (oddIndexParam_oddIndexSupported c).sinSq,
      latticeInner_neg_right, Complex.neg_re, neg_lt_zero]
    apply latticeInner_self_re_pos (hq.sinSq)
    intro hw
    apply hne
    change evenCarrierMap m (oddIndexParam c) = 0
    rw [eq_zero_of_latticeSinSq_eq_zero hq hw, evenCarrierMap_zero]
  have hle : P ⊔ Nn ≤ evenBoundaryFlatSubspace (m + 2) := by
    apply sup_le
    · intro u hu
      obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
      exact evenCarrierMap_mem (evenIndexParam_supported m c) (evenIndexParam_symmetric c)
    · intro u hu
      obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
      exact evenCarrierMap_mem (oddIndexParam_supported m c) (oddIndexParam_symmetric c)
  have hinf : P ⊓ Nn = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hne
    have h1 := hpos x hx.1 hne
    have h2 := hneg x hx.2 hne
    linarith
  have hsupdim : finrank ℂ ↥(P ⊔ Nn) = m + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P Nn
    rw [hinf, finrank_bot, add_zero, hPdim, hNdim] at h
    omega
  refine ⟨?_, hPdim, hNdim, horth, hpos, hneg⟩
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [hsupdim, finrank_evenBoundaryFlatSubspace (m + 2) (by omega)]
  omega

/-! ## Exact inertia: odd carrier -/

/-- Exact half-aperture orthogonal splitting of the odd boundary-flat carrier
on `[-(m+2), m+2]`. -/
theorem oddBoundaryFlat_sourceHalf_split (m : ℕ) :
    let P := LinearMap.range (oddCarrierOddIndexMap m)
    let Nn := LinearMap.range (oddCarrierEvenIndexMap m)
    P ⊔ Nn = oddBoundaryFlatSubspace (m + 2) ∧
      finrank ℂ P = (m + 1) / 2 ∧ finrank ℂ Nn = m / 2 + 1 ∧
      (∀ u ∈ P, ∀ v ∈ Nn,
        sourceSesq (1 / 2) (m + 2) u v = 0 ∧ sourceSesq (1 / 2) (m + 2) v u = 0) ∧
      (∀ u ∈ P, u ≠ 0 → 0 < (sourceSesq (1 / 2) (m + 2) u u).re) ∧
      (∀ u ∈ Nn, u ≠ 0 → (sourceSesq (1 / 2) (m + 2) u u).re < 0) := by
  intro P Nn
  have hPdim : finrank ℂ P = (m + 1) / 2 := by
    rw [LinearMap.finrank_range_of_inj (oddCarrierOddIndexMap_injective m),
      Module.finrank_fin_fun]
  have hNdim : finrank ℂ Nn = m / 2 + 1 := by
    rw [LinearMap.finrank_range_of_inj (oddCarrierEvenIndexMap_injective m),
      Module.finrank_fin_fun]
  have horth : ∀ u ∈ P, ∀ v ∈ Nn,
      sourceSesq (1 / 2) (m + 2) u v = 0 ∧ sourceSesq (1 / 2) (m + 2) v u = 0 := by
    intro u hu v hv
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
    obtain ⟨c', rfl⟩ := LinearMap.mem_range.mp hv
    constructor
    · change sourceSesq (1 / 2) (m + 2) (oddCarrierMap m (oddIndexParam c))
        (oddCarrierMap m (evenIndexParam c')) = 0
      rw [sourceSesq_half_oddCarrierMap (oddIndexParam_supported m c),
        latticeSignOp_of_evenIndexSupported (evenIndexParam_evenIndexSupported c').sinSq,
        latticeInner_odd_even_eq_zero _ (oddIndexParam_oddIndexSupported c).sinSq
          (evenIndexParam_evenIndexSupported c').sinSq, neg_zero]
    · change sourceSesq (1 / 2) (m + 2) (oddCarrierMap m (evenIndexParam c'))
        (oddCarrierMap m (oddIndexParam c)) = 0
      rw [sourceSesq_half_oddCarrierMap (evenIndexParam_supported m c'),
        latticeSignOp_of_oddIndexSupported (oddIndexParam_oddIndexSupported c).sinSq,
        latticeInner_neg_right,
        latticeInner_even_odd_eq_zero _ (evenIndexParam_evenIndexSupported c').sinSq
          (oddIndexParam_oddIndexSupported c).sinSq, neg_zero, neg_zero]
  have hpos : ∀ u ∈ P, u ≠ 0 → 0 < (sourceSesq (1 / 2) (m + 2) u u).re := by
    intro u hu hne
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
    change 0 < (sourceSesq (1 / 2) (m + 2) (oddCarrierMap m (oddIndexParam c))
      (oddCarrierMap m (oddIndexParam c))).re
    have hq := oddIndexParam_supported m c
    rw [sourceSesq_half_oddCarrierMap hq,
      latticeSignOp_of_oddIndexSupported (oddIndexParam_oddIndexSupported c).sinSq,
      latticeInner_neg_right, neg_neg]
    apply latticeInner_self_re_pos (hq.sinSq)
    intro hw
    apply hne
    change oddCarrierMap m (oddIndexParam c) = 0
    rw [eq_zero_of_latticeSinSq_eq_zero hq hw, oddCarrierMap_zero]
  have hneg : ∀ u ∈ Nn, u ≠ 0 → (sourceSesq (1 / 2) (m + 2) u u).re < 0 := by
    intro u hu hne
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
    change (sourceSesq (1 / 2) (m + 2) (oddCarrierMap m (evenIndexParam c))
      (oddCarrierMap m (evenIndexParam c))).re < 0
    have hq := evenIndexParam_supported m c
    rw [sourceSesq_half_oddCarrierMap hq,
      latticeSignOp_of_evenIndexSupported (evenIndexParam_evenIndexSupported c).sinSq,
      Complex.neg_re, neg_lt_zero]
    apply latticeInner_self_re_pos (hq.sinSq)
    intro hw
    apply hne
    change oddCarrierMap m (evenIndexParam c) = 0
    rw [eq_zero_of_latticeSinSq_eq_zero hq hw, oddCarrierMap_zero]
  have hle : P ⊔ Nn ≤ oddBoundaryFlatSubspace (m + 2) := by
    apply sup_le
    · intro u hu
      obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
      exact oddCarrierMap_mem (oddIndexParam_supported m c) (oddIndexParam_symmetric c)
    · intro u hu
      obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
      exact oddCarrierMap_mem (evenIndexParam_supported m c) (evenIndexParam_symmetric c)
  have hinf : P ⊓ Nn = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hne
    have h1 := hpos x hx.1 hne
    have h2 := hneg x hx.2 hne
    linarith
  have hsupdim : finrank ℂ ↥(P ⊔ Nn) = m + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P Nn
    rw [hinf, finrank_bot, add_zero, hPdim, hNdim] at h
    omega
  refine ⟨?_, hPdim, hNdim, horth, hpos, hneg⟩
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [hsupdim, finrank_oddBoundaryFlatSubspace (m + 2) (by omega)]
  omega

/-! ## Registry-facing exact inertia theorems -/

/-- **Exact even source inertia at `ω = 1/2`, every `K ≥ 2`.**  With
`d = K - 1`: the half-aperture source form on `evenBoundaryFlatSubspace K` is
nondegenerate, admits an orthogonal positive/negative splitting of dimensions
`K/2 = ⌈d/2⌉` and `(K-1)/2 = ⌊d/2⌋`, and these are the maximal dimensions of
positive and negative definite subspaces. -/
theorem evenBoundaryFlat_sourceHalf_exactInertia (K : ℕ) (hK : 2 ≤ K) :
    ∃ P Nn : Submodule ℂ (Fin (2 * K + 1) → ℂ),
      P ⊔ Nn = evenBoundaryFlatSubspace K ∧
      finrank ℂ P = K / 2 ∧ finrank ℂ Nn = (K - 1) / 2 ∧
      (∀ u ∈ P, ∀ v ∈ Nn, sourceSesq (1 / 2) K u v = 0 ∧ sourceSesq (1 / 2) K v u = 0) ∧
      (∀ u ∈ P, u ≠ 0 → 0 < (quadraticForm (sourceMatrix (1 / 2) K) u).re) ∧
      (∀ u ∈ Nn, u ≠ 0 → (quadraticForm (sourceMatrix (1 / 2) K) u).re < 0) ∧
      (∀ v ∈ evenBoundaryFlatSubspace K,
        (∀ w ∈ evenBoundaryFlatSubspace K, sourceSesq (1 / 2) K v w = 0) → v = 0) ∧
      (∀ W : Submodule ℂ (Fin (2 * K + 1) → ℂ), W ≤ evenBoundaryFlatSubspace K →
        (∀ w ∈ W, w ≠ 0 → 0 < (quadraticForm (sourceMatrix (1 / 2) K) w).re) →
          finrank ℂ W ≤ K / 2) ∧
      (∀ W : Submodule ℂ (Fin (2 * K + 1) → ℂ), W ≤ evenBoundaryFlatSubspace K →
        (∀ w ∈ W, w ≠ 0 → (quadraticForm (sourceMatrix (1 / 2) K) w).re < 0) →
          finrank ℂ W ≤ (K - 1) / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 2 := ⟨K - 2, by omega⟩
  obtain ⟨hsup, hP, hN, horth, hpos, hneg⟩ := evenBoundaryFlat_sourceHalf_split m
  have hinert := exactInertia_of_orthogonal_split (sourceSesq (1 / 2) (m + 2))
    (fun x y z => sourceSesq_add_left _ _ x y z) _ _ _ hsup horth hpos hneg
  refine ⟨_, _, hsup, by rw [hP]; omega, by rw [hN]; omega, horth, hpos, hneg,
    hinert.1, ?_, ?_⟩
  · intro W hW hWpos
    have := hinert.2.1 W hW hWpos
    rw [hP] at this
    omega
  · intro W hW hWneg
    have := hinert.2.2 W hW hWneg
    rw [hN] at this
    omega

/-- **Exact odd source inertia at `ω = 1/2`, every `K ≥ 2`.**  With
`d = K - 1`: positive index `(K-1)/2 = ⌊d/2⌋`, negative index `K/2 = ⌈d/2⌉`,
nullity zero. -/
theorem oddBoundaryFlat_sourceHalf_exactInertia (K : ℕ) (hK : 2 ≤ K) :
    ∃ P Nn : Submodule ℂ (Fin (2 * K + 1) → ℂ),
      P ⊔ Nn = oddBoundaryFlatSubspace K ∧
      finrank ℂ P = (K - 1) / 2 ∧ finrank ℂ Nn = K / 2 ∧
      (∀ u ∈ P, ∀ v ∈ Nn, sourceSesq (1 / 2) K u v = 0 ∧ sourceSesq (1 / 2) K v u = 0) ∧
      (∀ u ∈ P, u ≠ 0 → 0 < (quadraticForm (sourceMatrix (1 / 2) K) u).re) ∧
      (∀ u ∈ Nn, u ≠ 0 → (quadraticForm (sourceMatrix (1 / 2) K) u).re < 0) ∧
      (∀ v ∈ oddBoundaryFlatSubspace K,
        (∀ w ∈ oddBoundaryFlatSubspace K, sourceSesq (1 / 2) K v w = 0) → v = 0) ∧
      (∀ W : Submodule ℂ (Fin (2 * K + 1) → ℂ), W ≤ oddBoundaryFlatSubspace K →
        (∀ w ∈ W, w ≠ 0 → 0 < (quadraticForm (sourceMatrix (1 / 2) K) w).re) →
          finrank ℂ W ≤ (K - 1) / 2) ∧
      (∀ W : Submodule ℂ (Fin (2 * K + 1) → ℂ), W ≤ oddBoundaryFlatSubspace K →
        (∀ w ∈ W, w ≠ 0 → (quadraticForm (sourceMatrix (1 / 2) K) w).re < 0) →
          finrank ℂ W ≤ K / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 2 := ⟨K - 2, by omega⟩
  obtain ⟨hsup, hP, hN, horth, hpos, hneg⟩ := oddBoundaryFlat_sourceHalf_split m
  have hinert := exactInertia_of_orthogonal_split (sourceSesq (1 / 2) (m + 2))
    (fun x y z => sourceSesq_add_left _ _ x y z) _ _ _ hsup horth hpos hneg
  refine ⟨_, _, hsup, by rw [hP]; omega, by rw [hN]; omega, horth, hpos, hneg,
    hinert.1, ?_, ?_⟩
  · intro W hW hWpos
    have := hinert.2.1 W hW hWpos
    rw [hP] at this
    omega
  · intro W hW hWneg
    have := hinert.2.2 W hW hWneg
    rw [hN] at this
    omega

/-- Corollary: for `K ≥ 3` both parity carriers are strictly indefinite at the
half aperture; for `K = 2` the even carrier is positive and the odd carrier
negative (one-dimensional). -/
theorem parityBoundaryFlat_sourceHalf_indefinite (K : ℕ) (hK : 3 ≤ K) :
    (∃ u ∈ evenBoundaryFlatSubspace K, 0 < (quadraticForm (sourceMatrix (1 / 2) K) u).re) ∧
    (∃ u ∈ evenBoundaryFlatSubspace K, (quadraticForm (sourceMatrix (1 / 2) K) u).re < 0) ∧
    (∃ u ∈ oddBoundaryFlatSubspace K, 0 < (quadraticForm (sourceMatrix (1 / 2) K) u).re) ∧
    (∃ u ∈ oddBoundaryFlatSubspace K, (quadraticForm (sourceMatrix (1 / 2) K) u).re < 0) := by
  have hex : ∀ (W : Submodule ℂ (Fin (2 * K + 1) → ℂ)), 0 < finrank ℂ W →
      ∃ w ∈ W, w ≠ 0 := by
    intro W hW
    obtain ⟨w, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Submodule.one_le_finrank_iff.mp hW)
    exact ⟨w, hw.1, hw.2⟩
  obtain ⟨Pe, Ne, hsupe, hPe, hNe, -, hpose, hnege, -⟩ :=
    evenBoundaryFlat_sourceHalf_exactInertia K (by omega)
  obtain ⟨Po, No, hsupo, hPo, hNo, -, hposo, hnego, -⟩ :=
    oddBoundaryFlat_sourceHalf_exactInertia K (by omega)
  obtain ⟨a, ha, ha0⟩ := hex Pe (by rw [hPe]; omega)
  obtain ⟨b, hb, hb0⟩ := hex Ne (by rw [hNe]; omega)
  obtain ⟨c, hc, hc0⟩ := hex Po (by rw [hPo]; omega)
  obtain ⟨d, hd, hd0⟩ := hex No (by rw [hNo]; omega)
  exact ⟨⟨a, hsupe ▸ Submodule.mem_sup_left ha, hpose a ha ha0⟩,
    ⟨b, hsupe ▸ Submodule.mem_sup_right hb, hnege b hb hb0⟩,
    ⟨c, hsupo ▸ Submodule.mem_sup_left hc, hposo c hc hc0⟩,
    ⟨d, hsupo ▸ Submodule.mem_sup_right hd, hnego d hd hd0⟩⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.exactInertia_of_orthogonal_split
#print axioms Zeta23.CCM.sourceSesq_half_evenCarrierMap
#print axioms Zeta23.CCM.sourceSesq_half_oddCarrierMap
#print axioms Zeta23.CCM.evenBoundaryFlat_sourceHalf_split
#print axioms Zeta23.CCM.oddBoundaryFlat_sourceHalf_split
#print axioms Zeta23.CCM.evenBoundaryFlat_sourceHalf_exactInertia
#print axioms Zeta23.CCM.oddBoundaryFlat_sourceHalf_exactInertia
#print axioms Zeta23.CCM.parityBoundaryFlat_sourceHalf_indefinite
