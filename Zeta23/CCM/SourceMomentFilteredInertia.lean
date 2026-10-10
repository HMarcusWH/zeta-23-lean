import Zeta23.CCM.SourceParityExactInertia
import Zeta23.CCM.SourceMomentVandermondeFiltration

noncomputable section

namespace Zeta23.CCM

open Matrix Finset Module
open scoped BigOperators ComplexConjugate

/-!
# POST284-M18: filtered parity source inertia at the half aperture

Moment-filtered parity carriers:

* even, level `s ≥ 1`: `E_s(K) = {u even : M_0 = ⋯ = M_{2s-1} = 0}`, the
  coefficient form of `C_u = (1 - cos t)^s Q(cos t)`, complex dimension
  `K - s + 1`;
* odd, level `s ≥ 0`: `O_s(K) = {u odd : M_0 = ⋯ = M_{2s} = 0}`, the
  coefficient form of `T_u = sin t (1 - cos t)^s Q(cos t)`, complex dimension
  `K - s`.

At `ω = 1/2` the shift-operator identity gives
`B((1-cos)^s q₁, (1-cos)^s q₂) = ⟪q₁, (sin²)^s (-1)^n q₂⟫` and
`B(i sin (1-cos)^s q₁, i sin (1-cos)^s q₂) = -⟪q₁, (sin²)^{s+1} (-1)^n q₂⟫`,
so with `d` the carrier dimension the inertia is exactly
`(⌈d/2⌉, ⌊d/2⌋, 0)` on even carriers and `(⌊d/2⌋, ⌈d/2⌉, 0)` on odd
carriers, for every level.  In particular every filtered carrier of dimension
`≥ 2` is indefinite at `ω = 1/2`.

Scope: elementary `sourceMatrix (1/2)` only; the interior `0 < ω < 1/2`
(Andréief) is OPEN; nothing concerns the canonical operator or RH.
-/

/-! ## Operators as linear endomorphisms -/

/-- `1 - cos` as a linear endomorphism of lattice sequences. -/
def oneSubCosLM : Module.End ℂ (ℤ → ℂ) where
  toFun := latticeOneSubCos
  map_add' := latticeOneSubCos_add
  map_smul' c f := latticeOneSubCos_smul c f

/-- `1 + cos` as a linear endomorphism. -/
def onePlusCosLM : Module.End ℂ (ℤ → ℂ) where
  toFun := latticeOnePlusCos
  map_add' := latticeOnePlusCos_add
  map_smul' c f := latticeOnePlusCos_smul c f

/-- `sin² = (1 - cos)(1 + cos)` as a linear endomorphism. -/
def sinSqLM : Module.End ℂ (ℤ → ℂ) := oneSubCosLM * onePlusCosLM

/-- The sign operator `(-1)^n` as a linear endomorphism. -/
def signLM : Module.End ℂ (ℤ → ℂ) where
  toFun := latticeSignOp
  map_add' f g := by funext n; simp [latticeSignOp, mul_add]
  map_smul' c f := by funext n; simp [latticeSignOp]; ring

@[simp] theorem oneSubCosLM_apply (f : ℤ → ℂ) : oneSubCosLM f = latticeOneSubCos f := rfl
@[simp] theorem onePlusCosLM_apply (f : ℤ → ℂ) : onePlusCosLM f = latticeOnePlusCos f := rfl
@[simp] theorem signLM_apply (f : ℤ → ℂ) : signLM f = latticeSignOp f := rfl

theorem sinSqLM_apply (f : ℤ → ℂ) : sinSqLM f = latticeSinSq f := rfl

theorem commute_oneSubCosLM_onePlusCosLM : Commute oneSubCosLM onePlusCosLM := by
  apply LinearMap.ext
  intro f
  exact latticeOneSubCos_onePlusCos_comm f

theorem signLM_semiconj_oneSubCos : SemiconjBy signLM oneSubCosLM onePlusCosLM := by
  apply LinearMap.ext
  intro f
  exact latticeSignOp_oneSubCos f

theorem signLM_semiconj_onePlusCos : SemiconjBy signLM onePlusCosLM oneSubCosLM := by
  apply LinearMap.ext
  intro f
  exact latticeSignOp_onePlusCos f

theorem signLM_commute_sinSq : Commute signLM sinSqLM := by
  apply LinearMap.ext
  intro f
  exact latticeSignOp_sinSq f

/-! ## Supports of powers -/

theorem LatticeSupported.oneSubCosPow {N : ℕ} {f : ℤ → ℂ} (hf : LatticeSupported N f)
    (s : ℕ) : LatticeSupported (N + s) ((oneSubCosLM ^ s) f) := by
  induction s with
  | zero => simpa using hf
  | succ s ih =>
      rw [pow_succ', LinearMap.mul_apply]
      exact ih.oneSubCos

theorem LatticeSupported.onePlusCosPow {N : ℕ} {f : ℤ → ℂ} (hf : LatticeSupported N f)
    (s : ℕ) : LatticeSupported (N + s) ((onePlusCosLM ^ s) f) := by
  induction s with
  | zero => simpa using hf
  | succ s ih =>
      rw [pow_succ', LinearMap.mul_apply]
      exact ih.onePlusCos

theorem LatticeSupported.sinSqPow {N : ℕ} {f : ℤ → ℂ} (hf : LatticeSupported N f)
    (s : ℕ) : LatticeSupported (N + 2 * s) ((sinSqLM ^ s) f) := by
  induction s with
  | zero => simpa using hf
  | succ s ih =>
      rw [pow_succ', LinearMap.mul_apply, sinSqLM_apply]
      have h := ih.sinSq
      rwa [show N + 2 * s + 2 = N + 2 * (s + 1) by ring] at h

theorem EvenIndexSupported.sinSqPow {f : ℤ → ℂ} (hf : EvenIndexSupported f) (s : ℕ) :
    EvenIndexSupported ((sinSqLM ^ s) f) := by
  induction s with
  | zero => simpa using hf
  | succ s ih =>
      rw [pow_succ', LinearMap.mul_apply, sinSqLM_apply]
      exact ih.sinSq

theorem OddIndexSupported.sinSqPow {f : ℤ → ℂ} (hf : OddIndexSupported f) (s : ℕ) :
    OddIndexSupported ((sinSqLM ^ s) f) := by
  induction s with
  | zero => simpa using hf
  | succ s ih =>
      rw [pow_succ', LinearMap.mul_apply, sinSqLM_apply]
      exact ih.sinSq

theorem EvenIndexSupported.signOp {f : ℤ → ℂ} (hf : EvenIndexSupported f) :
    EvenIndexSupported (latticeSignOp f) := by
  intro n hn; simp [latticeSignOp, hf n hn]

theorem OddIndexSupported.signOp {f : ℤ → ℂ} (hf : OddIndexSupported f) :
    OddIndexSupported (latticeSignOp f) := by
  intro n hn; simp [latticeSignOp, hf n hn]

theorem LatticeSymmetric.oneSubCosPow {f : ℤ → ℂ} (hf : LatticeSymmetric f) (s : ℕ) :
    LatticeSymmetric ((oneSubCosLM ^ s) f) := by
  induction s with
  | zero => simpa using hf
  | succ s ih =>
      rw [pow_succ', LinearMap.mul_apply]
      exact ih.oneSubCos

/-! ## Box adjointness of powers -/

theorem latticeInner_oneSubCos_left_of_lt {N M : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (h : N < M) (g : ℤ → ℂ) :
    latticeInner M (latticeOneSubCos f) g = latticeInner M f (latticeOneSubCos g) := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  exact latticeInner_oneSubCos_left (hf.mono (by omega)) g

theorem latticeInner_onePlusCos_left_of_lt {N M : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (h : N < M) (g : ℤ → ℂ) :
    latticeInner M (latticeOnePlusCos f) g = latticeInner M f (latticeOnePlusCos g) := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  exact latticeInner_onePlusCos_left (hf.mono (by omega)) g

theorem latticeInner_latticeSin_left_of_lt {N M : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (h : N < M) (g : ℤ → ℂ) :
    latticeInner M (latticeSin f) g = -latticeInner M f (latticeSin g) := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  exact latticeInner_latticeSin_left (hf.mono (by omega)) g

theorem latticePair_oneSubCos_of_lt {N M : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (h : N < M) (p : ℤ → ℂ) :
    latticePair M p (latticeOneSubCos f) = latticePair M (latticeOneSubCos p) f := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  exact latticePair_oneSubCos (hf.mono (by omega)) p

theorem latticeInner_oneSubCosPow_left {N M : ℕ} {a : ℤ → ℂ}
    (ha : LatticeSupported N a) (s : ℕ) (hM : N + s ≤ M) (g : ℤ → ℂ) :
    latticeInner M ((oneSubCosLM ^ s) a) g = latticeInner M a ((oneSubCosLM ^ s) g) := by
  induction s generalizing g with
  | zero => simp
  | succ s ih =>
      rw [pow_succ', LinearMap.mul_apply, oneSubCosLM_apply,
        latticeInner_oneSubCos_left_of_lt (ha.oneSubCosPow s) (by omega),
        ih (by omega), ← oneSubCosLM_apply, ← LinearMap.mul_apply, ← pow_succ]

theorem latticeInner_onePlusCosPow_left {N M : ℕ} {a : ℤ → ℂ}
    (ha : LatticeSupported N a) (s : ℕ) (hM : N + s ≤ M) (g : ℤ → ℂ) :
    latticeInner M ((onePlusCosLM ^ s) a) g = latticeInner M a ((onePlusCosLM ^ s) g) := by
  induction s generalizing g with
  | zero => simp
  | succ s ih =>
      rw [pow_succ', LinearMap.mul_apply, onePlusCosLM_apply,
        latticeInner_onePlusCos_left_of_lt (ha.onePlusCosPow s) (by omega),
        ih (by omega), ← onePlusCosLM_apply, ← LinearMap.mul_apply, ← pow_succ]

theorem latticeInner_sinSq_left {N M : ℕ} {a : ℤ → ℂ}
    (ha : LatticeSupported N a) (hM : N + 2 ≤ M) (g : ℤ → ℂ) :
    latticeInner M (latticeSinSq a) g = latticeInner M a (latticeSinSq g) := by
  unfold latticeSinSq
  rw [latticeInner_oneSubCos_left_of_lt ha.onePlusCos (by omega),
    latticeInner_onePlusCos_left_of_lt ha (by omega), latticeOneSubCos_onePlusCos_comm]

theorem latticeInner_sinSqPow_left {N M : ℕ} {a : ℤ → ℂ}
    (ha : LatticeSupported N a) (s : ℕ) (hM : N + 2 * s ≤ M) (g : ℤ → ℂ) :
    latticeInner M ((sinSqLM ^ s) a) g = latticeInner M a ((sinSqLM ^ s) g) := by
  induction s generalizing g with
  | zero => simp
  | succ s ih =>
      rw [pow_succ', LinearMap.mul_apply, sinSqLM_apply,
        latticeInner_sinSq_left (ha.sinSqPow s) (by omega),
        ih (by omega), ← sinSqLM_apply, ← LinearMap.mul_apply, ← pow_succ]

/-! ## Positivity of `⟪q, (sin²)^t q⟫` -/

/-- `⟪w, sin² w⟫ = ⟪i sin w, i sin w⟫`. -/
theorem latticeInner_sinSq_self {N M : ℕ} {w : ℤ → ℂ}
    (hw : LatticeSupported N w) (hM : N < M) :
    latticeInner M w (latticeSinSq w) = latticeInner M (latticeSin w) (latticeSin w) := by
  rw [latticeInner_latticeSin_left_of_lt hw hM, latticeSin_latticeSin,
    latticeInner_neg_right, neg_neg]

theorem eq_zero_of_sinSqPow_eq_zero {m : ℕ} {q : ℤ → ℂ} (hq : LatticeSupported m q)
    (s : ℕ) (h : (sinSqLM ^ s) q = 0) : q = 0 := by
  induction s with
  | zero => simpa using h
  | succ s ih =>
      rw [pow_succ', LinearMap.mul_apply, sinSqLM_apply] at h
      exact ih (eq_zero_of_latticeSinSq_eq_zero (hq.sinSqPow s) h)

/-- `⟪q, (sin²)^t q⟫ > 0` for every nonzero box-supported `q`. -/
theorem latticeInner_sinSqPow_self_re_pos {m M : ℕ} {q : ℤ → ℂ}
    (hq : LatticeSupported m q) (hne : q ≠ 0) (t : ℕ) (hM : m + t ≤ M) :
    0 < (latticeInner M q ((sinSqLM ^ t) q)).re := by
  rcases Nat.even_or_odd t with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · rw [pow_add, LinearMap.mul_apply, ← latticeInner_sinSqPow_left hq σ (by omega)]
    have hw := hq.sinSqPow σ
    apply latticeInner_self_re_pos (hw.mono (by omega))
    intro h0
    exact hne (eq_zero_of_sinSqPow_eq_zero hq σ h0)
  · rw [show 2 * σ + 1 = σ + (1 + σ) by ring, pow_add, pow_add, pow_one,
      LinearMap.mul_apply, LinearMap.mul_apply,
      ← latticeInner_sinSqPow_left hq σ (by omega), sinSqLM_apply]
    have hw := hq.sinSqPow σ
    rw [latticeInner_sinSq_self hw (by omega)]
    apply latticeInner_self_re_pos (hw.latticeSin.mono (by omega))
    intro h0
    exact hne (eq_zero_of_sinSqPow_eq_zero hq σ (eq_zero_of_latticeSin_eq_zero hw h0))

/-! ## Core half-aperture forms on filtered images -/

theorem oneSubCosPow_mul_sinSq_mul_onePlusCosPow (s : ℕ) :
    oneSubCosLM ^ s * sinSqLM * onePlusCosLM ^ s = sinSqLM ^ (s + 1) := by
  rw [sinSqLM, commute_oneSubCosLM_onePlusCosLM.mul_pow, pow_succ, pow_succ']
  simp only [mul_assoc]

theorem latticeSignOp_oneSubCosPow (s : ℕ) (f : ℤ → ℂ) :
    latticeSignOp ((oneSubCosLM ^ s) f) = (onePlusCosLM ^ s) (latticeSignOp f) := by
  have h := (signLM_semiconj_oneSubCos.pow_right s).eq
  exact LinearMap.congr_fun h f

theorem latticeSignOp_sinSqPow (s : ℕ) (f : ℤ → ℂ) :
    latticeSignOp ((sinSqLM ^ s) f) = (sinSqLM ^ s) (latticeSignOp f) := by
  have h := (signLM_commute_sinSq.pow_right s).eq
  exact LinearMap.congr_fun h f

theorem latticeInner_signOp_eq_sum (N : ℕ) (f g : ℤ → ℂ) :
    ∑ n ∈ latticeBox N, latticeSign n * (conj (f n) * g n) =
      latticeInner N f (latticeSignOp g) := by
  unfold latticeInner latticeSignOp
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Even filtered core:
`B((1-cos)^s q₁, (1-cos)^s q₂) = ⟪q₁, (sin²)^s (-1)^n q₂⟫`. -/
theorem sourceSesq_half_oneSubCosPow {m s : ℕ} {q₁ q₂ : ℤ → ℂ}
    (h₁ : LatticeSupported m q₁) :
    sourceSesq (1 / 2) (m + s) (ofLattice (m + s) ((oneSubCosLM ^ s) q₁))
        (ofLattice (m + s) ((oneSubCosLM ^ s) q₂)) =
      latticeInner (m + s) q₁ ((sinSqLM ^ s) (latticeSignOp q₂)) := by
  rw [sourceSesq_half_ofLattice, latticeInner_signOp_eq_sum, latticeSignOp_oneSubCosPow,
    latticeInner_oneSubCosPow_left h₁ s le_rfl, ← LinearMap.mul_apply,
    ← commute_oneSubCosLM_onePlusCosLM.mul_pow]
  rfl

/-- Odd filtered core:
`B(i sin (1-cos)^s q₁, i sin (1-cos)^s q₂) = -⟪q₁, (sin²)^(s+1) (-1)^n q₂⟫`. -/
theorem sourceSesq_half_sinOneSubCosPow {m s : ℕ} {q₁ q₂ : ℤ → ℂ}
    (h₁ : LatticeSupported m q₁) :
    sourceSesq (1 / 2) (m + s + 1)
        (ofLattice (m + s + 1) (latticeSin ((oneSubCosLM ^ s) q₁)))
        (ofLattice (m + s + 1) (latticeSin ((oneSubCosLM ^ s) q₂))) =
      -latticeInner (m + s + 1) q₁ ((sinSqLM ^ (s + 1)) (latticeSignOp q₂)) := by
  have ha := h₁.oneSubCosPow s
  rw [sourceSesq_half_ofLattice, latticeInner_signOp_eq_sum, latticeSignOp_latticeSin,
    latticeInner_neg_right, latticeInner_latticeSin_left_of_lt ha (by omega), neg_neg,
    latticeSin_latticeSin, latticeInner_neg_right, latticeSignOp_oneSubCosPow,
    latticeInner_oneSubCosPow_left h₁ s (by omega), ← sinSqLM_apply,
    ← LinearMap.mul_apply, ← LinearMap.mul_apply, oneSubCosPow_mul_sinSq_mul_onePlusCosPow]

/-! ## Moments of filtered images -/

theorem latticeOneSubCos_monomial (k : ℕ) :
    latticeOneSubCos (fun n : ℤ => (n : ℂ) ^ k) =
      fun n => ∑ j ∈ Finset.range (k - 1),
        (-((k.choose j : ℂ) * (1 + (-1) ^ (k - j))) / 2) * (n : ℂ) ^ j := by
  funext n
  simp only [latticeOneSubCos, latticeCos]
  push_cast
  have h1 : ((n : ℂ) + 1) ^ k =
      ∑ j ∈ Finset.range (k + 1), (n : ℂ) ^ j * (k.choose j : ℂ) := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro j _
    simp
  have h2 : ((n : ℂ) - 1) ^ k =
      ∑ j ∈ Finset.range (k + 1), (n : ℂ) ^ j * ((-1) ^ (k - j) * (k.choose j : ℂ)) := by
    rw [sub_eq_add_neg, add_pow]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h1, h2]
  rcases k with _ | k
  · simp
  · rw [Finset.sum_range_succ, Finset.sum_range_succ (fun j => (n : ℂ) ^ j * _),
      Finset.sum_range_succ, Finset.sum_range_succ (fun j => (n : ℂ) ^ j * ((-1) ^ (k + 1 - j) * _))]
    simp only [Nat.add_sub_cancel, Nat.choose_self, Nat.sub_self, pow_zero,
      Nat.choose_succ_self_right, show k + 1 - k = 1 by omega, pow_one]
    have hsum : ∑ j ∈ Finset.range k,
        (-((((k + 1).choose j : ℕ) : ℂ) * (1 + (-1) ^ (k + 1 - j))) / 2) * (n : ℂ) ^ j =
        -((∑ j ∈ Finset.range k, (n : ℂ) ^ j * (((k + 1).choose j : ℕ) : ℂ)) +
          ∑ j ∈ Finset.range k,
            (n : ℂ) ^ j * ((-1) ^ (k + 1 - j) * (((k + 1).choose j : ℕ) : ℂ))) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum]
    push_cast
    ring

theorem latticeSin_monomial (k : ℕ) :
    latticeSin (fun n : ℤ => (n : ℂ) ^ k) =
      fun n => ∑ j ∈ Finset.range k,
        (-((k.choose j : ℂ) * (1 - (-1) ^ (k - j))) / 2) * (n : ℂ) ^ j := by
  funext n
  simp only [latticeSin]
  push_cast
  have h1 : ((n : ℂ) + 1) ^ k =
      ∑ j ∈ Finset.range (k + 1), (n : ℂ) ^ j * (k.choose j : ℂ) := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro j _
    simp
  have h2 : ((n : ℂ) - 1) ^ k =
      ∑ j ∈ Finset.range (k + 1), (n : ℂ) ^ j * ((-1) ^ (k - j) * (k.choose j : ℂ)) := by
    rw [sub_eq_add_neg, add_pow]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h1, h2, Finset.sum_range_succ, Finset.sum_range_succ (fun j => (n : ℂ) ^ j * _)]
  simp only [Nat.choose_self, Nat.sub_self, pow_zero]
  have hsum : ∑ j ∈ Finset.range k,
      (-((k.choose j : ℂ) * (1 - (-1) ^ (k - j))) / 2) * (n : ℂ) ^ j =
      ((∑ j ∈ Finset.range k, (n : ℂ) ^ j * ((-1) ^ (k - j) * (k.choose j : ℂ))) -
        ∑ j ∈ Finset.range k, (n : ℂ) ^ j * (k.choose j : ℂ)) / 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  push_cast
  ring

theorem latticePair_sum_left (M : ℕ) {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (p : ι → ℤ → ℂ) (f : ℤ → ℂ) :
    latticePair M (fun n => ∑ j ∈ S, c j * p j n) f =
      ∑ j ∈ S, c j * latticePair M (p j) f := by
  unfold latticePair
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- `(1 - cos)^s` kills the moments of order `< 2s`. -/
theorem latticePair_monomial_oneSubCosPow {m M : ℕ} {q : ℤ → ℂ}
    (hq : LatticeSupported m q) (s : ℕ) (hM : m + s ≤ M) :
    ∀ k, k < 2 * s →
      latticePair M (fun n : ℤ => (n : ℂ) ^ k) ((oneSubCosLM ^ s) q) = 0 := by
  induction s with
  | zero => intro k hk; omega
  | succ s ih =>
      intro k hk
      rw [pow_succ', LinearMap.mul_apply, oneSubCosLM_apply,
        latticePair_oneSubCos_of_lt (hq.oneSubCosPow s) (by omega),
        latticeOneSubCos_monomial, latticePair_sum_left]
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_range] at hj
      rw [ih (by omega) j (by omega), mul_zero]

/-- `i sin (1 - cos)^s` kills the moments of order `< 2s+1`. -/
theorem latticePair_monomial_sinOneSubCosPow {m M : ℕ} {q : ℤ → ℂ}
    (hq : LatticeSupported m q) (s : ℕ) (hM : m + s + 1 ≤ M) :
    ∀ k, k < 2 * s + 1 →
      latticePair M (fun n : ℤ => (n : ℂ) ^ k) (latticeSin ((oneSubCosLM ^ s) q)) = 0 := by
  intro k hk
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  rw [latticePair_latticeSin ((hq.oneSubCosPow s).mono (by omega)), latticeSin_monomial,
    latticePair_sum_left]
  rw [neg_eq_zero]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  rw [latticePair_monomial_oneSubCosPow hq s (by omega) j (by omega), mul_zero]

/-! ## Filtered carriers -/

/-- Even moment-filtered carrier of level `s`. -/
def evenFilteredCarrier (K s : ℕ) : Submodule ℂ (Fin (2 * K + 1) → ℂ) :=
  evenCoefficientSubspace K ⊓ momentFiltration K (2 * s)

/-- Odd moment-filtered carrier of level `s`. -/
def oddFilteredCarrier (K s : ℕ) : Submodule ℂ (Fin (2 * K + 1) → ℂ) :=
  oddCoefficientSubspace K ⊓ momentFiltration K (2 * s + 1)

theorem centeredMoment_ofLattice_eq_latticePair (N k : ℕ) (f : ℤ → ℂ) :
    centeredMoment N k (ofLattice N f) = latticePair N (fun n : ℤ => (n : ℂ) ^ k) f :=
  centeredMoment_ofLattice N k f

theorem evenFilteredMap_mem {m s : ℕ} {q : ℤ → ℂ}
    (hq : LatticeSupported m q) (hsym : LatticeSymmetric q) :
    ofLattice (m + s) ((oneSubCosLM ^ s) q) ∈ evenFilteredCarrier (m + s) s := by
  refine ⟨?_, ?_⟩
  · rw [mem_evenCoefficientSubspace_iff, reverseCoefficients_ofLattice]
    congr 1
    funext n
    exact hsym.oneSubCosPow s n
  · rw [mem_momentFiltration_iff]
    intro k hk
    rw [centeredMoment_ofLattice_eq_latticePair]
    exact latticePair_monomial_oneSubCosPow hq s le_rfl k hk

theorem oddFilteredMap_mem {m s : ℕ} {q : ℤ → ℂ}
    (hq : LatticeSupported m q) (hsym : LatticeSymmetric q) :
    ofLattice (m + s + 1) (latticeSin ((oneSubCosLM ^ s) q)) ∈
      oddFilteredCarrier (m + s + 1) s := by
  refine ⟨?_, ?_⟩
  · rw [mem_oddCoefficientSubspace_iff, reverseCoefficients_ofLattice]
    funext i
    simp only [ofLattice_apply, Pi.neg_apply]
    exact (hsym.oneSubCosPow s).latticeSin _
  · rw [mem_momentFiltration_iff]
    intro k hk
    rw [centeredMoment_ofLattice_eq_latticePair]
    exact latticePair_monomial_sinOneSubCosPow hq s le_rfl k hk

/-- A box-supported vector with all moments of order `≤ 2r` zero in a box of
size `r` vanishes. -/
theorem eq_zero_of_supported_of_moments {K r : ℕ} (hr : r ≤ K) {u : Fin (2 * K + 1) → ℂ}
    (hsupp : LatticeSupported r (toLattice K u))
    (hmom : ∀ k, k ≤ 2 * r → centeredMoment K k u = 0) : u = 0 := by
  set f := toLattice K u with hf
  have hsmall : ofLattice r f = 0 := by
    apply eq_zero_of_centeredMoment_eq_zero
    intro k hk
    rw [centeredMoment_ofLattice, ← sum_latticeBox_eq_of_vanish hr]
    · have := hmom k hk
      rw [← ofLattice_toLattice K u, centeredMoment_ofLattice] at this
      exact this
    · intro n hn
      rw [hsupp n hn, mul_zero]
  have hf0 : f = 0 := eq_zero_of_ofLattice_eq_zero hsupp hsmall
  rw [← ofLattice_toLattice K u, ← hf, hf0]
  rfl

/-- Dimension upper bound for the even filtered carrier. -/
theorem finrank_evenFilteredCarrier_le (m s : ℕ) (hs : 1 ≤ s) :
    finrank ℂ (evenFilteredCarrier (m + s) s) ≤ m + 1 := by
  let idx : Fin (m + 1) → Fin (2 * (m + s) + 1) := fun j => ⟨2 * s + m + j, by omega⟩
  let Φ : evenFilteredCarrier (m + s) s →ₗ[ℂ] (Fin (m + 1) → ℂ) :=
    (LinearMap.pi fun j => LinearMap.proj (idx j)) ∘ₗ (evenFilteredCarrier (m + s) s).subtype
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    have hzero : ∀ j : Fin (m + 1), (u : Fin (2 * (m + s) + 1) → ℂ) (idx j) = 0 := by
      intro j
      exact congrFun (LinearMap.mem_ker.mp hu) j
    obtain ⟨heven, hmom⟩ := u.2
    rw [mem_evenCoefficientSubspace_iff] at heven
    rw [mem_momentFiltration_iff] at hmom
    have hlat : ∀ n : ℤ, (s : ℤ) ≤ n → n ≤ (m + s : ℕ) →
        toLattice (m + s) (u : Fin (2 * (m + s) + 1) → ℂ) n = 0 := by
      intro n hn1 hn2
      have hj : (n - s).toNat < m + 1 := by omega
      have h := hzero ⟨(n - s).toNat, hj⟩
      have hci : centeredIndex (m + s) (idx ⟨(n - s).toNat, hj⟩) = n := by
        simp only [idx, centeredIndex]
        push_cast
        omega
      rw [← toLattice_centeredIndex, hci] at h
      exact h
    have hsym : ∀ n : ℤ, toLattice (m + s) (u : Fin (2 * (m + s) + 1) → ℂ) (-n) =
        toLattice (m + s) (u : Fin (2 * (m + s) + 1) → ℂ) n := by
      intro n
      have h := congrFun (toLattice_reverseCoefficients (m + s) (u : Fin (2 * (m + s) + 1) → ℂ)) n
      rw [heven] at h
      exact h.symm
    have hsupp : LatticeSupported (s - 1) (toLattice (m + s) (u : Fin (2 * (m + s) + 1) → ℂ)) := by
      intro n hn
      rw [mem_latticeBox] at hn
      by_cases hbox : -((m + s : ℕ) : ℤ) ≤ n ∧ n ≤ (m + s : ℕ)
      · rcases le_or_gt (s : ℤ) n with h1 | h1
        · exact hlat n h1 hbox.2
        · rw [← hsym n]
          exact hlat (-n) (by omega) (by omega)
      · exact toLattice_supported _ _ n (by rw [mem_latticeBox]; exact hbox)
    have hu0 := eq_zero_of_supported_of_moments (K := m + s) (r := s - 1) (by omega) hsupp
      (fun k hk => hmom k (by omega))
    exact Subtype.ext hu0
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fin_fun] at h

/-- Dimension upper bound for the odd filtered carrier. -/
theorem finrank_oddFilteredCarrier_le (m s : ℕ) :
    finrank ℂ (oddFilteredCarrier (m + s + 1) s) ≤ m + 1 := by
  let idx : Fin (m + 1) → Fin (2 * (m + s + 1) + 1) :=
    fun j => ⟨2 * s + m + 2 + j, by omega⟩
  let Φ : oddFilteredCarrier (m + s + 1) s →ₗ[ℂ] (Fin (m + 1) → ℂ) :=
    (LinearMap.pi fun j => LinearMap.proj (idx j)) ∘ₗ (oddFilteredCarrier (m + s + 1) s).subtype
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    have hzero : ∀ j : Fin (m + 1), (u : Fin (2 * (m + s + 1) + 1) → ℂ) (idx j) = 0 := by
      intro j
      exact congrFun (LinearMap.mem_ker.mp hu) j
    obtain ⟨hodd, hmom⟩ := u.2
    rw [mem_oddCoefficientSubspace_iff] at hodd
    rw [mem_momentFiltration_iff] at hmom
    have hlat : ∀ n : ℤ, (s + 1 : ℤ) ≤ n → n ≤ (m + s + 1 : ℕ) →
        toLattice (m + s + 1) (u : Fin (2 * (m + s + 1) + 1) → ℂ) n = 0 := by
      intro n hn1 hn2
      have hj : (n - s - 1).toNat < m + 1 := by omega
      have h := hzero ⟨(n - s - 1).toNat, hj⟩
      have hci : centeredIndex (m + s + 1) (idx ⟨(n - s - 1).toNat, hj⟩) = n := by
        simp only [idx, centeredIndex]
        push_cast
        omega
      rw [← toLattice_centeredIndex, hci] at h
      exact h
    have hanti : ∀ n : ℤ, toLattice (m + s + 1) (u : Fin (2 * (m + s + 1) + 1) → ℂ) (-n) =
        -toLattice (m + s + 1) (u : Fin (2 * (m + s + 1) + 1) → ℂ) n := by
      intro n
      have h := congrFun
        (toLattice_reverseCoefficients (m + s + 1) (u : Fin (2 * (m + s + 1) + 1) → ℂ)) n
      rw [hodd] at h
      rw [← h]
      simp [toLattice]
      split_ifs <;> simp
    have hsupp : LatticeSupported s (toLattice (m + s + 1) (u : Fin (2 * (m + s + 1) + 1) → ℂ)) := by
      intro n hn
      rw [mem_latticeBox] at hn
      by_cases hbox : -((m + s + 1 : ℕ) : ℤ) ≤ n ∧ n ≤ (m + s + 1 : ℕ)
      · rcases le_or_gt ((s : ℤ) + 1) n with h1 | h1
        · exact hlat n h1 hbox.2
        · have h2 := hlat (-n) (by omega) (by omega)
          rw [hanti n] at h2
          exact neg_eq_zero.mp h2
      · exact toLattice_supported _ _ n (by rw [mem_latticeBox]; exact hbox)
    have hu0 := eq_zero_of_supported_of_moments (K := m + s + 1) (r := s) (by omega) hsupp
      (fun k hk => hmom k (by omega))
    exact Subtype.ext hu0
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fin_fun] at h

/-! ## Parameter maps for filtered carriers -/

theorem oneSubCosPow_eq_zero {m : ℕ} {q : ℤ → ℂ} (hq : LatticeSupported m q) (s : ℕ)
    (h : (oneSubCosLM ^ s) q = 0) : q = 0 := by
  induction s with
  | zero => simpa using h
  | succ s ih =>
      rw [pow_succ', LinearMap.mul_apply, oneSubCosLM_apply] at h
      exact ih (eq_zero_of_latticeOneSubCos_eq_zero (hq.oneSubCosPow s) h)

/-- Even filtered map from even-index parameters. -/
def evenFilteredEvenIndexMap (m s : ℕ) :
    (Fin (m / 2 + 1) → ℂ) →ₗ[ℂ] (Fin (2 * (m + s) + 1) → ℂ) :=
  ofLatticeLinearMap (m + s) ∘ₗ (oneSubCosLM ^ s) ∘ₗ
    { toFun := evenIndexParam, map_add' := evenIndexParam_add,
      map_smul' := evenIndexParam_smul }

/-- Even filtered map from odd-index parameters. -/
def evenFilteredOddIndexMap (m s : ℕ) :
    (Fin ((m + 1) / 2) → ℂ) →ₗ[ℂ] (Fin (2 * (m + s) + 1) → ℂ) :=
  ofLatticeLinearMap (m + s) ∘ₗ (oneSubCosLM ^ s) ∘ₗ
    { toFun := oddIndexParam, map_add' := oddIndexParam_add,
      map_smul' := oddIndexParam_smul }

/-- `i sin` as a linear endomorphism. -/
def sinLM : Module.End ℂ (ℤ → ℂ) where
  toFun := latticeSin
  map_add' := latticeSin_add
  map_smul' c f := latticeSin_smul c f

/-- Odd filtered map from even-index parameters. -/
def oddFilteredEvenIndexMap (m s : ℕ) :
    (Fin (m / 2 + 1) → ℂ) →ₗ[ℂ] (Fin (2 * (m + s + 1) + 1) → ℂ) :=
  ofLatticeLinearMap (m + s + 1) ∘ₗ sinLM ∘ₗ (oneSubCosLM ^ s) ∘ₗ
    { toFun := evenIndexParam, map_add' := evenIndexParam_add,
      map_smul' := evenIndexParam_smul }

/-- Odd filtered map from odd-index parameters. -/
def oddFilteredOddIndexMap (m s : ℕ) :
    (Fin ((m + 1) / 2) → ℂ) →ₗ[ℂ] (Fin (2 * (m + s + 1) + 1) → ℂ) :=
  ofLatticeLinearMap (m + s + 1) ∘ₗ sinLM ∘ₗ (oneSubCosLM ^ s) ∘ₗ
    { toFun := oddIndexParam, map_add' := oddIndexParam_add,
      map_smul' := oddIndexParam_smul }

theorem evenFilteredMap_apply (m s : ℕ) (q : ℤ → ℂ) :
    ofLatticeLinearMap (m + s) ((oneSubCosLM ^ s) q) = ofLattice (m + s) ((oneSubCosLM ^ s) q) :=
  rfl

/-! ## Generic sign/orthogonality of the core form -/

theorem core_pos_of_evenIndex {m M t : ℕ} {q : ℤ → ℂ} (hq : LatticeSupported m q)
    (hev : EvenIndexSupported q) (hne : q ≠ 0) (hM : m + t ≤ M) :
    0 < (latticeInner M q ((sinSqLM ^ t) (latticeSignOp q))).re := by
  rw [latticeSignOp_of_evenIndexSupported hev]
  exact latticeInner_sinSqPow_self_re_pos hq hne t hM

theorem core_neg_of_oddIndex {m M t : ℕ} {q : ℤ → ℂ} (hq : LatticeSupported m q)
    (hodd : OddIndexSupported q) (hne : q ≠ 0) (hM : m + t ≤ M) :
    (latticeInner M q ((sinSqLM ^ t) (latticeSignOp q))).re < 0 := by
  rw [latticeSignOp_of_oddIndexSupported hodd, map_neg, latticeInner_neg_right,
    Complex.neg_re, neg_lt_zero]
  exact latticeInner_sinSqPow_self_re_pos hq hne t hM

theorem core_orth_even_odd (M t : ℕ) {q₁ q₂ : ℤ → ℂ}
    (h₁ : EvenIndexSupported q₁) (h₂ : OddIndexSupported q₂) :
    latticeInner M q₁ ((sinSqLM ^ t) (latticeSignOp q₂)) = 0 :=
  latticeInner_even_odd_eq_zero M h₁ (h₂.signOp.sinSqPow t)

theorem core_orth_odd_even (M t : ℕ) {q₁ q₂ : ℤ → ℂ}
    (h₁ : OddIndexSupported q₁) (h₂ : EvenIndexSupported q₂) :
    latticeInner M q₁ ((sinSqLM ^ t) (latticeSignOp q₂)) = 0 :=
  latticeInner_odd_even_eq_zero M h₁ (h₂.signOp.sinSqPow t)

/-! ## Exact filtered inertia -/

/-- **Exact even filtered source inertia at `ω = 1/2`.**  On the level-`s`
even filtered carrier of size `K = m + s` (dimension `d = m + 1`) the source
form has an orthogonal positive/negative splitting of dimensions
`m/2 + 1 = ⌈d/2⌉` and `(m+1)/2 = ⌊d/2⌋`. -/
theorem evenFilteredCarrier_sourceHalf_split (m s : ℕ) (hs : 1 ≤ s) :
    let P := LinearMap.range (evenFilteredEvenIndexMap m s)
    let Nn := LinearMap.range (evenFilteredOddIndexMap m s)
    P ⊔ Nn = evenFilteredCarrier (m + s) s ∧
      finrank ℂ P = m / 2 + 1 ∧ finrank ℂ Nn = (m + 1) / 2 ∧
      (∀ u ∈ P, ∀ v ∈ Nn,
        sourceSesq (1 / 2) (m + s) u v = 0 ∧ sourceSesq (1 / 2) (m + s) v u = 0) ∧
      (∀ u ∈ P, u ≠ 0 → 0 < (sourceSesq (1 / 2) (m + s) u u).re) ∧
      (∀ u ∈ Nn, u ≠ 0 → (sourceSesq (1 / 2) (m + s) u u).re < 0) := by
  intro P Nn
  have hinjP : Function.Injective (evenFilteredEvenIndexMap m s) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    have hq := evenIndexParam_supported m c
    exact eq_zero_of_evenIndexParam_eq_zero (oneSubCosPow_eq_zero hq s
      (eq_zero_of_ofLattice_eq_zero (hq.oneSubCosPow s) hc))
  have hinjN : Function.Injective (evenFilteredOddIndexMap m s) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    have hq := oddIndexParam_supported m c
    exact eq_zero_of_oddIndexParam_eq_zero (oneSubCosPow_eq_zero hq s
      (eq_zero_of_ofLattice_eq_zero (hq.oneSubCosPow s) hc))
  have hPdim : finrank ℂ P = m / 2 + 1 := by
    rw [LinearMap.finrank_range_of_inj hinjP, Module.finrank_fin_fun]
  have hNdim : finrank ℂ Nn = (m + 1) / 2 := by
    rw [LinearMap.finrank_range_of_inj hinjN, Module.finrank_fin_fun]
  have horth : ∀ u ∈ P, ∀ v ∈ Nn,
      sourceSesq (1 / 2) (m + s) u v = 0 ∧ sourceSesq (1 / 2) (m + s) v u = 0 := by
    intro u hu v hv
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
    obtain ⟨c', rfl⟩ := LinearMap.mem_range.mp hv
    constructor
    · change sourceSesq (1 / 2) (m + s) (ofLattice (m + s) ((oneSubCosLM ^ s) (evenIndexParam c)))
        (ofLattice (m + s) ((oneSubCosLM ^ s) (oddIndexParam c'))) = 0
      rw [sourceSesq_half_oneSubCosPow (evenIndexParam_supported m c)]
      exact core_orth_even_odd _ _ (evenIndexParam_evenIndexSupported c)
        (oddIndexParam_oddIndexSupported c')
    · change sourceSesq (1 / 2) (m + s) (ofLattice (m + s) ((oneSubCosLM ^ s) (oddIndexParam c')))
        (ofLattice (m + s) ((oneSubCosLM ^ s) (evenIndexParam c))) = 0
      rw [sourceSesq_half_oneSubCosPow (oddIndexParam_supported m c')]
      exact core_orth_odd_even _ _ (oddIndexParam_oddIndexSupported c')
        (evenIndexParam_evenIndexSupported c)
  have hpos : ∀ u ∈ P, u ≠ 0 → 0 < (sourceSesq (1 / 2) (m + s) u u).re := by
    intro u hu hne
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
    change 0 < (sourceSesq (1 / 2) (m + s)
      (ofLattice (m + s) ((oneSubCosLM ^ s) (evenIndexParam c)))
      (ofLattice (m + s) ((oneSubCosLM ^ s) (evenIndexParam c)))).re
    have hq := evenIndexParam_supported m c
    rw [sourceSesq_half_oneSubCosPow hq]
    apply core_pos_of_evenIndex hq (evenIndexParam_evenIndexSupported c) _ le_rfl
    intro h0
    apply hne
    change ofLattice (m + s) ((oneSubCosLM ^ s) (evenIndexParam c)) = 0
    rw [h0, map_zero]
    rfl
  have hneg : ∀ u ∈ Nn, u ≠ 0 → (sourceSesq (1 / 2) (m + s) u u).re < 0 := by
    intro u hu hne
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
    change (sourceSesq (1 / 2) (m + s)
      (ofLattice (m + s) ((oneSubCosLM ^ s) (oddIndexParam c)))
      (ofLattice (m + s) ((oneSubCosLM ^ s) (oddIndexParam c)))).re < 0
    have hq := oddIndexParam_supported m c
    rw [sourceSesq_half_oneSubCosPow hq]
    apply core_neg_of_oddIndex hq (oddIndexParam_oddIndexSupported c) _ le_rfl
    intro h0
    apply hne
    change ofLattice (m + s) ((oneSubCosLM ^ s) (oddIndexParam c)) = 0
    rw [h0, map_zero]
    rfl
  have hle : P ⊔ Nn ≤ evenFilteredCarrier (m + s) s := by
    apply sup_le
    · intro u hu
      obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
      exact evenFilteredMap_mem (evenIndexParam_supported m c) (evenIndexParam_symmetric c)
    · intro u hu
      obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
      exact evenFilteredMap_mem (oddIndexParam_supported m c) (oddIndexParam_symmetric c)
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
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [hsupdim]
  exact finrank_evenFilteredCarrier_le m s hs

/-- **Exact odd filtered source inertia at `ω = 1/2`.**  On the level-`s` odd
filtered carrier of size `K = m + s + 1` (dimension `d = m + 1`) the source
form has an orthogonal positive/negative splitting of dimensions
`(m+1)/2 = ⌊d/2⌋` and `m/2 + 1 = ⌈d/2⌉`. -/
theorem oddFilteredCarrier_sourceHalf_split (m s : ℕ) :
    let P := LinearMap.range (oddFilteredOddIndexMap m s)
    let Nn := LinearMap.range (oddFilteredEvenIndexMap m s)
    P ⊔ Nn = oddFilteredCarrier (m + s + 1) s ∧
      finrank ℂ P = (m + 1) / 2 ∧ finrank ℂ Nn = m / 2 + 1 ∧
      (∀ u ∈ P, ∀ v ∈ Nn,
        sourceSesq (1 / 2) (m + s + 1) u v = 0 ∧ sourceSesq (1 / 2) (m + s + 1) v u = 0) ∧
      (∀ u ∈ P, u ≠ 0 → 0 < (sourceSesq (1 / 2) (m + s + 1) u u).re) ∧
      (∀ u ∈ Nn, u ≠ 0 → (sourceSesq (1 / 2) (m + s + 1) u u).re < 0) := by
  intro P Nn
  have hinjP : Function.Injective (oddFilteredOddIndexMap m s) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    have hq := oddIndexParam_supported m c
    have h1 := eq_zero_of_ofLattice_eq_zero (hq.oneSubCosPow s).latticeSin hc
    exact eq_zero_of_oddIndexParam_eq_zero (oneSubCosPow_eq_zero hq s
      (eq_zero_of_latticeSin_eq_zero (hq.oneSubCosPow s) h1))
  have hinjN : Function.Injective (oddFilteredEvenIndexMap m s) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    have hq := evenIndexParam_supported m c
    have h1 := eq_zero_of_ofLattice_eq_zero (hq.oneSubCosPow s).latticeSin hc
    exact eq_zero_of_evenIndexParam_eq_zero (oneSubCosPow_eq_zero hq s
      (eq_zero_of_latticeSin_eq_zero (hq.oneSubCosPow s) h1))
  have hPdim : finrank ℂ P = (m + 1) / 2 := by
    rw [LinearMap.finrank_range_of_inj hinjP, Module.finrank_fin_fun]
  have hNdim : finrank ℂ Nn = m / 2 + 1 := by
    rw [LinearMap.finrank_range_of_inj hinjN, Module.finrank_fin_fun]
  have horth : ∀ u ∈ P, ∀ v ∈ Nn,
      sourceSesq (1 / 2) (m + s + 1) u v = 0 ∧ sourceSesq (1 / 2) (m + s + 1) v u = 0 := by
    intro u hu v hv
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
    obtain ⟨c', rfl⟩ := LinearMap.mem_range.mp hv
    constructor
    · change sourceSesq (1 / 2) (m + s + 1)
        (ofLattice (m + s + 1) (latticeSin ((oneSubCosLM ^ s) (oddIndexParam c))))
        (ofLattice (m + s + 1) (latticeSin ((oneSubCosLM ^ s) (evenIndexParam c')))) = 0
      rw [sourceSesq_half_sinOneSubCosPow (oddIndexParam_supported m c),
        core_orth_odd_even _ _ (oddIndexParam_oddIndexSupported c)
          (evenIndexParam_evenIndexSupported c'), neg_zero]
    · change sourceSesq (1 / 2) (m + s + 1)
        (ofLattice (m + s + 1) (latticeSin ((oneSubCosLM ^ s) (evenIndexParam c'))))
        (ofLattice (m + s + 1) (latticeSin ((oneSubCosLM ^ s) (oddIndexParam c)))) = 0
      rw [sourceSesq_half_sinOneSubCosPow (evenIndexParam_supported m c'),
        core_orth_even_odd _ _ (evenIndexParam_evenIndexSupported c')
          (oddIndexParam_oddIndexSupported c), neg_zero]
  have hpos : ∀ u ∈ P, u ≠ 0 → 0 < (sourceSesq (1 / 2) (m + s + 1) u u).re := by
    intro u hu hne
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
    change 0 < (sourceSesq (1 / 2) (m + s + 1)
      (ofLattice (m + s + 1) (latticeSin ((oneSubCosLM ^ s) (oddIndexParam c))))
      (ofLattice (m + s + 1) (latticeSin ((oneSubCosLM ^ s) (oddIndexParam c))))).re
    have hq := oddIndexParam_supported m c
    rw [sourceSesq_half_sinOneSubCosPow hq, Complex.neg_re, neg_pos]
    apply core_neg_of_oddIndex hq (oddIndexParam_oddIndexSupported c) _ (by omega)
    intro h0
    apply hne
    change ofLattice (m + s + 1) (latticeSin ((oneSubCosLM ^ s) (oddIndexParam c))) = 0
    rw [h0, map_zero]
    funext i
    simp [ofLattice, latticeSin]
  have hneg : ∀ u ∈ Nn, u ≠ 0 → (sourceSesq (1 / 2) (m + s + 1) u u).re < 0 := by
    intro u hu hne
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
    change (sourceSesq (1 / 2) (m + s + 1)
      (ofLattice (m + s + 1) (latticeSin ((oneSubCosLM ^ s) (evenIndexParam c))))
      (ofLattice (m + s + 1) (latticeSin ((oneSubCosLM ^ s) (evenIndexParam c))))).re < 0
    have hq := evenIndexParam_supported m c
    rw [sourceSesq_half_sinOneSubCosPow hq, Complex.neg_re, neg_lt_zero]
    apply core_pos_of_evenIndex hq (evenIndexParam_evenIndexSupported c) _ (by omega)
    intro h0
    apply hne
    change ofLattice (m + s + 1) (latticeSin ((oneSubCosLM ^ s) (evenIndexParam c))) = 0
    rw [h0, map_zero]
    funext i
    simp [ofLattice, latticeSin]
  have hle : P ⊔ Nn ≤ oddFilteredCarrier (m + s + 1) s := by
    apply sup_le
    · intro u hu
      obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
      exact oddFilteredMap_mem (oddIndexParam_supported m c) (oddIndexParam_symmetric c)
    · intro u hu
      obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hu
      exact oddFilteredMap_mem (evenIndexParam_supported m c) (evenIndexParam_symmetric c)
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
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [hsupdim]
  exact finrank_oddFilteredCarrier_le m s

/-- Every filtered carrier of dimension `≥ 2` is indefinite at `ω = 1/2`. -/
theorem filteredCarriers_sourceHalf_indefinite (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) :
    (∃ u ∈ evenFilteredCarrier (m + s) s, 0 < (sourceSesq (1 / 2) (m + s) u u).re) ∧
    (∃ u ∈ evenFilteredCarrier (m + s) s, (sourceSesq (1 / 2) (m + s) u u).re < 0) ∧
    (∃ u ∈ oddFilteredCarrier (m + s + 1) s,
      0 < (sourceSesq (1 / 2) (m + s + 1) u u).re) ∧
    (∃ u ∈ oddFilteredCarrier (m + s + 1) s,
      (sourceSesq (1 / 2) (m + s + 1) u u).re < 0) := by
  have hex : ∀ {K : ℕ} (W : Submodule ℂ (Fin (2 * K + 1) → ℂ)), 0 < finrank ℂ W →
      ∃ w ∈ W, w ≠ 0 := by
    intro K W hW
    obtain ⟨w, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Submodule.one_le_finrank_iff.mp hW)
    exact ⟨w, hw.1, hw.2⟩
  obtain ⟨hsupe, hPe, hNe, -, hpose, hnege⟩ := evenFilteredCarrier_sourceHalf_split m s hs
  obtain ⟨hsupo, hPo, hNo, -, hposo, hnego⟩ := oddFilteredCarrier_sourceHalf_split m s
  obtain ⟨a, ha, ha0⟩ := hex _ (by rw [hPe]; omega)
  obtain ⟨b, hb, hb0⟩ := hex _ (by rw [hNe]; omega)
  obtain ⟨c, hc, hc0⟩ := hex _ (by rw [hPo]; omega)
  obtain ⟨d, hd, hd0⟩ := hex _ (by rw [hNo]; omega)
  exact ⟨⟨a, hsupe ▸ Submodule.mem_sup_left ha, hpose a ha ha0⟩,
    ⟨b, hsupe ▸ Submodule.mem_sup_right hb, hnege b hb hb0⟩,
    ⟨c, hsupo ▸ Submodule.mem_sup_left hc, hposo c hc hc0⟩,
    ⟨d, hsupo ▸ Submodule.mem_sup_right hd, hnego d hd hd0⟩⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.latticeInner_sinSqPow_self_re_pos
#print axioms Zeta23.CCM.sourceSesq_half_oneSubCosPow
#print axioms Zeta23.CCM.sourceSesq_half_sinOneSubCosPow
#print axioms Zeta23.CCM.latticePair_monomial_oneSubCosPow
#print axioms Zeta23.CCM.latticePair_monomial_sinOneSubCosPow
#print axioms Zeta23.CCM.finrank_evenFilteredCarrier_le
#print axioms Zeta23.CCM.finrank_oddFilteredCarrier_le
#print axioms Zeta23.CCM.evenFilteredCarrier_sourceHalf_split
#print axioms Zeta23.CCM.oddFilteredCarrier_sourceHalf_split
#print axioms Zeta23.CCM.filteredCarriers_sourceHalf_indefinite
