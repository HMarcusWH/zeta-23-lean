import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

noncomputable section

namespace Zeta23.OPICARound4
open scoped BigOperators

/-- Finite signed response. The list may repeat eigenvalues; no simplicity or
positive-residue assumption is built into this definition. -/
def signedSpectralResponse {ι : Type*} [Fintype ι]
    (eigenvalue residue : ι → ℝ) (lam : ℝ) : ℝ :=
  ∑ i, residue i / (eigenvalue i - lam)

/-- Exact derivative on the resolvent set. Signed residues give no automatic
monotonicity; every eigenvalue avoidance premise remains explicit. -/
theorem signed_response_hasDerivAt {ι : Type*} [Fintype ι]
    (eigenvalue residue : ι → ℝ) (lam : ℝ)
    (haway : ∀ i, eigenvalue i - lam ≠ 0) :
    HasDerivAt (signedSpectralResponse eigenvalue residue)
      (∑ i, residue i / (eigenvalue i - lam) ^ 2) lam := by
  have hi (i : ι) : HasDerivAt
      (fun x : ℝ => residue i / (eigenvalue i - x))
      (residue i / (eigenvalue i - lam) ^ 2) lam := by
    have hd : HasDerivAt (fun x : ℝ => eigenvalue i - x) (-1) lam := by
      simpa using! (hasDerivAt_const lam (eigenvalue i)).sub (hasDerivAt_id lam)
    convert! (hasDerivAt_const lam (residue i)).div hd (haway i) using 1 <;> ring
  unfold signedSpectralResponse
  apply HasDerivAt.fun_sum
  intro i _
  exact hi i

/-- A nonnegative resolvent kernel below its bottom is a contraction after
multiplication by the gap. This is an exact scalar spectral calculation. -/
theorem resolvent_kernel_unit_interval {mu b lam : ℝ}
    (hmu : b ≤ mu) (hlam : lam < b) :
    0 ≤ (b - lam) / (mu - lam) ∧ (b - lam) / (mu - lam) ≤ 1 := by
  have hd : 0 < mu - lam := by linarith
  exact ⟨div_nonneg (by linarith) hd.le, (div_le_one hd).mpr (by linarith)⟩

/-- Positive-mass control expressed through the signed mass and total variation.
Negative residues are retained on the left, rather than replaced there by norms. -/
theorem signed_kernel_upper {ι : Type*} [Fintype ι]
    (residue kernel : ι → ℝ)
    (hlo : ∀ i, 0 ≤ kernel i) (hhi : ∀ i, kernel i ≤ 1) :
    ∑ i, kernel i * residue i ≤
      ((∑ i, |residue i|) + ∑ i, residue i) / 2 := by
  have hpoint : ∀ i, 2 * (kernel i * residue i) ≤ |residue i| + residue i := by
    intro i
    rcases le_total 0 (residue i) with hp | hn
    · rw [abs_of_nonneg hp]
      nlinarith [mul_le_mul_of_nonneg_right (hhi i) hp]
    · rw [abs_of_nonpos hn]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (hlo i) hn]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  linarith

/-- S05 finite spectral support with the exact opposite-spectrum domain. It is
a one-sided signed estimate and does not supply any arithmetic smallness. -/
theorem signed_resolvent_upper {ι : Type*} [Fintype ι]
    (eigenvalue residue : ι → ℝ) (b lam : ℝ)
    (hbottom : ∀ i, b ≤ eigenvalue i) (hlam : lam < b) :
    (b - lam) * signedSpectralResponse eigenvalue residue lam ≤
      ((∑ i, |residue i|) + ∑ i, residue i) / 2 := by
  have h := signed_kernel_upper residue
    (fun i => (b - lam) / (eigenvalue i - lam))
    (fun i => (resolvent_kernel_unit_interval (hbottom i) hlam).1)
    (fun i => (resolvent_kernel_unit_interval (hbottom i) hlam).2)
  convert h using 1
  simp only [signedSpectralResponse, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- An explicit margin comparison consumer. Its budget premise remains visible;
no native source packet installs this as an automatic terminal bound. -/
theorem signed_response_lt_one_of_budget {ι : Type*} [Fintype ι]
    (eigenvalue residue : ι → ℝ) (b lam : ℝ)
    (hbottom : ∀ i, b ≤ eigenvalue i) (hlam : lam < b)
    (hbudget : ((∑ i, |residue i|) + ∑ i, residue i) / 2 < b - lam) :
    signedSpectralResponse eigenvalue residue lam < 1 := by
  have hs := signed_resolvent_upper eigenvalue residue b lam hbottom hlam
  have hmul : (b - lam) * signedSpectralResponse eigenvalue residue lam <
      (b - lam) * 1 := by nlinarith
  nlinarith [sub_pos.mpr hlam]

/-- A signed prefix is the cumulative mass through index n-1. -/
def signedPrefix (residue : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, residue i

/-- Discrete Abel identity with its final endpoint term. -/
theorem signed_prefix_abel (residue kernel : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, residue i * kernel i) =
      signedPrefix residue n * kernel n +
      ∑ i ∈ Finset.range n,
        signedPrefix residue (i + 1) * (kernel i - kernel (i + 1)) := by
  induction n with
  | zero => simp [signedPrefix]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have hp : signedPrefix residue (n + 1) = signedPrefix residue n + residue n := by
      simp only [signedPrefix, Finset.sum_range_succ]
    rw [hp]
    ring

/-- Nonnegative prefixes and a nonnegative decreasing kernel give a nonnegative
pairing. Ordering and every endpoint hypothesis are explicit. -/
theorem signed_prefix_nonnegative (residue kernel : ℕ → ℝ) (n : ℕ)
    (hp : ∀ j, j ≤ n → 0 ≤ signedPrefix residue j)
    (hk : 0 ≤ kernel n)
    (hdec : ∀ i, i < n → kernel (i + 1) ≤ kernel i) :
    0 ≤ ∑ i ∈ Finset.range n, residue i * kernel i := by
  rw [signed_prefix_abel]
  apply add_nonneg (mul_nonneg (hp n le_rfl) hk)
  apply Finset.sum_nonneg
  intro i hi
  have hi' := Finset.mem_range.mp hi
  exact mul_nonneg (hp (i + 1) (by omega)) (sub_nonneg.mpr (hdec i hi'))

end Zeta23.OPICARound4
