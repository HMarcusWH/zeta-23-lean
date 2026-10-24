import Zeta23.OPICAFollowup.CoPoissonJets
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin

/- Candidate ConfluentProfiles module. Original roots retain their complete grouped contracts.
The only direct project import is frozen CoPoissonJets. Compilation and physical expected consumers
must pass before any original-root authority is recorded. RH and Step 4 remain OPEN. -/
set_option maxHeartbeats 800000

/- Verified source fragment: ConfluentAlgebra.lean ; sha256=89182b42729b89bbb7762b8f61626f8d6879f21a36a17afea5936cc350278d04 -/
section

/-! Mathlib-only algebra for the full OPICA H2a determinant route.
This file is scratch support and confers no primary-root authority. -/

noncomputable section
open Polynomial Finset
open scoped BigOperators

namespace Zeta23.OPICAFollowup.OPICAConfluentAudit

variable {K : Type*} [CommRing K] {M : ℕ}

def functionalMatrix (L : Fin M → K[X] →ₗ[K] K) (p : Fin M → K[X]) :
    Matrix (Fin M) (Fin M) K := fun i j => L j (p i)

theorem functionalMatrix_eq_coeff_mul (L : Fin M → K[X] →ₗ[K] K)
    (p : Fin M → K[X]) (hdeg : ∀ i, (p i).natDegree < M) :
    functionalMatrix L p =
      (Matrix.of (fun i j : Fin M => (p j).coeff i)).transpose *
        functionalMatrix L (fun i => X ^ (i : ℕ)) := by
  ext i j
  change L j (p i) = ∑ k : Fin M, (p i).coeff k * L j (X ^ (k : ℕ))
  conv_lhs => rw [(p i).as_sum_range_C_mul_X_pow' (hdeg i)]
  rw [map_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.C_mul', map_smul]
  rfl

theorem det_functionalMatrix_monic_basis (L : Fin M → K[X] →ₗ[K] K)
    (p : Fin M → K[X]) (hdeg : ∀ i, (p i).natDegree = (i : ℕ))
    (hmonic : ∀ i, (p i).Monic) :
    (functionalMatrix L p).det =
      (functionalMatrix L (fun i => X ^ (i : ℕ))).det := by
  rw [functionalMatrix_eq_coeff_mul L p (fun i => by rw [hdeg]; exact i.isLt),
    Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_matrixOfPolynomials p hdeg hmonic, one_mul]

def hasseFunctional (κ : K) (k : ℕ) : K[X] →ₗ[K] K :=
  (Polynomial.leval κ).comp (Polynomial.hasseDeriv k)

theorem hasseFunctional_eq_taylor_coeff (κ : K) (k : ℕ) (p : K[X]) :
    hasseFunctional κ k p = (Polynomial.taylor κ p).coeff k := by
  exact (Polynomial.taylor_coeff κ p k).symm

/-- Monic Newton polynomials in an arbitrary ordered node sequence. Repeated
nodes are intentional: their number before a column is its normalized jet order. -/
def newtonPolynomial (node : Fin M → K) (i : Fin M) : K[X] :=
  ∏ j ∈ Finset.Iio i, (X - C (node j))

theorem newtonPolynomial_monic (node : Fin M → K) (i : Fin M) :
    (newtonPolynomial node i).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro j hj
  exact Polynomial.monic_X_sub_C _

theorem newtonPolynomial_natDegree [Nontrivial K] (node : Fin M → K) (i : Fin M) :
    (newtonPolynomial node i).natDegree = (i : ℕ) := by
  rw [newtonPolynomial, Polynomial.natDegree_prod_of_monic]
  · simp
  · intro j hj
    exact Polynomial.monic_X_sub_C _


end Zeta23.OPICAFollowup.OPICAConfluentAudit
end
end

/- Verified source fragment: NewtonHermite.lean ; sha256=3bf01d19e2496d0e52291afe75f88f620c465af63aeed09dc785fd90d88a996d -/
section

noncomputable section
open Polynomial Finset
open scoped BigOperators

namespace Zeta23.OPICAFollowup.OPICAConfluentAudit
variable {K : Type*} [CommRing K] {M : ℕ}

def priorMatches (node : Fin M → K) (κ : K) (i : Fin M) : Finset (Fin M) := by
  classical
  exact (Finset.Iio i).filter (fun j => node j = κ)

def priorNonmatches (node : Fin M → K) (κ : K) (i : Fin M) : Finset (Fin M) := by
  classical
  exact (Finset.Iio i).filter (fun j => node j ≠ κ)

def repeatedJetOrder (node : Fin M → K) (i : Fin M) : ℕ :=
  (priorMatches node (node i) i).card

theorem taylor_newtonPolynomial (node : Fin M → K) (κ : K) (i : Fin M) :
    Polynomial.taylor κ (newtonPolynomial node i) =
      X ^ (priorMatches node κ i).card *
        ∏ j ∈ priorNonmatches node κ i, (X + C (κ - node j)) := by
  classical
  rw [newtonPolynomial, Polynomial.taylor_apply, Polynomial.prod_comp]
  have hterm (j : Fin M) :
      (X - C (node j)).comp (X + C κ) = (X + C (κ - node j) : K[X]) := by
    simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, map_sub]
    ring
  simp_rw [hterm]
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Iio i)
    (fun j => node j = κ) (fun j => (X + C (κ - node j) : K[X]))]
  have hmatch : (∏ j ∈ priorMatches node κ i, (X + C (κ - node j) : K[X])) =
      X ^ (priorMatches node κ i).card := by
    calc
      _ = ∏ j ∈ priorMatches node κ i, (X : K[X]) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hjκ : node j = κ := (Finset.mem_filter.mp hj).2
        simp [hjκ]
      _ = _ := Finset.prod_const _
  exact congrArg (fun p : K[X] => p *
    ∏ j ∈ priorNonmatches node κ i, (X + C (κ - node j))) hmatch

theorem priorMatches_strict (node : Fin M → K) {i j : Fin M} (hji : j < i) :
    repeatedJetOrder node j < (priorMatches node (node j) i).card := by
  classical
  have hjnot : j ∉ priorMatches node (node j) j := by simp [priorMatches]
  have hsub : insert j (priorMatches node (node j) j) ⊆ priorMatches node (node j) i := by
    intro l hl
    rcases Finset.mem_insert.mp hl with hl | hl
    · subst l
      simp [priorMatches, hji]
    · have hl' := Finset.mem_filter.mp hl
      simp only [priorMatches, Finset.mem_filter, Finset.mem_Iio] at hl' ⊢
      exact ⟨lt_trans hl'.1 hji, hl'.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hjnot] at hcard
  exact Nat.lt_of_succ_le hcard

theorem hasseFunctional_newton_below (node : Fin M → K) {i j : Fin M} (hji : j < i) :
    hasseFunctional (node j) (repeatedJetOrder node j) (newtonPolynomial node i) = 0 := by
  rw [hasseFunctional_eq_taylor_coeff, taylor_newtonPolynomial,
    Polynomial.coeff_X_pow_mul', if_neg (not_le.mpr (priorMatches_strict node hji))]

theorem hasseFunctional_newton_diagonal (node : Fin M → K) (i : Fin M) :
    hasseFunctional (node i) (repeatedJetOrder node i) (newtonPolynomial node i) =
      ∏ j ∈ priorNonmatches node (node i) i, (node i - node j) := by
  rw [hasseFunctional_eq_taylor_coeff, taylor_newtonPolynomial]
  rw [repeatedJetOrder, Polynomial.coeff_X_pow_mul']
  simp [Polynomial.coeff_zero_prod]

theorem normalizedHermite_determinant [Nontrivial K] (node : Fin M → K) :
    (functionalMatrix (fun j => hasseFunctional (node j) (repeatedJetOrder node j))
      (fun i => X ^ (i : ℕ))).det =
      ∏ i : Fin M, ∏ j ∈ priorNonmatches node (node i) i, (node i - node j) := by
  rw [← det_functionalMatrix_monic_basis _ (newtonPolynomial node)
    (newtonPolynomial_natDegree node) (newtonPolynomial_monic node)]
  have hu : (functionalMatrix (fun j => hasseFunctional (node j) (repeatedJetOrder node j))
      (newtonPolynomial node)).IsUpperTriangular := by
    intro i j hji
    exact hasseFunctional_newton_below node hji
  rw [Matrix.det_of_isUpperTriangular hu]
  apply Finset.prod_congr rfl
  intro i hi
  exact hasseFunctional_newton_diagonal node i

end Zeta23.OPICAFollowup.OPICAConfluentAudit
end
end

/- Verified source fragment: CoordinateConfluent.lean ; sha256=e08fb1cc080e175ee0a1c2a3928bb107420f03d4419b200253b1a4f662e1500c -/
section

noncomputable section
open Polynomial Finset
open scoped BigOperators

namespace Zeta23.OPICAFollowup.OPICAConfluentAudit
variable {K : Type*} [CommRing K] {M : ℕ}

theorem priorMatches_cons_zero (node : Fin M → K) {κ : K} (hκ : κ ≠ 0) (i : Fin M) :
    priorMatches (Fin.cons 0 node) κ i.succ =
      (priorMatches node κ i).map (Fin.succEmb M) := by
  classical
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [priorMatches, hκ, Ne.symm hκ]
  · simp [priorMatches]

theorem priorNonmatches_cons_zero (node : Fin M → K) {κ : K} (hκ : κ ≠ 0) (i : Fin M) :
    priorNonmatches (Fin.cons 0 node) κ i.succ =
      insert 0 ((priorNonmatches node κ i).map (Fin.succEmb M)) := by
  classical
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [priorNonmatches, hκ, Ne.symm hκ]
  · simp [priorNonmatches]

theorem repeatedJetOrder_cons_zero (node : Fin M → K) (hnode : ∀ i, node i ≠ 0) (i : Fin M) :
    repeatedJetOrder (Fin.cons 0 node) i.succ = repeatedJetOrder node i := by
  unfold repeatedJetOrder
  rw [Fin.cons_succ, priorMatches_cons_zero node (hnode i), Finset.card_map]

theorem coordinateHermite_determinant [Nontrivial K] (node : Fin M → K)
    (hnode : ∀ i, node i ≠ 0) :
    (functionalMatrix (fun j => hasseFunctional (node j) (repeatedJetOrder node j))
      (fun i => X ^ ((i : ℕ) + 1))).det =
      (∏ i : Fin M, node i) *
        ∏ i : Fin M, ∏ j ∈ priorNonmatches node (node i) i, (node i - node j) := by
  classical
  let extnode : Fin (M + 1) → K := Fin.cons 0 node
  let A : Matrix (Fin (M + 1)) (Fin (M + 1)) K :=
    functionalMatrix (fun j => hasseFunctional (extnode j) (repeatedJetOrder extnode j))
      (fun i => X ^ (i : ℕ))
  have horder : repeatedJetOrder extnode 0 = 0 := by simp [extnode, repeatedJetOrder, priorMatches]
  have hA00 : A 0 0 = 1 := by simp [A, functionalMatrix, horder, hasseFunctional, extnode]
  have hAcol (i : Fin M) : A i.succ 0 = 0 := by
    simp [A, functionalMatrix, horder, hasseFunctional, extnode]
  have hminor : A.submatrix Fin.succ Fin.succ =
      functionalMatrix (fun j => hasseFunctional (node j) (repeatedJetOrder node j))
        (fun i => X ^ ((i : ℕ) + 1)) := by
    ext i j
    change hasseFunctional (extnode j.succ) (repeatedJetOrder extnode j.succ)
      (X ^ (i.succ : ℕ)) = _
    rw [show extnode j.succ = node j from Fin.cons_succ _ _ _,
      show repeatedJetOrder extnode j.succ = repeatedJetOrder node j from
        repeatedJetOrder_cons_zero node hnode j]
    rfl
  have hexpand : A.det =
      (functionalMatrix (fun j => hasseFunctional (node j) (repeatedJetOrder node j))
        (fun i => X ^ ((i : ℕ) + 1))).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, hA00, one_mul, Fin.succAbove_zero, hminor,
      hAcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rw [← hexpand]
  change (functionalMatrix (fun j => hasseFunctional (extnode j) (repeatedJetOrder extnode j))
    (fun i => X ^ (i : ℕ))).det = _
  rw [normalizedHermite_determinant, Fin.prod_univ_succ]
  have hzero : (∏ j ∈ priorNonmatches extnode (extnode 0) 0,
      (extnode 0 - extnode j)) = 1 := by
    have hempty : Finset.Iio (0 : Fin (M + 1)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hj' : j < (0 : Fin (M + 1)) := Finset.mem_Iio.mp hj
      exact Nat.not_lt_zero j.val hj'
    simp [priorNonmatches, hempty]
  rw [hzero, one_mul]
  have hterm (i : Fin M) :
      (∏ j ∈ priorNonmatches extnode (extnode i.succ) i.succ,
        (extnode i.succ - extnode j)) =
      node i * ∏ j ∈ priorNonmatches node (node i) i, (node i - node j) := by
    rw [show extnode i.succ = node i from Fin.cons_succ _ _ _,
      show priorNonmatches extnode (node i) i.succ =
        insert 0 ((priorNonmatches node (node i) i).map (Fin.succEmb M)) from
          priorNonmatches_cons_zero node (hnode i) i,
      Finset.prod_insert (by simp)]
    simp [extnode, Finset.prod_map]
  simp_rw [hterm]
  exact Finset.prod_mul_distrib

end Zeta23.OPICAFollowup.OPICAConfluentAudit
end
end

/- Verified source fragment: AffineConfluent.lean ; sha256=8213e875d8faae9fda4a41d8910bb64c4973711d82373f179844abbe075e6183 -/
section

noncomputable section
set_option maxHeartbeats 800000
open Polynomial Finset
open scoped BigOperators

namespace Zeta23.OPICAFollowup.OPICAConfluentAudit
variable {K : Type*} [CommRing K] {M : ℕ}

theorem affineNegPower (a : K) (n : ℕ) :
    (C a - X : K[X]) ^ n = (-1 : K) ^ n • (X - C a) ^ n := by
  have he : (C a - X : K[X]) = C (-1) * (X - C a) := by
    simp only [map_neg, map_one]
    ring
  rw [he, mul_pow, ← map_pow, Polynomial.C_mul']

theorem det_functionalMatrix_affine (L : Fin M → K[X] →ₗ[K] K) (a : K)
    [Nontrivial K] :
    (functionalMatrix L (fun i => (C a - X) ^ (i : ℕ))).det =
      (-1 : K) ^ (M * (M - 1) / 2) *
        (functionalMatrix L (fun i => X ^ (i : ℕ))).det := by
  have hmat : functionalMatrix L (fun i => (C a - X) ^ (i : ℕ)) =
      Matrix.of (fun i j : Fin M => (-1 : K) ^ (i : ℕ) *
        functionalMatrix L (fun i => (X - C a) ^ (i : ℕ)) i j) := by
    ext i j
    change L j ((C a - X) ^ (i : ℕ)) = _
    rw [affineNegPower, map_smul]
    rfl
  rw [hmat, Matrix.det_mul_column]
  have hpdeg (i : Fin M) : ((X - C a : K[X]) ^ (i : ℕ)).natDegree = (i : ℕ) := by
    rw [(Polynomial.monic_X_sub_C a).natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  rw [det_functionalMatrix_monic_basis L (fun i => (X - C a) ^ (i : ℕ)) hpdeg
    (fun i => (Polynomial.monic_X_sub_C a).pow _),
    Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun n : ℕ => n) M, Finset.sum_range_id]

theorem profilePolynomial_confluent_expanded_determinant [Nontrivial K]
    (node : Fin M → K) (hnode : ∀ i, node i ≠ 0) (a : K) :
    (functionalMatrix (fun j => hasseFunctional (node j) (repeatedJetOrder node j))
      (fun i => X * (C a - X) ^ (i : ℕ))).det =
      (-1 : K) ^ (M * (M - 1) / 2) *
        (∏ i : Fin M, node i) *
          ∏ i : Fin M, ∏ j ∈ priorNonmatches node (node i) i, (node i - node j) := by
  let L : Fin M → K[X] →ₗ[K] K := fun j =>
    (hasseFunctional (node j) (repeatedJetOrder node j)).comp
      (LinearMap.mulLeft K (X : K[X]))
  have hsource : functionalMatrix L (fun i => (C a - X) ^ (i : ℕ)) =
      functionalMatrix (fun j => hasseFunctional (node j) (repeatedJetOrder node j))
        (fun i => X * (C a - X) ^ (i : ℕ)) := rfl
  have hmonomial : functionalMatrix L (fun i => X ^ (i : ℕ)) =
      functionalMatrix (fun j => hasseFunctional (node j) (repeatedJetOrder node j))
        (fun i => X ^ ((i : ℕ) + 1)) := by
    ext i j
    change hasseFunctional (node j) (repeatedJetOrder node j) (X * X ^ (i : ℕ)) = _
    rw [← pow_succ']
    rfl
  rw [← hsource, det_functionalMatrix_affine, hmonomial,
    coordinateHermite_determinant node hnode]
  rw [mul_assoc]

end Zeta23.OPICAFollowup.OPICAConfluentAudit
end
end

/- Verified source fragment: HasseNormalizedDerivative.lean ; sha256=ce7f03101b0aee68cd0457e1dcca832c5ec90cc61b26f228389fc8b2eaa261d9 -/
section

noncomputable section
open Polynomial
namespace Zeta23.OPICAFollowup.OPICAConfluentAudit

variable {K : Type*} [NontriviallyNormedField K]

theorem iteratedDeriv_polynomial_eval (p : K[X]) (n : ℕ) :
    iteratedDeriv n (fun z => p.eval z) =
      (fun z => (Polynomial.derivative^[n] p).eval z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    rw [Polynomial.deriv, Function.iterate_succ_apply']

theorem hasse_eq_normalized_iteratedDeriv [CharZero K] (p : K[X]) (n : ℕ) (z : K) :
    (Polynomial.hasseDeriv n p).eval z =
      iteratedDeriv n (fun w => p.eval w) z / (n.factorial : K) := by
  have hf := congrFun (Polynomial.factorial_smul_hasseDeriv n) p
  have he := congrArg (fun q : K[X] => q.eval z) hf
  change (Polynomial.evalRingHom z) (n.factorial • Polynomial.hasseDeriv n p) =
    (Polynomial.derivative^[n] p).eval z at he
  rw [map_nsmul, nsmul_eq_mul] at he
  have he' : (n.factorial : K) * (Polynomial.hasseDeriv n p).eval z =
      iteratedDeriv n (fun w => p.eval w) z := by
    rw [iteratedDeriv_polynomial_eval]
    exact he
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero n : (n.factorial : K) ≠ 0)).mpr
  simpa only [mul_comm] using he'

end Zeta23.OPICAFollowup.OPICAConfluentAudit
end
end

/- Verified source fragment: ActualFirstCell.lean ; sha256=eb9c6db2542fbe6ad73b539c618aa8ebfb141fe4c39b14fe71c5a677822ab44e -/
section

/-! Actual physical first-cell bridge for H2a. This identifies the existing
zeroJetDensity with the κ-jets of the entire first-cell kernel. The odd-u
Taylor coefficient extraction and measure-independence bridge remain separate. -/

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology
namespace Zeta23.OPICAFollowup.OPICAActualFirstCellAudit
open Zeta23.OPICAFollowup

theorem actual_family_first_cell (κ : ℂ) {y : ℝ} (hy1 : 1 ≤ y) (hy2 : y < 2) :
    zeroFamilyDensity κ y =
      κ * (Real.exp (-Real.log y / 2) : ℂ) * shKernel (1 / 4 - κ) (Real.log y) := by
  have hy0 : 0 ≤ y := by linarith
  have hfloor : ⌊|y|⌋₊ = 1 := by
    apply (Nat.floor_eq_iff (abs_nonneg y)).mpr
    rw [abs_of_nonneg hy0]
    norm_num
    exact ⟨hy1, hy2⟩
  rw [zeroFamilyDensity, hfloor, abs_of_nonneg hy0]
  simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, div_one]
  ring

theorem actual_family_first_log_cell (κ : ℂ) {u : ℝ} (hu0 : 0 ≤ u)
    (hu2 : u < Real.log 2) :
    (Real.exp (u / 2) : ℂ) * zeroFamilyDensity κ (Real.exp u) =
      κ * shKernel (1 / 4 - κ) u := by
  have hy1 : 1 ≤ Real.exp u := Real.one_le_exp hu0
  have hy2 : Real.exp u < 2 := by
    calc
      Real.exp u < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hu2
      _ = 2 := Real.exp_log (by norm_num)
  rw [actual_family_first_cell κ hy1 hy2, Real.log_exp]
  have he : (Real.exp (u / 2) : ℂ) * (Real.exp (-u / 2) : ℂ) = 1 := by
    have hr : Real.exp (u / 2) * Real.exp (-u / 2) = 1 := by
      rw [← Real.exp_add, show u / 2 + -u / 2 = 0 by ring, Real.exp_zero]
    exact_mod_cast hr
  calc
    _ = κ * ((Real.exp (u / 2) : ℂ) * (Real.exp (-u / 2) : ℂ)) *
        shKernel (1 / 4 - κ) u := by ring
    _ = _ := by rw [he]; ring

theorem actual_normalized_jet_first_log_cell (κ : ℂ) (k : ℕ) {u : ℝ} (hu0 : 0 ≤ u)
    (hu2 : u < Real.log 2) :
    (Real.exp (u / 2) : ℂ) * zeroJetDensity κ k (Real.exp u) =
      iteratedDeriv k (fun w : ℂ => w * shKernel (1 / 4 - w) u) κ /
        (k.factorial : ℂ) := by
  have heq : (fun w : ℂ => (Real.exp (u / 2) : ℂ) * zeroFamilyDensity w (Real.exp u)) =
      (fun w : ℂ => w * shKernel (1 / 4 - w) u) :=
    funext (fun w => actual_family_first_log_cell w hu0 hu2)
  have hk := congrArg (fun f : ℂ → ℂ => iteratedDeriv k f κ) heq
  rw [iteratedDeriv_const_mul_field] at hk
  rw [zeroJetDensity, ← mul_div_assoc, hk]

end Zeta23.OPICAFollowup.OPICAActualFirstCellAudit
end
end

/- Verified source fragment: ShFiniteTaylor.lean ; sha256=59f266e1dc8043bb502665133b6b1b7db4e4832482b169cfb380c59ff7f6f525 -/
section

/-! Finite right-cell Taylor remainders, prior to any κ differentiation.
These are statements about the explicit entire kernel, not derivatives of
the global physical density at the first lattice boundary. -/

noncomputable section
set_option maxHeartbeats 800000
open Set Filter Complex
open scoped Topology
namespace Zeta23.OPICAFollowup.OPICARightCellTaylor
open Zeta23.OPICAFollowup

def expMajorant (B : ℝ) : ℝ := ∑' m : ℕ, B ^ m / (m.factorial : ℝ)

theorem expMajorant_nonneg {B : ℝ} (hB : 0 ≤ B) : 0 ≤ expMajorant B :=
  tsum_nonneg (fun m => div_nonneg (pow_nonneg hB _) (Nat.cast_nonneg _))

def shPartial (w : ℂ) (u : ℝ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    w ^ j * (u : ℂ) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℂ)

theorem shKernel_sub_partial (w : ℂ) (u : ℝ) (n : ℕ) :
    shKernel w u - shPartial w u n =
      ∑' m : ℕ, w ^ (m + (n + 1)) * (u : ℂ) ^ (2 * (m + (n + 1)) + 1) /
        ((2 * (m + (n + 1)) + 1).factorial : ℂ) := by
  have h := (summable_shKernel w u).sum_add_tsum_nat_add (n + 1)
  exact (eq_sub_iff_add_eq.mpr (by simpa [shKernel, shPartial, add_comm] using h)).symm

theorem shKernel_sub_partial_norm {B : ℝ} (hB : 0 ≤ B) {w : ℂ} (hw : ‖w‖ ≤ B)
    {u : ℝ} (hu : |u| ≤ 1) (n : ℕ) :
    ‖shKernel w u - shPartial w u n‖ ≤
      B ^ (n + 1) * |u| ^ (2 * n + 3) * expMajorant B := by
  rw [shKernel_sub_partial]
  have hs := (Real.summable_pow_div_factorial B).hasSum.mul_left
    (B ^ (n + 1) * |u| ^ (2 * n + 3))
  apply tsum_of_norm_bounded hs
  intro m
  rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_natCast]
  have hp : |u| ^ (2 * m) ≤ 1 := pow_le_one₀ (abs_nonneg _) hu
  have hf : (m.factorial : ℝ) ≤ ((2 * (m + (n + 1)) + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : m ≤ 2 * (m + (n + 1)) + 1)
  have hn : 2 * (m + (n + 1)) + 1 = 2 * m + (2 * n + 3) := by omega
  have hwp : ‖w‖ ^ (m + (n + 1)) = ‖w‖ ^ m * ‖w‖ ^ (n + 1) := pow_add _ _ _
  have hup : |u| ^ (2 * (m + (n + 1)) + 1) = |u| ^ (2 * m) * |u| ^ (2 * n + 3) := by
    rw [hn, pow_add]
  rw [hwp, hup]
  calc
    ‖w‖ ^ m * ‖w‖ ^ (n + 1) * (|u| ^ (2 * m) * |u| ^ (2 * n + 3)) /
        ((2 * (m + (n + 1)) + 1).factorial : ℝ)
      ≤ B ^ m * B ^ (n + 1) * (1 * |u| ^ (2 * n + 3)) / (m.factorial : ℝ) := by
        gcongr
    _ = _ := by ring

end Zeta23.OPICAFollowup.OPICARightCellTaylor
end
end

/- Verified source fragment: ActualJetTaylor.lean ; sha256=d7f58cfc9cfd1486a95a15996aa72d7e284b6e0c61f45487fa00014329993df7 -/
section

/-! Uniform finite Taylor remainders for the actual normalized parameter jets.
The real variable is restricted to the explicit analytic right-cell continuation.
No derivative of the global physical density at the lattice boundary is used. -/

noncomputable section
set_option maxHeartbeats 800000
open Set Filter Complex
open scoped Topology
namespace Zeta23.OPICAFollowup.OPICARightCellTaylor
open Zeta23.OPICAFollowup

def firstPartial (κ : ℂ) (u : ℝ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    (κ * (1 / 4 - κ) ^ j) * (u : ℂ) ^ (2 * j + 1) /
      ((2 * j + 1).factorial : ℂ)

theorem firstPartial_eq (κ : ℂ) (u : ℝ) (n : ℕ) :
    firstPartial κ u n = κ * shPartial (1 / 4 - κ) u n := by
  unfold firstPartial shPartial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem differentiable_firstPartial (u : ℝ) (n : ℕ) :
    Differentiable ℂ (fun κ => firstPartial κ u n) := by
  unfold firstPartial
  exact Differentiable.fun_sum (fun j _ =>
    ((differentiable_id.mul (((differentiable_const (1 / 4 : ℂ)).sub
      differentiable_id).pow j)).mul_const _).div_const _)

theorem differentiable_firstKernel (u : ℝ) :
    Differentiable ℂ (fun κ : ℂ => κ * shKernel (1 / 4 - κ) u) :=
  differentiable_id.mul ((differentiable_shKernel u).comp
    ((differentiable_const _).sub differentiable_id))

theorem firstKernel_sub_partial_norm (κ₀ : ℂ) {w : ℂ}
    (hw : ‖w‖ ≤ ‖κ₀‖ + 1) {u : ℝ} (hu : |u| ≤ 1) (n : ℕ) :
    ‖w * shKernel (1 / 4 - w) u - firstPartial w u n‖ ≤
      (‖κ₀‖ + 2) ^ (n + 2) * expMajorant (‖κ₀‖ + 2) * |u| ^ (2 * n + 3) := by
  let B : ℝ := ‖κ₀‖ + 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hwB : ‖w‖ ≤ B := by dsimp [B]; linarith
  have hxB : ‖(1 / 4 : ℂ) - w‖ ≤ B := by
    calc
      ‖(1 / 4 : ℂ) - w‖ ≤ ‖(1 / 4 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ B := by norm_num; dsimp [B]; linarith
  rw [firstPartial_eq, ← mul_sub, norm_mul]
  calc
    ‖w‖ * ‖shKernel (1 / 4 - w) u - shPartial (1 / 4 - w) u n‖
      ≤ B * (B ^ (n + 1) * |u| ^ (2 * n + 3) * expMajorant B) := by
        exact mul_le_mul hwB (shKernel_sub_partial_norm hB hxB hu n)
          (norm_nonneg _) hB
    _ = _ := by dsimp [B]; rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]; ring

def rightCellJet (κ : ℂ) (k : ℕ) (u : ℝ) : ℂ :=
  iteratedDeriv k (fun w : ℂ => w * shKernel (1 / 4 - w) u) κ /
    (k.factorial : ℂ)

def partialJet (κ : ℂ) (k : ℕ) (u : ℝ) (n : ℕ) : ℂ :=
  iteratedDeriv k (fun w : ℂ => firstPartial w u n) κ / (k.factorial : ℂ)

theorem normalized_jet_remainder (κ : ℂ) (k : ℕ) {u : ℝ} (hu : |u| ≤ 1) (n : ℕ) :
    ‖rightCellJet κ k u - partialJet κ k u n‖ ≤
      (‖κ‖ + 2) ^ (n + 2) * expMajorant (‖κ‖ + 2) * |u| ^ (2 * n + 3) := by
  have hd := (differentiable_firstKernel u).sub (differentiable_firstPartial u n)
  have hb := norm_iteratedDeriv_le_of_entire hd k κ
    (fun w hw => firstKernel_sub_partial_norm κ hw hu n)
  have he : iteratedDeriv k (fun w : ℂ => w * shKernel (1 / 4 - w) u -
      firstPartial w u n) κ =
      iteratedDeriv k (fun w : ℂ => w * shKernel (1 / 4 - w) u) κ -
      iteratedDeriv k (fun w : ℂ => firstPartial w u n) κ := by
    exact iteratedDeriv_fun_sub (differentiable_firstKernel u).contDiff.contDiffAt
      (differentiable_firstPartial u n).contDiff.contDiffAt
  change ‖iteratedDeriv k (fun w : ℂ => w * shKernel (1 / 4 - w) u -
    firstPartial w u n) κ‖ ≤ _ at hb
  rw [he] at hb
  unfold rightCellJet partialJet
  rw [← sub_div, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < k.factorial)).mpr
  simpa [mul_comm, mul_left_comm, mul_assoc] using hb

def oddJetCoefficient (κ : ℂ) (k j : ℕ) : ℂ :=
  iteratedDeriv k (fun w : ℂ => w * (1 / 4 - w) ^ j) κ /
    (k.factorial : ℂ) / ((2 * j + 1).factorial : ℂ)

theorem partialJet_eq (κ : ℂ) (k : ℕ) (u : ℝ) (n : ℕ) :
    partialJet κ k u n =
      ∑ j ∈ Finset.range (n + 1), oddJetCoefficient κ k j * (u : ℂ) ^ (2 * j + 1) := by
  unfold partialJet firstPartial
  rw [iteratedDeriv_fun_sum]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    rw [iteratedDeriv_div_const, iteratedDeriv_mul_const_field]
    unfold oddJetCoefficient
    ring
  · intro j hj
    exact (((differentiable_id.mul (((differentiable_const (1 / 4 : ℂ)).sub
      differentiable_id).pow j)).mul_const _).div_const _).contDiff.contDiffAt

end Zeta23.OPICAFollowup.OPICARightCellTaylor
end
end

/- Verified source fragment: ShAccumulatingCoefficientExtraction.lean ; sha256=a255da208b28483c30d4bb43eb440aafa1adf051e236103e4a1a33112e97c097 -/
section

noncomputable section
open Set Filter Complex
open scoped Topology

namespace Zeta23.OPICAFollowup.OPICAShCoefficientExtraction

/-- Uniform higher-order bounds along arbitrarily small positive
parameters force a leading coefficient to vanish. -/
theorem eq_zero_of_accumulating_monomial_bound (c : ℂ) (d : ℕ) (C : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ u : ℝ, 0 < u ∧ u < ε ∧
      ‖c * (u : ℂ) ^ d‖ ≤ C * u ^ (d + 2)) : c = 0 := by
  have hex : ∀ n : ℕ, ∃ u : ℝ, 0 < u ∧ u < 1 / ((n : ℝ) + 1) ∧
      ‖c * (u : ℂ) ^ d‖ ≤ C * u ^ (d + 2) := by
    intro n
    exact h _ (by positivity)
  choose u hu0 hus hub using hex
  have hut : Tendsto u atTop (𝓝 0) :=
    squeeze_zero (fun n => (hu0 n).le) (fun n => (hus n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hb : ∀ n : ℕ, ‖c‖ ≤ C * (u n) ^ 2 := by
    intro n
    have hp : 0 < (u n) ^ d := pow_pos (hu0 n) d
    have hn := hub n
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hu0 n), pow_add] at hn
    apply (mul_le_mul_iff_of_pos_right hp).mp
    calc ‖c‖ * (u n) ^ d ≤ C * ((u n) ^ d * (u n) ^ 2) := hn
      _ = (C * (u n) ^ 2) * (u n) ^ d := by ring
  have hlim : Tendsto (fun n : ℕ => C * (u n) ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow two_ne_zero, mul_zero] using tendsto_const_nhds.mul (hut.pow 2)
  have hn : ‖c‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hb)
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg c))

/-- Coefficient extraction needs only a set of valid parameters
accumulating at zero, provided each error constant is independent of the
chosen small parameter. -/
theorem odd_coefficients_eq_zero_of_accumulating_remainder_bound
    (c : ℕ → ℂ)
    (h : ∀ n : ℕ, ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∃ u : ℝ, 0 < u ∧ u < ε ∧
      ‖∑ j ∈ Finset.range (n + 1), c j * (u : ℂ) ^ (2 * j + 1)‖ ≤
        C * u ^ (2 * n + 3)) : ∀ n : ℕ, c n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨C, hC⟩ := h n
    apply eq_zero_of_accumulating_monomial_bound (c n) (2 * n + 1) C
    intro ε hε
    obtain ⟨u, hu0, huε, hub⟩ := hC ε hε
    refine ⟨u, hu0, huε, ?_⟩
    have hs : (∑ j ∈ Finset.range (n + 1), c j * (u : ℂ) ^ (2 * j + 1)) =
        c n * (u : ℂ) ^ (2 * n + 1) := by
      apply Finset.sum_eq_single n
      · intro j hj hjn
        have hjlt : j < n := by have := Finset.mem_range.mp hj; omega
        rw [ih j hjlt, zero_mul]
      · simp
    rw [hs] at hub
    simpa [show 2 * n + 1 + 2 = 2 * n + 3 by omega] using hub


end Zeta23.OPICAFollowup.OPICAShCoefficientExtraction
end
end

/- Verified source fragment: ActualMeasureCell.lean ; sha256=e8941d6178a5042f62fd40902ac281bbb6e5ee21dbb5fa659510d3f4d10d074e -/
section

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology SchwartzMap FourierTransform

namespace Zeta23.OPICAFollowup.OPICAActualMeasureCell
open Zeta23.OPICAFollowup

/-- No integer lies in the open first cell; every lattice sample of a test
supported in that cell therefore vanishes. -/
theorem integer_samples_zero (φ : 𝓢(ℝ, ℂ))
    (hφ : Function.support (φ : ℝ → ℂ) ⊆ Ioo 1 2) (n : ℤ) : φ n = 0 := by
  by_contra hn
  have hcell := hφ hn
  have hlow : (1 : ℤ) < n := by exact_mod_cast hcell.1
  have hhigh : n < (2 : ℤ) := by exact_mod_cast hcell.2
  omega

/-- On the open first cell the actual normalized measure jet pairs with
its density alone: the actual punctured-lattice term vanishes. -/
theorem actual_jet_first_cell_pairing {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hh : ρ ≠ 1 / 2) (k : ℕ) (φ : 𝓢(ℝ, ℂ))
    (hφ : Function.support (φ : ℝ → ℂ) ⊆ Ioo 1 2) :
    (normalizedZeroMeasureJet ρ k).integral φ =
      ∫ x, zeroJetDensity (spectralKappa ρ) k x * φ x := by
  rw [normalizedZeroMeasureJet_integral h0 h1 hh]
  simp [integer_samples_zero φ hφ]

/-- A zero combination of the faithful embedded actual measure jets has
zero density pairing against every Schwartz test supported in (1,2).
Linear growth is established from the prescribed physical jet orders. -/
theorem actual_jet_combination_first_cell_integral_zero {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (ρ : ι → ℂ) (k : ι → ℕ)
    (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1)
    (hh : ∀ i, ρ i ≠ 1 / 2) (hk : ∀ i, k i < zeroJetOrder (ρ i))
    (hzero : (∑ i, c i • (normalizedZeroMeasureJet (ρ i) (k i)).distributionOfLinearGrowth
      (normalizedZeroMeasureJet_hasLinearGrowth (h0 i) (h1 i) (hh i) (hk i))) = 0)
    (φ : 𝓢(ℝ, ℂ)) (hφ : Function.support (φ : ℝ → ℂ) ⊆ Ioo 1 2) :
    (∫ x, (∑ i, c i * zeroJetDensity (spectralKappa (ρ i)) (k i) x) * φ x) = 0 := by
  have hp : (∑ i, c i * (normalizedZeroMeasureJet (ρ i) (k i)).integral φ) = 0 := by
    have he := congrArg (fun T : TemperedDistribution ℝ ℂ => T φ) hzero
    simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.zero_apply, smul_eq_mul,
      LocallyFiniteComplexMeasure.distributionOfLinearGrowth_apply] using he
  simp_rw [actual_jet_first_cell_pairing (h0 _) (h1 _) (hh _) _ φ hφ] at hp
  calc
    (∫ x, (∑ i, c i * zeroJetDensity (spectralKappa (ρ i)) (k i) x) * φ x) =
        ∑ i, c i * ∫ x, zeroJetDensity (spectralKappa (ρ i)) (k i) x * φ x := by
      simp_rw [Finset.sum_mul, mul_assoc]
      rw [integral_finset_sum]
      · simp_rw [integral_const_mul]
      · intro i _
        exact (integrable_zeroJetDensity_mul _ _ φ).const_mul (c i)
    _ = 0 := hp


end Zeta23.OPICAFollowup.OPICAActualMeasureCell
end
end

/- Verified source fragment: ActualMeasureCellAE.lean ; sha256=4ac78adea94c311af22a8fc6e318f9483d2cb09933052cc7d93d7d300047b990 -/
section

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology SchwartzMap FourierTransform ContDiff

namespace Zeta23.OPICAFollowup.OPICAActualMeasureCell
open Zeta23.OPICAFollowup

/-- The actual finite measure relation forces the physical first-cell
density combination to vanish almost everywhere. No density-zero premise
or auxiliary replacement measure is supplied. -/
theorem actual_jet_combination_first_cell_ae_zero {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (ρ : ι → ℂ) (k : ι → ℕ)
    (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1)
    (hh : ∀ i, ρ i ≠ 1 / 2) (hk : ∀ i, k i < zeroJetOrder (ρ i))
    (hzero : (∑ i, c i • (normalizedZeroMeasureJet (ρ i) (k i)).distributionOfLinearGrowth
      (normalizedZeroMeasureJet_hasLinearGrowth (h0 i) (h1 i) (hh i) (hk i))) = 0) :
    ∀ᵐ x : ℝ, x ∈ Ioo (1 : ℝ) 2 →
      (∑ i, c i * zeroJetDensity (spectralKappa (ρ i)) (k i) x) = 0 := by
  have hli : LocallyIntegrable
      (fun x : ℝ => ∑ i, c i * zeroJetDensity (spectralKappa (ρ i)) (k i) x) volume := by
    apply locallyIntegrable_finsetSum Finset.univ
    intro i _
    simpa only [Pi.smul_def, smul_eq_mul] using
      (locallyIntegrable_zeroJetDensity (spectralKappa (ρ i)) (k i)).smul (c i)
  apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hli.locallyIntegrableOn (Ioo 1 2))
  intro g hg hc hs
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let φ : 𝓢(ℝ, ℂ) := hc'.toSchwartzMap hg'
  have hφ : Function.support (φ : ℝ → ℂ) ⊆ Ioo 1 2 := by
    intro x hx
    apply hs
    apply subset_tsupport g
    change g x ≠ 0
    intro h
    apply hx
    change (g x : ℂ) = 0
    simp [h]
  have he := actual_jet_combination_first_cell_integral_zero c ρ k h0 h1 hh hk hzero φ hφ
  change (∫ x, (∑ i, c i * zeroJetDensity (spectralKappa (ρ i)) (k i) x) * (g x : ℂ)) = 0 at he
  simpa only [Complex.real_smul, mul_comm] using he


end Zeta23.OPICAFollowup.OPICAActualMeasureCell
end
end

/- Verified source fragment: ActualMeasureCellAccumulation.lean ; sha256=67e4b4fb2e22da4afffdbcef74a5f6d77ccd06ba617339dfad234146e9f8f7f8 -/
section

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology SchwartzMap FourierTransform

namespace Zeta23.OPICAFollowup.OPICAActualMeasureCell
open Zeta23.OPICAFollowup

/-- Actual first-cell density vanishing almost everywhere supplies
arbitrarily small positive logarithmic parameters at which the exact
analytic right-cell jet combination vanishes. No continuity or change of
variables theorem for a.e. sets is needed. -/
theorem first_cell_ae_zero_gives_accumulating_right_cell_zeros
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (κ : ι → ℂ) (k : ι → ℕ)
    (hAE : ∀ᵐ x : ℝ, x ∈ Ioo (1 : ℝ) 2 →
      (∑ i, c i * zeroJetDensity (κ i) (k i) x) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℝ, 0 < u ∧ u < ε ∧ u < Real.log 2 ∧
      (∑ i, c i * (iteratedDeriv (k i)
        (fun w : ℂ => w * shKernel (1 / 4 - w) u) (κ i) /
          ((k i).factorial : ℂ))) = 0 := by
  let δ : ℝ := min ε (Real.log 2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ : 0 < δ := lt_min hε hlog
  have hb : 1 < Real.exp δ := Real.one_lt_exp_iff.mpr hδ
  have hb2 : Real.exp δ ≤ 2 := by
    calc Real.exp δ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (min_le_right _ _)
      _ = 2 := Real.exp_log (by norm_num)
  have hm : volume (Ioo (1 : ℝ) (Real.exp δ)) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  obtain ⟨x, hx, hz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hm (ae_restrict_of_ae hAE)
  have hx0 : 0 < x := by linarith [hx.1]
  have hxcell : x ∈ Ioo (1 : ℝ) 2 := ⟨hx.1, hx.2.trans_le hb2⟩
  have hu0 : 0 < Real.log x := Real.log_pos hx.1
  have huδ : Real.log x < δ := (Real.log_lt_iff_lt_exp hx0).mpr hx.2
  have huε : Real.log x < ε := huδ.trans_le (min_le_left _ _)
  have hu2 : Real.log x < Real.log 2 := huδ.trans_le (min_le_right _ _)
  refine ⟨Real.log x, hu0, huε, hu2, ?_⟩
  calc
    (∑ i, c i * (iteratedDeriv (k i)
        (fun w : ℂ => w * shKernel (1 / 4 - w) (Real.log x)) (κ i) /
          ((k i).factorial : ℂ))) =
      (Real.exp (Real.log x / 2) : ℂ) *
        (∑ i, c i * zeroJetDensity (κ i) (k i) (Real.exp (Real.log x))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Zeta23.OPICAFollowup.OPICAActualFirstCellAudit.actual_normalized_jet_first_log_cell
        (κ i) (k i) hu0.le hu2]
      ring
    _ = 0 := by rw [Real.exp_log hx0, hz hxcell, mul_zero]


end Zeta23.OPICAFollowup.OPICAActualMeasureCell
end
end

/- Verified source fragment: FiniteJetCombinationRemainder.lean ; sha256=a6be6979529762ca17b8331488a8e5f9a62d21c6e8b67b3b98e0e0186fc61373 -/
section

noncomputable section
set_option maxHeartbeats 800000
open Set Filter Complex
open scoped Topology
namespace Zeta23.OPICAFollowup.OPICARightCellTaylor

variable {ι : Type*} [Fintype ι]

def combinationTaylorConstant (node : ι → ℂ) (a : ι → ℂ) (n : ℕ) : ℝ :=
  ∑ i, ‖a i‖ * ((‖node i‖ + 2) ^ (n + 2) * expMajorant (‖node i‖ + 2))

theorem finite_combination_remainder (node : ι → ℂ) (order : ι → ℕ) (a : ι → ℂ)
    {u : ℝ} (hu : |u| ≤ 1) (n : ℕ) :
    ‖(∑ j ∈ Finset.range (n + 1),
        (∑ i, a i * oddJetCoefficient (node i) (order i) j) * (u : ℂ) ^ (2 * j + 1)) -
      ∑ i, a i * rightCellJet (node i) (order i) u‖ ≤
        combinationTaylorConstant node a n * |u| ^ (2 * n + 3) := by
  classical
  have heq : (∑ j ∈ Finset.range (n + 1),
      (∑ i, a i * oddJetCoefficient (node i) (order i) j) * (u : ℂ) ^ (2 * j + 1)) =
      ∑ i, a i * partialJet (node i) (order i) u n := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [partialJet_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq, ← Finset.sum_sub_distrib]
  have hres : (∑ i, (a i * partialJet (node i) (order i) u n -
      a i * rightCellJet (node i) (order i) u)) =
      ∑ i, a i * (partialJet (node i) (order i) u n - rightCellJet (node i) (order i) u) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hres]
  calc
    ‖∑ i, a i * (partialJet (node i) (order i) u n - rightCellJet (node i) (order i) u)‖
      ≤ ∑ i, ‖a i * (partialJet (node i) (order i) u n - rightCellJet (node i) (order i) u)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i, ‖a i‖ * (((‖node i‖ + 2) ^ (n + 2) * expMajorant (‖node i‖ + 2)) *
        |u| ^ (2 * n + 3)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_sub_rev]
      exact mul_le_mul_of_nonneg_left
        (normalized_jet_remainder (node i) (order i) hu n) (norm_nonneg _)
    _ = combinationTaylorConstant node a n * |u| ^ (2 * n + 3) := by
      unfold combinationTaylorConstant
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

end Zeta23.OPICAFollowup.OPICARightCellTaylor
end
end

/- Verified source fragment: AccumulatingRightCellCoefficientBridge.lean ; sha256=24793e105e3c93af3ea061166bbbbd2fa80b53f7d4da89118224547d1cb15a77 -/
section

noncomputable section
set_option maxHeartbeats 800000
open Set Filter Complex
open scoped Topology
namespace Zeta23.OPICAFollowup.OPICARightCellTaylor

variable {ι : Type*} [Fintype ι]

theorem accumulating_rightCell_combination_coefficients_zero (node : ι → ℂ)
    (order : ι → ℕ) (a : ι → ℂ)
    (hacc : ∀ ε : ℝ, 0 < ε → ∃ u : ℝ, 0 < u ∧ u < ε ∧
      ∑ i, a i * rightCellJet (node i) (order i) u = 0) :
    ∀ n : ℕ, ∑ i, a i * oddJetCoefficient (node i) (order i) n = 0 := by
  apply Zeta23.OPICAFollowup.OPICAShCoefficientExtraction.odd_coefficients_eq_zero_of_accumulating_remainder_bound
  intro n
  refine ⟨combinationTaylorConstant node a n, ?_⟩
  intro ε hε
  obtain ⟨u, hu0, huε1, hzero⟩ := hacc (min ε 1) (lt_min hε zero_lt_one)
  have huε : u < ε := (lt_min_iff.mp huε1).1
  have hu1 : |u| ≤ 1 := by rw [abs_of_pos hu0]; exact le_of_lt (lt_min_iff.mp huε1).2
  refine ⟨u, hu0, huε, ?_⟩
  have hb := finite_combination_remainder node order a hu1 n
  rw [hzero, sub_zero, abs_of_pos hu0] at hb
  exact hb

theorem accumulating_rightCell_combination_polynomial_rows_zero (node : ι → ℂ)
    (order : ι → ℕ) (a : ι → ℂ)
    (hacc : ∀ ε : ℝ, 0 < ε → ∃ u : ℝ, 0 < u ∧ u < ε ∧
      ∑ i, a i * rightCellJet (node i) (order i) u = 0) :
    ∀ n : ℕ, ∑ i, a i *
      (iteratedDeriv (order i) (fun w : ℂ => w * (1 / 4 - w) ^ n) (node i) /
        ((order i).factorial : ℂ)) = 0 := by
  intro n
  have h := accumulating_rightCell_combination_coefficients_zero node order a hacc n
  unfold oddJetCoefficient at h
  simp_rw [← mul_div_assoc] at h
  rw [← Finset.sum_div] at h
  have hr := (div_eq_zero_iff.mp h).resolve_right
    (by exact_mod_cast Nat.factorial_ne_zero (2 * n + 1))
  simpa only [mul_div_assoc] using hr

end Zeta23.OPICAFollowup.OPICARightCellTaylor
end
end

section
noncomputable section
namespace Zeta23.OPICAFollowup.OPICARightCellTaylor
open Polynomial Zeta23.OPICAFollowup.OPICAConfluentAudit
theorem actual_polynomial_row (κ : ℂ) (k n : ℕ) :
    (Polynomial.hasseDeriv k (X * (C (1 / 4 : ℂ) - X) ^ n)).eval κ =
      iteratedDeriv k (fun w : ℂ => w * (1 / 4 - w) ^ n) κ / (k.factorial : ℂ) := by
  rw [hasse_eq_normalized_iteratedDeriv]
  congr 2
  funext w
  simp


end Zeta23.OPICAFollowup.OPICARightCellTaylor
end
end

/- Source fragment: ExpandedActualMeasureIndependence.lean ; sha256=9fbcec1be1ed58df6194444fea640dd128adc7607ad4203c81dd6a2099495fa6 -/
section

/-! Actual zero-measure independence in cumulative occurrence order.
This is not the frozen grouped primary theorem: the canonical (j,k) indexing
and grouped determinant product remain separate proof obligations. -/

noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory Filter Complex Polynomial Finset
open scoped Topology SchwartzMap FourierTransform
namespace Zeta23.OPICAFollowup.OPICAActualMeasureCell
open Zeta23.OPICAFollowup Zeta23.OPICAFollowup.OPICAConfluentAudit Zeta23.OPICAFollowup.OPICARightCellTaylor

theorem expanded_actual_zero_measure_jet_independent {M : ℕ}
    (ρ : Fin M → ℂ) (c : Fin M → ℂ)
    (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1)
    (hz : ∀ i, riemannZeta (ρ i) = 0)
    (hk : ∀ i, repeatedJetOrder (fun j => spectralKappa (ρ j)) i < zeroJetOrder (ρ i))
    (hzero : (∑ i, c i •
      (normalizedZeroMeasureJet (ρ i) (repeatedJetOrder (fun j => spectralKappa (ρ j)) i)).distributionOfLinearGrowth
        (normalizedZeroMeasureJet_hasLinearGrowth (h0 i) (h1 i) (zero_ne_half (hz i)) (hk i))) = 0) :
    c = 0 := by
  classical
  let node : Fin M → ℂ := fun i => spectralKappa (ρ i)
  have hnode (i : Fin M) : node i ≠ 0 := by
    obtain ⟨hρ0, hρ1⟩ := strip_ne (h0 i) (h1 i)
    exact mul_ne_zero hρ0 (sub_ne_zero.mpr (Ne.symm hρ1))
  have hAE := actual_jet_combination_first_cell_ae_zero c ρ (repeatedJetOrder node)
    h0 h1 (fun i => zero_ne_half (hz i)) hk hzero
  have hacc : ∀ ε : ℝ, 0 < ε → ∃ u : ℝ, 0 < u ∧ u < ε ∧
      ∑ i, c i * rightCellJet (node i) (repeatedJetOrder node i) u = 0 := by
    intro ε hε
    obtain ⟨u, hu0, huε, hu2, hvan⟩ :=
      first_cell_ae_zero_gives_accumulating_right_cell_zeros c node (repeatedJetOrder node) hAE hε
    exact ⟨u, hu0, huε, hvan⟩
  have hrows := accumulating_rightCell_combination_polynomial_rows_zero
    node (repeatedJetOrder node) c hacc
  let A : Matrix (Fin M) (Fin M) ℂ := functionalMatrix
    (fun j => hasseFunctional (node j) (repeatedJetOrder node j))
    (fun i => X * (C (1 / 4 : ℂ) - X) ^ (i : ℕ))
  have hdet : A.det ≠ 0 := by
    rw [show A = _ from rfl, profilePolynomial_confluent_expanded_determinant node hnode]
    apply mul_ne_zero
    · exact mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Finset.prod_ne_zero_iff.mpr (fun i _ => hnode i))
    · apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      have hjne : node j ≠ node i := (Finset.mem_filter.mp hj).2
      exact sub_ne_zero.mpr (Ne.symm hjne)
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet
  ext i
  change ∑ j, A i j * c j = 0
  have hrow (j : Fin M) : A i j = iteratedDeriv (repeatedJetOrder node j)
      (fun w : ℂ => w * (1 / 4 - w) ^ (i : ℕ)) (node j) /
        ((repeatedJetOrder node j).factorial : ℂ) := by
    exact actual_polynomial_row (node j) (repeatedJetOrder node j) (i : ℕ)
  simp_rw [hrow, mul_comm]
  exact hrows (i : ℕ)

end Zeta23.OPICAFollowup.OPICAActualMeasureCell
end
end

/- Source fragment: GroupedIndex.lean ; sha256=241869684c596a398871898ee0265424c7a55ad2399b266a171bd0dedbe7f504 -/
section

noncomputable section
set_option maxHeartbeats 800000
open Finset
namespace Zeta23.OPICAFollowup.OPICAGroupedConfluent

def blockStart {r : ℕ} (m : Fin r → ℕ) (j : Fin r) : ℕ := ∑ i ∈ Iio j, m i

theorem prefix_add_le_total {r : ℕ} (m : Fin r → ℕ) (j : Fin r) :
    blockStart m j + m j ≤ ∑ i, m i := by
  calc
    blockStart m j + m j = ∑ i ∈ insert j (Iio j), m i := by
      rw [Finset.sum_insert (by simp)]
      exact Nat.add_comm _ _
    _ ≤ ∑ i, m i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem prefix_add_le_prefix {r : ℕ} (m : Fin r → ℕ) {i j : Fin r} (hij : i < j) :
    blockStart m i + m i ≤ blockStart m j := by
  have hs : insert i (Iio i) ⊆ Iio j := by
    intro l hl
    rcases mem_insert.mp hl with rfl | hl
    · exact mem_Iio.mpr hij
    · exact mem_Iio.mpr ((mem_Iio.mp hl).trans hij)
  calc
    blockStart m i + m i = ∑ l ∈ insert i (Iio i), m l := by
      rw [Finset.sum_insert (by simp)]
      exact Nat.add_comm _ _
    _ ≤ blockStart m j := Finset.sum_le_sum_of_subset hs

def groupIndex {r : ℕ} (m : Fin r → ℕ) (p : (j : Fin r) × Fin (m j)) : Fin (∑ j, m j) :=
  ⟨blockStart m p.1 + p.2, (Nat.add_lt_add_left p.2.isLt _).trans_le (prefix_add_le_total m p.1)⟩

theorem groupIndex_first_lt {r : ℕ} (m : Fin r → ℕ)
    {p q : (j : Fin r) × Fin (m j)} (h : p.1 < q.1) : groupIndex m p < groupIndex m q := by
  have hp := p.2.isLt
  have hb := prefix_add_le_prefix m h
  change blockStart m p.1 + (p.2 : ℕ) < blockStart m q.1 + (q.2 : ℕ)
  omega

theorem groupIndex_injective {r : ℕ} (m : Fin r → ℕ) : Function.Injective (groupIndex m) := by
  rintro ⟨j, k⟩ ⟨l, t⟩ h
  have hv := congrArg Fin.val h
  change blockStart m j + (k : ℕ) = blockStart m l + (t : ℕ) at hv
  rcases lt_trichotomy j l with hjl | hjl | hjl
  · have hs := groupIndex_first_lt m (p := ⟨j, k⟩) (q := ⟨l, t⟩) hjl
    rw [h] at hs
    exact (lt_irrefl _ hs).elim
  · subst l
    have hkt : k = t := Fin.ext (Nat.add_left_cancel hv)
    subst t
    rfl
  · have hs := groupIndex_first_lt m (p := ⟨l, t⟩) (q := ⟨j, k⟩) hjl
    rw [h] at hs
    exact (lt_irrefl _ hs).elim

def groupEquiv {r : ℕ} (m : Fin r → ℕ) :
    ((j : Fin r) × Fin (m j)) ≃ Fin (∑ j, m j) :=
  Equiv.ofBijective (groupIndex m)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨groupIndex_injective m, by simp⟩)

def groupedNode {K : Type*} {r : ℕ} (κ : Fin r → K) (m : Fin r → ℕ)
    (i : Fin (∑ j, m j)) : K := κ ((groupEquiv m).symm i).1

theorem groupedNode_at {K : Type*} {r : ℕ} (κ : Fin r → K) (m : Fin r → ℕ)
    (p : (j : Fin r) × Fin (m j)) : groupedNode κ m (groupIndex m p) = κ p.1 := by
  change κ ((groupEquiv m).symm (groupEquiv m p)).1 = _
  rw [Equiv.symm_apply_apply]

theorem prior_nonmatch_condition {K : Type*} {r : ℕ} (κ : Fin r → K)
    (hκ : Function.Injective κ) (m : Fin r → ℕ)
    (p q : (j : Fin r) × Fin (m j)) :
    (groupIndex m p < groupIndex m q ∧ κ p.1 ≠ κ q.1) ↔ p.1 < q.1 := by
  constructor
  · rintro ⟨hidx, hne⟩
    rcases lt_trichotomy p.1 q.1 with h | h | h
    · exact h
    · exact (hne (congrArg κ h)).elim
    · exact ((not_lt_of_gt (groupIndex_first_lt m h)) hidx).elim
  · intro h
    exact ⟨groupIndex_first_lt m h, fun he => (ne_of_lt h) (hκ he)⟩

theorem grouped_node_product {K : Type*} [CommMonoid K] {r : ℕ}
    (κ : Fin r → K) (m : Fin r → ℕ) :
    (∏ i, groupedNode κ m i) = ∏ j, κ j ^ m j := by
  rw [← (groupEquiv m).prod_comp]
  simp [groupedNode, Fintype.prod_sigma]

end Zeta23.OPICAFollowup.OPICAGroupedConfluent

end
end

/- Source fragment: GroupedProducts.lean ; sha256=83a757165b337515c40ba7cf4ed13dc285c6a9b72388c8ff78e6e2d01d20a6a3 -/
section

noncomputable section
set_option maxHeartbeats 800000
open Finset
namespace Zeta23.OPICAFollowup.OPICAGroupedConfluent
open Zeta23.OPICAFollowup.OPICAConfluentAudit

theorem prior_match_condition {K : Type*} {r : ℕ} (κ : Fin r → K)
    (hκ : Function.Injective κ) (m : Fin r → ℕ)
    (p q : (j : Fin r) × Fin (m j)) :
    (groupIndex m p < groupIndex m q ∧ κ p.1 = κ q.1) ↔
      (p.1 = q.1 ∧ (p.2 : ℕ) < (q.2 : ℕ)) := by
  constructor
  · rintro ⟨hidx, he⟩
    have hj := hκ he
    refine ⟨hj, ?_⟩
    change blockStart m p.1 + (p.2 : ℕ) < blockStart m q.1 + (q.2 : ℕ) at hidx
    have hb := congrArg (blockStart m) hj
    omega
  · rintro ⟨hj, hk⟩
    refine ⟨?_, congrArg κ hj⟩
    change blockStart m p.1 + (p.2 : ℕ) < blockStart m q.1 + (q.2 : ℕ)
    have hb := congrArg (blockStart m) hj
    omega

theorem grouped_repeatedJetOrder {K : Type*} {r : ℕ} [DecidableEq K]
    (κ : Fin r → K) (hκ : Function.Injective κ) (m : Fin r → ℕ)
    (q : (j : Fin r) × Fin (m j)) :
    repeatedJetOrder (groupedNode κ m) (groupIndex m q) = (q.2 : ℕ) := by
  classical
  rcases q with ⟨j, k⟩
  unfold repeatedJetOrder priorMatches
  rw [groupedNode_at]
  dsimp only [Sigma.fst, Sigma.snd]
  rw [Finset.filter_congr_decidable]
  have hs : ((Iio (groupIndex m ⟨j, k⟩)).filter (fun i => groupedNode κ m i = κ j)) =
      univ.filter (fun i => i < groupIndex m ⟨j, k⟩ ∧ groupedNode κ m i = κ j) := by
    ext i
    simp
  rw [hs, card_eq_sum_ones, sum_filter, ← (groupEquiv m).sum_comp]
  simp only [groupedNode, Equiv.symm_apply_apply]
  change (∑ p : (j : Fin r) × Fin (m j),
    if groupIndex m p < groupIndex m ⟨j, k⟩ ∧ κ p.1 = κ j then 1 else 0) = (k : ℕ)
  simp_rw [prior_match_condition κ hκ m]
  rw [Fintype.sum_sigma, Fintype.sum_eq_single j]
  · simp only [true_and, eq_self_iff_true]
    have hi : univ.filter (fun l : Fin (m j) => (l : ℕ) < (k : ℕ)) = Iio k := by
      ext l
      simp
    rw [← sum_filter, hi, ← card_eq_sum_ones, Fin.card_Iio]
  · intro l hl
    simp [hl]

theorem grouped_prior_gap {K : Type*} [CommRing K] {r : ℕ}
    (κ : Fin r → K) (hκ : Function.Injective κ) (m : Fin r → ℕ)
    (q : (j : Fin r) × Fin (m j)) :
    (priorNonmatches (groupedNode κ m) (groupedNode κ m (groupIndex m q))
        (groupIndex m q)).prod (fun i : Fin (∑ j, m j) =>
          groupedNode κ m (groupIndex m q) - groupedNode κ m i) =
      ∏ j ∈ Iio q.1, (κ q.1 - κ j) ^ m j := by
  classical
  rw [groupedNode_at]
  unfold priorNonmatches
  have hs : ((Iio (groupIndex m q)).filter (fun i => groupedNode κ m i ≠ κ q.1)) =
      univ.filter (fun i => i < groupIndex m q ∧ groupedNode κ m i ≠ κ q.1) := by
    ext i
    simp
  rw [hs, prod_filter, ← (groupEquiv m).prod_comp]
  simp only [groupedNode, Equiv.symm_apply_apply]
  change (∏ p : (j : Fin r) × Fin (m j),
    if groupIndex m p < groupIndex m q ∧ κ p.1 ≠ κ q.1 then κ q.1 - κ p.1 else 1) = _
  simp_rw [prior_nonmatch_condition κ hκ m]
  rw [Fintype.prod_sigma]
  have hi : univ.filter (fun j : Fin r => j < q.1) = Iio q.1 := by ext j; simp
  rw [← hi, prod_filter]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hjq : j < q.1
  · simp [hjq]
  · simp [hjq]

theorem grouped_gap_product {K : Type*} [CommRing K] {r : ℕ}
    (κ : Fin r → K) (hκ : Function.Injective κ) (m : Fin r → ℕ) :
    (∏ i : Fin (∑ j, m j),
      (priorNonmatches (groupedNode κ m) (groupedNode κ m i) i).prod
        (fun j : Fin (∑ l, m l) => groupedNode κ m i - groupedNode κ m j)) =
      ∏ j, ∏ i ∈ Iio j, (κ j - κ i) ^ (m i * m j) := by
  classical
  rw [← (groupEquiv m).prod_comp]
  trans ∏ p : (j : Fin r) × Fin (m j), ∏ i ∈ Iio p.1, (κ p.1 - κ i) ^ m i
  · apply Finset.prod_congr rfl
    intro p hp
    exact grouped_prior_gap κ hκ m p
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j hj
  change (∏ _y : Fin (m j), ∏ i ∈ Iio j, (κ j - κ i) ^ m i) = _
  rw [Fin.prod_const, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← pow_mul]

end Zeta23.OPICAFollowup.OPICAGroupedConfluent

end
end

/- Source fragment: GroupedActualConfluent.lean ; sha256=e42779fef21dc97535447d012d4f496cfd0dbc59ab8c7a0f64d71522a8be46a9 -/
section

/-! Candidate exact grouped H2a contracts. These declarations are scratch only
until their complete compiler/independent expected-type gates pass. -/

noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory Filter Complex Polynomial Finset
open scoped Topology SchwartzMap FourierTransform
namespace Zeta23.OPICAFollowup
open Zeta23.OPICAFollowup.OPICAGroupedConfluent Zeta23.OPICAFollowup.OPICAConfluentAudit Zeta23.OPICAFollowup.OPICARightCellTaylor

def distinctSpectralNodes {r : ℕ} (ρ : Fin r → ℂ) : Prop :=
  Function.Injective (fun j => spectralKappa (ρ j))

/-- The exact normalized polynomial rows obtained from the actual right-cell
Taylor coefficients after clearing the nonzero odd factorials. Columns are
ordered (j,0),...,(j,m_j-1) via the explicit increasing block equivalence. -/
def profileJetMatrix {r : ℕ} (κ : Fin r → ℂ) (m : Fin r → ℕ) :
    Matrix (Fin (∑ j, m j)) (Fin (∑ j, m j)) ℂ := fun n i =>
  iteratedDeriv (((groupEquiv m).symm i).2 : ℕ)
    (fun w : ℂ => w * (1 / 4 - w) ^ (n : ℕ))
    (κ ((groupEquiv m).symm i).1) /
      ((((groupEquiv m).symm i).2 : ℕ).factorial : ℂ)

theorem profile_jet_confluent_determinant {r : ℕ} (κ : Fin r → ℂ)
    (hκ : Function.Injective κ) (hκ0 : ∀ j, κ j ≠ 0) (m : Fin r → ℕ) :
    (profileJetMatrix κ m).det =
      (-1 : ℂ) ^ ((∑ j, m j) * ((∑ j, m j) - 1) / 2) *
        (∏ j, κ j ^ m j) * ∏ j, ∏ i ∈ Iio j, (κ j - κ i) ^ (m i * m j) := by
  classical
  have ho (i : Fin (∑ j, m j)) :
      repeatedJetOrder (groupedNode κ m) i = (((groupEquiv m).symm i).2 : ℕ) := by
    have h := grouped_repeatedJetOrder κ hκ m ((groupEquiv m).symm i)
    have hi : groupIndex m ((groupEquiv m).symm i) = i := (groupEquiv m).apply_symm_apply i
    simpa only [hi] using h
  have hmatrix : profileJetMatrix κ m = functionalMatrix
      (fun j => hasseFunctional (groupedNode κ m j) (repeatedJetOrder (groupedNode κ m) j))
      (fun i => X * (C (1 / 4 : ℂ) - X) ^ (i : ℕ)) := by
    ext i j
    change _ = (Polynomial.hasseDeriv (repeatedJetOrder (groupedNode κ m) j)
      (X * (C (1 / 4 : ℂ) - X) ^ (i : ℕ))).eval (groupedNode κ m j)
    rw [actual_polynomial_row, ho]
    rfl
  rw [hmatrix, profilePolynomial_confluent_expanded_determinant
    (groupedNode κ m) (fun i => hκ0 _), grouped_node_product, grouped_gap_product κ hκ m]

theorem finite_zero_jet_independent {r : ℕ} (ρ : Fin r → ℂ)
    (hz : ∀ j, riemannZeta (ρ j) = 0)
    (h0 : ∀ j, 0 < (ρ j).re) (h1 : ∀ j, (ρ j).re < 1)
    (hdist : distinctSpectralNodes ρ) :
    LinearIndependent ℂ (fun p : (j : Fin r) × Fin (zeroJetOrder (ρ j)) =>
      (normalizedZeroMeasureJet (ρ p.1) (p.2 : ℕ)).distributionOfLinearGrowth
        (normalizedZeroMeasureJet_hasLinearGrowth (h0 p.1) (h1 p.1)
          (zero_ne_half (hz p.1)) p.2.isLt)) := by
  classical
  let m : Fin r → ℕ := fun j => zeroJetOrder (ρ j)
  let κ : Fin r → ℂ := fun j => spectralKappa (ρ j)
  let e := groupEquiv m
  let ρe : Fin (∑ j, m j) → ℂ := fun i => ρ (e.symm i).1
  have ho (i : Fin (∑ j, m j)) :
      repeatedJetOrder (fun j => spectralKappa (ρe j)) i = ((e.symm i).2 : ℕ) := by
    change repeatedJetOrder (groupedNode κ m) i = _
    have h := grouped_repeatedJetOrder κ hdist m (e.symm i)
    have hi : groupIndex m (e.symm i) = i := e.apply_symm_apply i
    simpa only [hi] using h
  have hke (i : Fin (∑ j, m j)) :
      repeatedJetOrder (fun j => spectralKappa (ρe j)) i < zeroJetOrder (ρe i) := by
    rw [ho]
    exact (e.symm i).2.isLt
  have hLI : LinearIndependent ℂ (fun i : Fin (∑ j, m j) =>
      (normalizedZeroMeasureJet (ρe i)
        (repeatedJetOrder (fun j => spectralKappa (ρe j)) i)).distributionOfLinearGrowth
          (normalizedZeroMeasureJet_hasLinearGrowth (h0 (e.symm i).1) (h1 (e.symm i).1)
            (zero_ne_half (hz (e.symm i).1)) (hke i))) := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    exact congrFun (Zeta23.OPICAFollowup.OPICAActualMeasureCell.expanded_actual_zero_measure_jet_independent
      ρe c (fun i => h0 (e.symm i).1) (fun i => h1 (e.symm i).1)
      (fun i => hz (e.symm i).1) hke hc) i
  have hcomp := hLI.comp e e.injective
  have hkcol (p : (j : Fin r) × Fin (m j)) :
      ((e.symm (e p)).2 : ℕ) = (p.2 : ℕ) :=
    congrArg (fun q : (j : Fin r) × Fin (m j) => (q.2 : ℕ)) (e.symm_apply_apply p)
  simpa [Function.comp_def, ρe, ho, hkcol] using hcomp

end Zeta23.OPICAFollowup
end
end

#print axioms Zeta23.OPICAFollowup.profile_jet_confluent_determinant
#print axioms Zeta23.OPICAFollowup.finite_zero_jet_independent

