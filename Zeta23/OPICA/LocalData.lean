import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic

/-! Explicit local analytic representatives.  Source labels are data and are
retained when the observation changes.  Singular expressions are compared
only on punctured neighborhoods. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Zeta23.OPICA

structure SimplePoleData (Source : Type*) where
  source : Source
  center : ℂ
  field : ℂ → ℂ
  residue : ℂ
  residue_ne_zero : residue ≠ 0
  remainder : ℂ → ℂ
  remainder_analytic : AnalyticAt ℂ remainder center
  field_eq : field =ᶠ[𝓝[≠] center]
    fun z => residue / (z - center) + remainder z

structure MultiplierOrderData (center : ℂ) where
  multiplier : ℂ → ℂ
  order : ℕ
  unit : ℂ → ℂ
  unit_analytic : AnalyticAt ℂ unit center
  unit_ne_zero : unit center ≠ 0
  multiplier_eq : multiplier =ᶠ[𝓝 center]
    fun z => (z - center) ^ order * unit z

def SimplePoleData.regularRepresentative {Source : Type*}
    (p : SimplePoleData Source) (m : MultiplierOrderData p.center) : ℂ → ℂ :=
  fun z => (z - p.center) ^ (m.order - 1) *
    (m.unit z * (p.residue + (z - p.center) * p.remainder z))

def normalizedTaylorObservation (n : ℕ) (f : ℂ → ℂ) (center : ℂ) : ℂ :=
  iteratedDeriv n f center / n.factorial

theorem multiplier_analytic {center : ℂ} (m : MultiplierOrderData center) :
    AnalyticAt ℂ m.multiplier center := by
  exact ((analyticAt_id.sub analyticAt_const).pow m.order |>.mul
    m.unit_analytic).congr m.multiplier_eq.symm

theorem multiplier_center_value {center : ℂ} (m : MultiplierOrderData center) :
    m.multiplier center = (0 : ℂ) ^ m.order * m.unit center := by
  simpa using m.multiplier_eq.self_of_nhds

theorem multiplier_order {center : ℂ} (m : MultiplierOrderData center) :
    analyticOrderAt m.multiplier center = (m.order : ℕ∞) := by
  exact (multiplier_analytic m).analyticOrderAt_eq_natCast.mpr
    ⟨m.unit, m.unit_analytic, m.unit_ne_zero, m.multiplier_eq⟩

def MultiplierOrderData.one (center : ℂ) : MultiplierOrderData center where
  multiplier := fun _ => 1
  order := 0
  unit := fun _ => 1
  unit_analytic := analyticAt_const
  unit_ne_zero := one_ne_zero
  multiplier_eq := by simp

def MultiplierOrderData.mul {center : ℂ}
    (m n : MultiplierOrderData center) : MultiplierOrderData center where
  multiplier := fun z => m.multiplier z * n.multiplier z
  order := m.order + n.order
  unit := fun z => m.unit z * n.unit z
  unit_analytic := m.unit_analytic.mul n.unit_analytic
  unit_ne_zero := mul_ne_zero m.unit_ne_zero n.unit_ne_zero
  multiplier_eq := by
    filter_upwards [m.multiplier_eq, n.multiplier_eq] with z hm hn
    rw [hm, hn, pow_add]
    ring

def MultiplierOrderData.prod {center : ℂ} (m : ℕ → MultiplierOrderData center) :
    ℕ → MultiplierOrderData center
  | 0 => MultiplierOrderData.one center
  | n + 1 => (m n).mul (MultiplierOrderData.prod m n)

theorem multiplier_prod_order {center : ℂ} (m : ℕ → MultiplierOrderData center) (n : ℕ) :
    (MultiplierOrderData.prod m n).order = ∑ i ∈ Finset.range n, (m i).order := by
  induction n with
  | zero => simp [MultiplierOrderData.prod, MultiplierOrderData.one]
  | succ n ih =>
    simp [MultiplierOrderData.prod, MultiplierOrderData.mul, Finset.sum_range_succ, ih, Nat.add_comm]

theorem multiplier_prod_value {center : ℂ} (m : ℕ → MultiplierOrderData center)
    (n : ℕ) (z : ℂ) :
    (MultiplierOrderData.prod m n).multiplier z =
      ∏ i ∈ Finset.range n, (m i).multiplier z := by
  induction n with
  | zero => simp [MultiplierOrderData.prod, MultiplierOrderData.one]
  | succ n ih =>
    simp [MultiplierOrderData.prod, MultiplierOrderData.mul, Finset.prod_range_succ, ih, mul_comm]

end Zeta23.OPICA
