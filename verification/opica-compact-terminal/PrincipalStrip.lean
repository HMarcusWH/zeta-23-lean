import New.ArithmeticOnly

/-!
Attribution: arithmetic supply and conditional one-sided criterion from
Alpöge/Claude/Anthropic, lsernau/grh-lean at 72fead102f663d5c7a407964a13dc0cf9d977207
(Apache-2.0). New fixed-exponent conductor-one adapter. No Main, Statements,
New.grh, or unconditional RH/GRH declaration imported.
-/
noncomputable section
open DirichletCharacter Real Filter Nat ZMod Parameters

namespace OPICACompactSupplier

/-- Exactly the conditional criterion's arithmetic input, at the fixed
modulus/class M=18480, a=9239. Thresholds can depend on d and β. -/
def PrincipalWeightedUpper (β : ℝ) : Prop :=
  ∀ d : Nat.Primes, (d : ZMod 18480) = (9239 : ZMod 18480) →
    (d.1 % 8 = 7 ∧ (18480 : ℕ).Coprime d) ∧
    ∀ᶠ x : ℝ in atTop, primeError d 18480 x ≤ x ^ (β - 1)

theorem weighted_upper_at (P : Parameters) {β : ℝ}
    (hβ : 1 / 2 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, primeError P.d P.N₀ x ≤ x ^ (β - 1) := by
  let ε : ℝ := (β - 1 / 2) / 51
  have hε : 0 < ε / 6 ∧ ε < 1 / 100 := by
    dsimp [ε]
    constructor <;> linarith
  have hexp : 8 * ε + (2 : ℝ)⁻¹ - 1 ≤ β - 1 := by
    dsimp [ε]
    norm_num
    linarith
  filter_upwards [eventually_primeError_le_rpow P hε,
    eventually_ge_atTop (1 : ℝ)] with x hx hx1
  exact hx.trans (Real.rpow_le_rpow_of_exponent_le hx1 hexp)

/-- Closed arithmetic supplier, not a zero-exclusion theorem. -/
theorem principal_weighted_upper {β : ℝ}
    (hβ : 1 / 2 < β) (hβ1 : β < 1) : PrincipalWeightedUpper β := by
  intro d hd
  have hmod : (d : ℕ) % 18480 = 9239 := by
    have hm : (d : ℕ) ≡ 9239 [MOD 18480] :=
      (ZMod.natCast_eq_natCast_iff (d : ℕ) 9239 18480).1 hd
    simpa [Nat.ModEq] using hm
  let P : Parameters := ⟨18480, d, dvd_refl _, d.2, by
    constructor <;> omega⟩
  exact ⟨⟨P.instHeegD.2, (P.coprime_N₁_d 0).coprime_mul_right⟩,
    weighted_upper_at P hβ hβ1⟩

/-- Fixed-exponent analytic transfer, with the arithmetic hypothesis exposed.
The conditional upstream Landau/twist-avoidance theorem is deliberately
reused. This is not a formalization of the supplement's separate Taylor
moment proof or of its integrated explicit formula. -/
theorem zeta_ne_zero_of_principal_weighted_upper {β : ℝ}
    (hβ : 1 / 2 < β) (h : PrincipalWeightedUpper β)
    (ρ : ℂ) (hρ : β < ρ.re) (hs1 : ρ ≠ 1) : riemannZeta ρ ≠ 0 := by
  intro hz
  let χ : DirichletCharacter ℂ 1 := 1
  have hχ : χ.LFunction ρ = 0 := by
    rw [DirichletCharacter.LFunction_modOne_eq]
    exact hz
  have h_induced :
      entireL (χ.changeLevel (show 1 ∣ 18480 by decide)) ρ = 0 := by
    rw [entireL]
    grind [LFunction_changeLevel, changeLevel_eq_one_iff]
  have ha : IsUnit (9239 : ZMod 18480) :=
    .of_mul_eq_one (9239 : ZMod 18480) (by decide)
  exact entireL_ne_zero_of_primeError_le (M := 18480)
    (a := 9239) hβ ha h ρ hρ _ h_induced

/-- One fixed tolerance at a time, not an imported terminal RH/GRH result. -/
theorem principal_fixed_strip {β : ℝ} (hβ : 1 / 2 < β)
    (hβ1 : β < 1) (ρ : ℂ) (hs1 : ρ ≠ 1)
    (hz : riemannZeta ρ = 0) : ρ.re ≤ β := by
  by_contra hn
  exact zeta_ne_zero_of_principal_weighted_upper hβ
    (principal_weighted_upper hβ hβ1) ρ (lt_of_not_ge hn) hs1 hz

end OPICACompactSupplier
