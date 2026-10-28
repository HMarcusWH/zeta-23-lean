import Zeta23.CCM.DictionaryAnalysis

noncomputable section

namespace Zeta23.OPICARound4

open CCM Matrix

variable {ι : Type*}

/-- A confluent divided difference: equal nodes use the actual derivative.
This includes the diagonal and repeated nodes, without a distinctness premise. -/
def nodeJetMatrix (nodes : ι → ℝ) (ψ : ℝ → ℝ) : Matrix ι ι ℝ := by
  classical
  exact fun i j => if nodes i = nodes j then deriv ψ (nodes i)
    else (ψ (nodes i) - ψ (nodes j)) / (nodes i - nodes j)

@[simp] theorem nodeJetMatrix_diagonal (nodes : ι → ℝ) (ψ : ℝ → ℝ) (i : ι) :
    nodeJetMatrix nodes ψ i i = deriv ψ (nodes i) := by
  classical
  simp [nodeJetMatrix]

/-- The conditional dictionary adapter needs both values and derivatives.
No external dictionary theorem is assumed or imported. -/
theorem nodeJetMatrix_eq_of_node_jets (nodes : ι → ℝ) (ψ φ : ℝ → ℝ)
    (hv : ∀ i, ψ (nodes i) = φ (nodes i))
    (hd : ∀ i, deriv ψ (nodes i) = deriv φ (nodes i)) :
    nodeJetMatrix nodes ψ = nodeJetMatrix nodes φ := by
  classical
  ext i j
  dsimp only [nodeJetMatrix]
  split_ifs
  · exact hd i
  · rw [hv i, hv j]

def integerNodePerturb (ψ : ℝ → ℝ) (ε : ℝ) (x : ℝ) : ℝ :=
  ψ x + ε * Real.sin (2 * Real.pi * x)

theorem integerNodePerturb_value (ψ : ℝ → ℝ) (ε : ℝ) (n : ℤ) :
    integerNodePerturb ψ ε (n : ℝ) = ψ (n : ℝ) := by
  have hs : Real.sin (2 * Real.pi * (n : ℝ)) = 0 := by
    rw [show 2 * Real.pi * (n : ℝ) = (n : ℝ) * (2 * Real.pi) by ring]
    simpa using Real.sin_add_int_mul_two_pi 0 n
  simp [integerNodePerturb, hs]

theorem integerNodePerturb_hasDerivAt (ψ : ℝ → ℝ) (ε : ℝ) (n : ℤ)
    (hψ : DifferentiableAt ℝ ψ (n : ℝ)) :
    HasDerivAt (integerNodePerturb ψ ε)
      (deriv ψ (n : ℝ) + 2 * Real.pi * ε) (n : ℝ) := by
  have hs : HasDerivAt (fun x : ℝ => Real.sin (2 * Real.pi * x))
      (2 * Real.pi) (n : ℝ) := by
    convert! (((hasDerivAt_id (n : ℝ)).const_mul (2 * Real.pi)).sin) using 1
    dsimp only [id_eq]
    rw [show 2 * Real.pi * (n : ℝ) = (n : ℝ) * (2 * Real.pi) by ring,
      Real.cos_int_mul_two_pi]
    ring
  convert! hψ.hasDerivAt.add (hs.const_mul ε) using 1
  ring

theorem integerNodePerturb_deriv (ψ : ℝ → ℝ) (ε : ℝ) (n : ℤ)
    (hψ : DifferentiableAt ℝ ψ (n : ℝ)) :
    deriv (integerNodePerturb ψ ε) (n : ℝ) = deriv ψ (n : ℝ) + 2 * Real.pi * ε :=
  (integerNodePerturb_hasDerivAt ψ ε n hψ).deriv

/-- Exact values-only negative control on any nonempty integer-node family.
The perturbation preserves every sampled value and shifts every diagonal by
2*pi*epsilon, so it changes the actual derivative-based matrix. -/
theorem integer_node_values_same_matrix_ne [Nonempty ι] (nodes : ι → ℤ)
    (ψ : ℝ → ℝ) (ε : ℝ) (hε : ε ≠ 0)
    (hψ : ∀ i, DifferentiableAt ℝ ψ (nodes i : ℝ)) :
    (∀ i, integerNodePerturb ψ ε (nodes i : ℝ) = ψ (nodes i : ℝ)) ∧
      nodeJetMatrix (fun i => (nodes i : ℝ)) (integerNodePerturb ψ ε) ≠
        nodeJetMatrix (fun i => (nodes i : ℝ)) ψ := by
  classical
  refine ⟨fun i => integerNodePerturb_value ψ ε (nodes i), ?_⟩
  intro hm
  let i : ι := Classical.arbitrary ι
  have hd := congrFun (congrFun hm i) i
  rw [nodeJetMatrix_diagonal, nodeJetMatrix_diagonal,
    integerNodePerturb_deriv ψ ε (nodes i) (hψ i)] at hd
  have hz : 2 * Real.pi * ε = 0 := by linarith
  exact (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hε) hz

/-- The native sine potential as a real function, including its true jets. -/
def nativeSinePotential (ω : ℝ) (x : ℝ) : ℝ :=
  Real.sin (2 * Real.pi * x * ω) / Real.pi

theorem nativeSinePotential_hasDerivAt (ω x : ℝ) :
    HasDerivAt (nativeSinePotential ω)
      (2 * ω * Real.cos (2 * Real.pi * x * ω)) x := by
  have hp : HasDerivAt (fun y : ℝ => 2 * Real.pi * y * ω)
      (2 * Real.pi * ω) x := by
    convert! ((hasDerivAt_id x).const_mul (2 * Real.pi)).mul_const ω using 1
    ring
  convert! hp.sin.div_const Real.pi using 1
  field_simp [Real.pi_ne_zero]

theorem nativeSinePotential_deriv (ω x : ℝ) :
    deriv (nativeSinePotential ω) x = 2 * ω * Real.cos (2 * Real.pi * x * ω) :=
  (nativeSinePotential_hasDerivAt ω x).deriv

theorem native_sine_nodeJet_eq_sourceEntryReal (ω : ℝ) (nodes : ι → ℤ) (i j : ι) :
    nodeJetMatrix (fun i => (nodes i : ℝ)) (nativeSinePotential ω) i j =
      sourceEntryReal ω (nodes i) (nodes j) := by
  classical
  by_cases h : nodes i = nodes j
  · simp [nodeJetMatrix, h, nativeSinePotential_deriv, sourceEntryReal, sourceDiagonalReal]
  · have hr : (nodes i : ℝ) ≠ (nodes j : ℝ) := by exact_mod_cast h
    simp [nodeJetMatrix, hr, sourceEntryReal, h, nativeSinePotential,
      sourcePotentialReal, Int.cast_sub]

/-- Named exact, diagonal-safe regression against the actual native source. -/
theorem diagonal_safe_source_regression (ω : ℝ) (K : ℕ) :
    (nodeJetMatrix (fun i : Fin (2 * K + 1) => (centeredIndex K i : ℝ))
      (nativeSinePotential ω)).map (fun x : ℝ => (x : ℂ)) = sourceMatrix ω K := by
  ext i j
  rw [Matrix.map_apply, native_sine_nodeJet_eq_sourceEntryReal,
    sourceMatrix_apply, sourceEntry_eq_ofReal]

/-- A proposed external potential can identify this actual finite source only
after its real node values AND actual derivative values are proved. The
real-even/odd-complex dictionary crosswalk itself remains OPEN. -/
theorem external_dictionary_source_eq_of_node_jets (ω : ℝ) (K : ℕ) (Φ : ℝ → ℝ)
    (hv : ∀ i : Fin (2 * K + 1), Φ (centeredIndex K i : ℝ) =
      nativeSinePotential ω (centeredIndex K i : ℝ))
    (hd : ∀ i : Fin (2 * K + 1), deriv Φ (centeredIndex K i : ℝ) =
      2 * ω * Real.cos (2 * Real.pi * (centeredIndex K i : ℝ) * ω)) :
    (nodeJetMatrix (fun i : Fin (2 * K + 1) => (centeredIndex K i : ℝ)) Φ).map
      (fun x : ℝ => (x : ℂ)) = sourceMatrix ω K := by
  rw [nodeJetMatrix_eq_of_node_jets _ Φ (nativeSinePotential ω) hv
    (fun i => (hd i).trans (nativeSinePotential_deriv _ _).symm)]
  exact diagonal_safe_source_regression ω K

end Zeta23.OPICARound4
