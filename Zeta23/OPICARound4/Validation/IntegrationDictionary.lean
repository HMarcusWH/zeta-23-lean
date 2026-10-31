import Zeta23.OPICARound4.SourceDictionaryCrosswalk

noncomputable section

namespace Zeta23.OPICARound4.Validation

open CCM Matrix

theorem diagonal_safe_source_regression_consumer (ω : ℝ) (K : ℕ) :
    (nodeJetMatrix (fun i : Fin (2 * K + 1) => (centeredIndex K i : ℝ))
      (fun x : ℝ => Real.sin (2 * Real.pi * x * ω) / Real.pi)).map
        (fun x : ℝ => (x : ℂ)) = sourceMatrix ω K :=
  diagonal_safe_source_regression ω K

theorem node_jets_suffice_consumer {ι : Type*} (nodes : ι → ℝ) (ψ φ : ℝ → ℝ)
    (hv : ∀ i, ψ (nodes i) = φ (nodes i))
    (hd : ∀ i, deriv ψ (nodes i) = deriv φ (nodes i)) :
    nodeJetMatrix nodes ψ = nodeJetMatrix nodes φ :=
  nodeJetMatrix_eq_of_node_jets nodes ψ φ hv hd

theorem integer_node_values_insufficient_consumer {ι : Type*} [Nonempty ι]
    (nodes : ι → ℤ) (ψ : ℝ → ℝ) (ε : ℝ) (hε : ε ≠ 0)
    (hψ : ∀ i, DifferentiableAt ℝ ψ (nodes i : ℝ)) :
    (∀ i, ψ (nodes i : ℝ) + ε * Real.sin (2 * Real.pi * (nodes i : ℝ)) = ψ (nodes i : ℝ)) ∧
      nodeJetMatrix (fun i => (nodes i : ℝ))
        (fun x => ψ x + ε * Real.sin (2 * Real.pi * x)) ≠
          nodeJetMatrix (fun i => (nodes i : ℝ)) ψ :=
  integer_node_values_same_matrix_ne nodes ψ ε hε hψ

theorem conditional_external_dictionary_consumer (ω : ℝ) (K : ℕ) (Φ : ℝ → ℝ)
    (hv : ∀ i : Fin (2 * K + 1), Φ (centeredIndex K i : ℝ) =
      Real.sin (2 * Real.pi * (centeredIndex K i : ℝ) * ω) / Real.pi)
    (hd : ∀ i : Fin (2 * K + 1), deriv Φ (centeredIndex K i : ℝ) =
      2 * ω * Real.cos (2 * Real.pi * (centeredIndex K i : ℝ) * ω)) :
    (nodeJetMatrix (fun i : Fin (2 * K + 1) => (centeredIndex K i : ℝ)) Φ).map
      (fun x : ℝ => (x : ℂ)) = sourceMatrix ω K :=
  external_dictionary_source_eq_of_node_jets ω K Φ hv hd

end Zeta23.OPICARound4.Validation

#print axioms Zeta23.OPICARound4.nodeJetMatrix_eq_of_node_jets
#print axioms Zeta23.OPICARound4.integer_node_values_same_matrix_ne
#print axioms Zeta23.OPICARound4.diagonal_safe_source_regression
#print axioms Zeta23.OPICARound4.external_dictionary_source_eq_of_node_jets
#print axioms Zeta23.OPICARound4.Validation.diagonal_safe_source_regression_consumer
#print axioms Zeta23.OPICARound4.Validation.node_jets_suffice_consumer
#print axioms Zeta23.OPICARound4.Validation.integer_node_values_insufficient_consumer
#print axioms Zeta23.OPICARound4.Validation.conditional_external_dictionary_consumer
