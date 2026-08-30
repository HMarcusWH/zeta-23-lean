import Zeta23.CCM.DictionaryResidualSecondOrderGluing
import Zeta23.CCM.DictionaryTentZeroSummability
import Zeta23.CCM.DictionaryTentMollifierSupport
import Zeta23.CCM.DictionaryTentEFExtension
import Zeta23.CCM.DictionaryZeroSideBridge
import Zeta23.CCM.DictionaryRHSIdentity
import Zeta23.ExceptionalZero.DisplacementTransfer

/-!
# R003 promoted-claim theorem bindings

This module pins promoted RHRC claim IDs to concrete Lean theorem names so that
`lake build Zeta23.CCM` checks the promoted theorem surface transitively.
-/

#check Zeta23.CCM.dictionaryResidualTest_admissible
#check Zeta23.CCM.dictionaryTent_analytic_package
#check Zeta23.CCM.dictionaryTent_mollifier_architecture_package
#print axioms Zeta23.CCM.dictionaryTent_mollifier_architecture_package
#check Zeta23.CCM.dictionaryTent_zero_sum_eq_literatureRHS
#print axioms Zeta23.CCM.dictionaryTent_zero_sum_eq_literatureRHS
#check Zeta23.CCM.dictionaryTent_explicitFormula
#print axioms Zeta23.CCM.dictionaryTent_explicitFormula
#check Zeta23.CCM.dictionaryTentDefect_eq_zero
#print axioms Zeta23.CCM.dictionaryTentDefect_eq_zero
#check Zeta23.CCM.zeroSideMatrix_eq_dictionaryMatrix
#print axioms Zeta23.CCM.zeroSideMatrix_eq_dictionaryMatrix
#check Zeta23.CCM.zeroSideMatrix_eq_finiteMatrix_add_correction
#print axioms Zeta23.CCM.zeroSideMatrix_eq_finiteMatrix_add_correction
#check Zeta23.CCM.literatureRHS_dictionaryTest_eq_quadraticForm
#print axioms Zeta23.CCM.literatureRHS_dictionaryTest_eq_quadraticForm
#check Zeta23.ExceptionalZero.rank_displacement_le_two_of_eq_smul_add_scalar
