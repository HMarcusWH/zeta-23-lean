import Zeta23.OPICARound4.NativeSourceBudget
import Zeta23.OPICARound4.NativeJointIndex

noncomputable section
namespace Zeta23.OPICARound4.SearchSupport

/-- An explicit independent margin consumes a one-sided signed estimate. -/
theorem strict_response_of_signed_upper {gap response cost : ℝ}
    (hgap : 0 < gap) (hupper : gap * response ≤ cost) (hcost : cost < gap) :
    response < 1 := by
  nlinarith

/-- Only the index identification, not the native two-plane producer. -/
theorem index_two_contradicts_cap {n : ℕ} (htwo : n = 2) (hcap : n ≤ 1) : False := by
  omega

end Zeta23.OPICARound4.SearchSupport
