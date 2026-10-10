#!/usr/bin/env python3
"""Regenerate research/RHRC/integration/post284/PROOF_ROOTS.json from the
#print axioms receipt lines of the post-284 Lean modules (ledger only)."""
import json, re
from pathlib import Path
REPO=Path(__file__).resolve().parents[5]
META = {
 "Zeta23/CCM/SourceLatticeCoordinates.lean": ("M04/M17","infrastructure: lattice sums, half-aperture diagonal source, centered zero extension"),
 "Zeta23/CCM/SourceSignCountermodels.lean": ("M04/M15/M18","exact integer witnesses; fourth-moment firewall at omega=1/2"),
 "Zeta23/CCM/SourceParityPolynomialCoordinates.lean": ("M17","shift-operator parity-polynomial coordinates"),
 "Zeta23/CCM/SourceParityExactInertia.lean": ("M17","exact source inertia at omega=1/2 for every K>=2"),
 "Zeta23/CCM/SourceMomentVandermondeFiltration.lean": ("M15","Vandermonde moment filtration and leading jet signs"),
 "Zeta23/CCM/SourceFourierConvolution.lean": ("M04","Fourier convolution representation"),
 "Zeta23/CCM/StrictEvenPrimeSeamDichotomy.lean": ("M11","abstract LOW/HIGH seam dichotomy"),
 "Zeta23/CCM/ContactNinthJumpGapBound.lean": ("M19","index-mass inequality and conditional ninth-jump bound"),
 "Zeta23/CCM/CanonicalRegularizedEnergyIdentity.lean": ("M05/F-M52/F-M64","canonical nonzero-endpoint regularized energy identity"),
 "Zeta23/CCM/SourceMomentFilteredInertia.lean": ("M18","moment-filtered carriers at omega=1/2: exact sign splits and indefiniteness"),
 "Zeta23/CCM/CanonicalSourceWeightedIntegral.lean": ("F-M35/F-M40/F-M54","integrated elementary source identities over omega in [0,1]; averaged negativity and sign reversal"),
 "Zeta23/CCM/SecularDeterminantKernel.lean": ("F-M20/F-M24/F-M26/F-M30","abstract rank-one secular determinant, constructive kernel, shifted secular equation, matched update; exact 2x2 crossing negative control"),
 "Zeta23/CCM/CanonicalCenteredIndexCoercivity.lean": ("F-M46","discrete Poincare coercivity C_K<5 and contact-moment corollary from the existing parity-gap theorem"),
 "Zeta23/CCM/CanonicalK2SourceSignInterval.lean": ("F-M47/F-M48","K=2 legal odd/even source negativity on 0<omega<=3/4; prime samples sign-controlled for 0<L<=log 16 (source side only)"),
}
CONDITIONAL = {
 "Zeta23.CCM.fourthMoment_lower_bound_of_gap": ["explicit gap premise delta*D2 <= B*M4"],
 "Zeta23.CCM.ninthJump_le_of_gap_conditional": ["parity-ground gap premise delta*||Dz||^2 <= B*|M4(z)| (M19 identity, OPEN)", "optimized ninth-jump formula Delta9 = -kappa*|M4|^2 (M10, OPEN)"],
 "Zeta23.CCM.strictEven_seam_dichotomy": ["degree-9 expansion of s- with O(h^10) remainder", "entering continuation s+ = s- - alpha h^9 + O(h^10), alpha>0 (M10, OPEN)", "left nonnegativity", "right negativity at arbitrarily small h"],
}
roots=[]
for rel,(pkg,desc) in META.items():
    text=(REPO/rel).read_text()
    for m in re.finditer(r'(?m)^#print\s+axioms\s+(\S+)\s*$', text):
        decl=m.group(1)
        cond = decl in CONDITIONAL
        roots.append({"declaration":decl,"source":rel,"module":rel[:-5].replace('/','.'),"package":pkg,
            "module_scope":desc,"status":"CONDITIONAL_PROVED_PENDING_CI" if cond else "PROVED_PENDING_CI",
            "premises":CONDITIONAL.get(decl,[]),
            "authority":"exact Lean theorem with its stated hypotheses; research-ledger root, not a registered claim",
            "axiom_receipt":"LOCAL_PENDING"})
out={"schema":"post284.proof_roots.v1","terminal_claim":"RH_OPEN",
 "rule":"PROVED = exact clean Lean theorem with its full premises; status becomes PROVED only after the exact PR head passes the post-284 Lean/axiom/proof-escape jobs",
 "roots":roots}
json.dump(out,open(REPO/'research/RHRC/integration/post284/PROOF_ROOTS.json','w'),indent=2)
print(len(roots))
