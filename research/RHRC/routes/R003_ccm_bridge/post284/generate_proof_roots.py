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
 "Zeta23/CCM/CanonicalRegularizedEnergyIdentity.lean": ("M05","canonical nonzero-endpoint regularized energy identity"),
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
