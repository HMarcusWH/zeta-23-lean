#!/usr/bin/env python3
"""Finite 768-bit seam calibration controls; these do not certify a continuum."""
import json
import sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
import canonical_source_arb as C
from flint import arb,ctx


def main():
    C.set_precision(768);ctx.prec=768
    rows=[]
    for q in range(2,17):
        L=arb(q).log()
        if not bool(L>0):
            raise AssertionError("nonzero logarithmic aperture required")
        coordinate=1-arb(q).log()/L
        C.require_finite(coordinate)
        if not coordinate.contains(0):
            raise AssertionError("entering source coordinate misses exact omega=0")
        for n in range(-3,4):
            for m in range(-3,4):
                endpoint=C.q_basis(n,m,L,L)
                entering=C.von_mangoldt(q)/arb(q).sqrt()*endpoint
                C.require_finite(endpoint,entering)
                if not endpoint.contains(0) or not entering.contains(0):
                    raise AssertionError(("entering atom does not enclose exact zero",q,n,m))
        rows.append({"q":q,"aperture":f"log({q})","coordinate":"omega=0","entries_checked":49,"finite_zero_enclosure":True})
    print(json.dumps({"schema":"post290.k3-seam-controls.v1","evidence_type":"FINITE_CALIBRATION_CONTROL","precision_bits":768,"seams":15,"entries":735,
        "theorem_bindings":["Zeta23.CCM.qBasis_aperture_eq_zero","Zeta23.CCM.primeSourceCoordinate_log_add","Zeta23.CCM.sourceMatrix_zero"],"rows":rows,"terminal_claim":"RH_OPEN","not_a_continuous_certificate":True},sort_keys=True))


if __name__=="__main__":
    main()
