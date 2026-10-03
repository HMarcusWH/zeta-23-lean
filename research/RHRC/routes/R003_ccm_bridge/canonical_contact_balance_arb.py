#!/usr/bin/env python3
"""Rigorous/fail-closed post-#282 contact-balance diagnostics.

The spectral/eigenvector/response lane uses Arb enclosures and a certified
bordered inverse. Direct physical remainder integration remains independent:
where it is not rigorously resolved the row stays unresolved rather than
borrowing the theorem being tested.

Research/certification infrastructure only. RH remains OPEN.
"""
from __future__ import annotations
import json, math, sys
from pathlib import Path
import numpy as np
from flint import arb, arb_mat, ctx

ROUTE=Path(__file__).resolve().parent
RHRC=ROUTE.parents[1]
sys.path.insert(0,str(RHRC/"closure_batch"))
from interval_codec import DyadicInterval
from canonical_contact_frontier_arb import (
    restricted_jets, _mid_matrix, _eigs, _ball_record_full, _bounds_record,
    _arb_col, _norm_sq, _quad_quotient, _frobenius_upper_arb,
    _residual_upper_arb,
)
from post247_remainder_budget_ratio_scout import (
    boundary_flat_parity_basis, orthonormalizer,
)
from post194_fb05_q14_fixed_unit_second_derivative import (
    fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb,
)
from certify_post281_generated_contact_frontier import ladder_point
import post280_saturation_frontier as floating


def interval_record(x: arb) -> dict:
    d=DyadicInterval.from_arb(x)
    return {
        "dyadic_interval":d.to_json(),"sign":d.sign(),
        "display_mid":str(x.mid()),"display_rad":str(x.rad()),
        "display_only":True,
    }


def _arb_identity(n:int)->arb_mat:
    return arb_mat([[arb(1 if i==j else 0) for j in range(n)] for i in range(n)])


def _arb_from_numpy(A:np.ndarray)->arb_mat:
    return arb_mat([[arb(repr(float(A[i,j]))) for j in range(A.shape[1])]
                    for i in range(A.shape[0])])


def _vec_ball(v:np.ndarray,rad:arb)->arb_mat:
    r=rad.upper()
    return arb_mat([[arb(repr(float(x)),r)] for x in np.asarray(v,dtype=float)])


def _vec_norm_upper(v:arb_mat)->arb:
    s=arb(0)
    for i in range(v.nrows()):
        u=abs(v[i,0]).upper(); s+=u*u
    return s.sqrt().upper()


def _interval_overlap(a:arb,b:arb)->bool:
    return not (bool(a.upper()<b.lower()) or bool(b.upper()<a.lower()))


def simple_ground_bundle(L:arb,K:int,Q:int,parity:str,prec:int)->dict:
    ctx.prec=int(prec)
    H,Hp,Hpp=restricted_jets(L,K,Q,parity)
    try:
        eigs=_eigs(H)
    except ValueError as exc:
        return {"status":"EIGENSOLVER_UNRESOLVED","error":str(exc)}
    d=H.nrows()
    if d==0: return {"status":"ZERO_DIMENSIONAL_CARRIER"}
    Hmid=_mid_matrix(H)
    _,vecs=np.linalg.eigh((Hmid+Hmid.T)/2)
    v0=np.asarray(vecs[:,0],dtype=float);v0/=np.linalg.norm(v0)
    V0=_arb_col(v0); theta=_quad_quotient(H,V0)
    if d==1:
        angle=arb(0);gap=None;status="CERTIFIED_ONE_DIMENSIONAL"
    else:
        gap=eigs[1].lower()-eigs[0].upper()
        if not bool(gap>0):
            return {"status":"GROUND_CLUSTER_UNRESOLVED",
                    "lambda":_ball_record_full(eigs[0]),
                    "lambda_2":_ball_record_full(eigs[1])}
        residual=_residual_upper_arb(H,V0,theta)
        norm_lower=_norm_sq(V0).lower().sqrt()
        sep=eigs[1].lower()-theta.upper()
        if not (bool(norm_lower>0) and bool(sep>0)):
            return {"status":"EIGENVECTOR_ENCLOSURE_UNRESOLVED"}
        angle=(residual/norm_lower)/sep
        if bool(angle>1): angle=arb(1)
        status="SIMPLE_GROUND_RESOLVED"
    V=_vec_ball(v0,angle)
    j1=_quad_quotient(Hp,V)
    fixed2=_quad_quotient(Hpp,V)
    return {
        "status":status,"H":H,"Hp":Hp,"Hpp":Hpp,"eigs":eigs,
        "v0":v0,"V":V,"angle":angle,"lambda":eigs[0],"gap":gap,
        "j1":j1,"fixed2":fixed2,
        "record":{"status":status,"lambda":_ball_record_full(eigs[0]),
                  "j1":_ball_record_full(j1),"fixed_second":_ball_record_full(fixed2),
                  "angle_upper_exact":angle.upper().str(30,radius=False),"dimension":d},
    }


def validated_bordered_response(bundle:dict)->dict:
    if bundle.get("status") not in {"SIMPLE_GROUND_RESOLVED","CERTIFIED_ONE_DIMENSIONAL"}:
        return {"status":"INELIGIBLE_GROUND"}
    H,Hp=bundle["H"],bundle["Hp"];V=bundle["V"];lam=bundle["lambda"];j1=bundle["j1"]
    d=H.nrows()
    if d==1:
        W=arb_mat([[arb(0)]])
        return {"status":"CERTIFIED_ZERO_COMPLEMENT_RESPONSE","W":W,
                "response_norm":interval_record(arb(0)),
                "orthogonality":interval_record((V.transpose()*W)[0,0]),
                "inverse_certificate":{"rho_upper_exact":"0","correction_upper_exact":"0"}}
    I=_arb_identity(d);A=H-lam*I
    top_rhs=-(Hp-j1*I)*V
    B=arb_mat(d+1,d+1);rhs=arb_mat(d+1,1)
    for i in range(d):
        for j in range(d): B[i,j]=A[i,j]
        B[i,d]=V[i,0];B[d,i]=V[i,0];rhs[i,0]=top_rhs[i,0]
    B[d,d]=arb(0);rhs[d,0]=arb(0)
    Bmid=_mid_matrix(B)
    try: Xnp=np.linalg.inv(Bmid)
    except np.linalg.LinAlgError: return {"status":"BORDERED_MIDPOINT_SINGULAR"}
    X=_arb_from_numpy(Xnp);R=_arb_identity(d+1)-X*B
    rho=_frobenius_upper_arb(R)
    if not bool(rho<1):
        return {"status":"BORDERED_INVERSE_UNRESOLVED","rho_upper_exact":rho.str(30,radius=False)}
    rhsmid=np.array([float(rhs[i,0].mid()) for i in range(d+1)])
    x0=Xnp@rhsmid;X0=arb_mat([[arb(repr(float(x0[i])))] for i in range(d+1)])
    resid=rhs-B*X0;resid_norm=_vec_norm_upper(resid)
    inv_bound=arb(repr(float(np.linalg.norm(Xnp,ord="fro"))))/(1-rho)
    corr=(inv_bound*resid_norm).upper()
    Xball=arb_mat([[arb(repr(float(x0[i])),corr)] for i in range(d+1)])
    W=arb_mat([[Xball[i,0]] for i in range(d)])
    response_residual=A*W+Hp*V-j1*V
    return {"status":"CERTIFIED_BORDERED_RESPONSE","W":W,
            "response_norm":interval_record((_norm_sq(W)).sqrt()),
            "orthogonality":interval_record((V.transpose()*W)[0,0]),
            "response_residual_norm_upper_exact":_vec_norm_upper(response_residual).str(30,radius=False),
            "inverse_certificate":{"rho_upper_exact":rho.str(30,radius=False),
                "midpoint_inverse_frobenius":float(np.linalg.norm(Xnp,ord="fro")),
                "residual_norm_upper_exact":resid_norm.str(30,radius=False),
                "correction_upper_exact":corr.str(30,radius=False)}}


def _orthonormal_full_basis(K:int,parity:str)->arb_mat:
    V=boundary_flat_parity_basis(K,parity);Linv=orthonormalizer(V)
    return V*Linv.transpose()


def q_representations(L:arb,K:int,Q:int,bundle:dict)->dict:
    if bundle.get("status") not in {"SIMPLE_GROUND_RESOLVED","CERTIFIED_ONE_DIMENSIONAL"}:
        return {"status":"INELIGIBLE_GROUND"}
    M,_,_=fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb(L,K,Q)
    U=_orthonormal_full_basis(K,"even");z=U*bundle["V"]
    ns=list(range(-K,K+1));n2=[arb(n*n) for n in ns]
    mean=sum(n2,arb(0))/arb(len(n2));normal=arb_mat([[x-mean] for x in n2])
    den=(normal.transpose()*normal)[0,0];S=(normal.transpose()*M*z)[0,0]/den
    m4=arb(0);Dz=arb_mat(2*K+1,1)
    for i,n in enumerate(ns):
        m4+=arb(n**4)*z[i,0];Dz[i,0]=arb(n)*z[i,0]
    q_arith=m4*S
    q_spec=(Dz.transpose()*M*Dz)[0,0]-bundle["lambda"]*(Dz.transpose()*Dz)[0,0]
    return {"status":"CERTIFIED_MATRIX_CONTRACTIONS","source_moment":interval_record(S),
            "M4":interval_record(m4),"Q_arithmetic":interval_record(q_arith),
            "Q_spectral_shifted":interval_record(q_spec),"overlap":_interval_overlap(q_arith,q_spec),
            "_q_arith":q_arith,"_q_spec":q_spec}


def curvature_enclosure(bundle:dict,response:dict)->dict:
    if response.get("status") not in {"CERTIFIED_BORDERED_RESPONSE","CERTIFIED_ZERO_COMPLEMENT_RESPONSE"}:
        return {"status":"RESPONSE_UNRESOLVED"}
    V,W=bundle["V"],response["W"]
    fixed=(V.transpose()*bundle["Hpp"]*V)[0,0]/(V.transpose()*V)[0,0]
    mixed=(V.transpose()*bundle["Hp"]*W)[0,0]
    kappa=fixed+2*mixed
    return {"status":"CERTIFIED_FROM_JETS_AND_RESPONSE",
            "fixed_second":interval_record(fixed),"mixed_twice":interval_record(2*mixed),
            "optimized_curvature":interval_record(kappa),"_kappa":kappa}


def projected_dilation_defect(K:int,bundle:dict,response:dict,L:arb)->dict:
    if response.get("status") not in {"CERTIFIED_BORDERED_RESPONSE","CERTIFIED_ZERO_COMPLEMENT_RESPONSE"}:
        return {"status":"RESPONSE_UNRESOLVED"}
    U=_orthonormal_full_basis(K,"even");ns=list(range(-K,K+1))
    H=arb_mat(2*K+1,2*K+1)
    for i,n in enumerate(ns):
        for j,m in enumerate(ns):
            H[i,j]=arb(1)/2 if i==j else arb(m)/arb(m-n)
    T=U.transpose()*H*U;V,W=bundle["V"],response["W"]
    Tv=T*V;coeff=(V.transpose()*Tv)[0,0]/(V.transpose()*V)[0,0]
    defect=Tv-coeff*V-L*W
    return {"status":"NEAR_CONTACT_DIAGNOSTIC_ONLY",
            "defect_norm_upper_exact":_vec_norm_upper(defect).str(30,radius=False),
            "pointwise_exact_contact_law_claimed":False}


def selected_balance(cand:dict,prec:int)->dict:
    Q=int(cand["Q"]);K=int(cand["K"]);frac=cand.get("cell_fraction")
    if frac is None:
        a,b=cand["fraction_left"],cand["fraction_right"]
        frac=[a[0]*b[1]+b[0]*a[1],2*a[1]*b[1]]
    lo=arb(1)/512 if Q==1 else arb(Q).log();hi=arb(2).log() if Q==1 else arb(Q+1).log()
    L=lo+(hi-lo)*arb(frac[0])/arb(frac[1])
    bundle=simple_ground_bundle(L,K,Q,"even",prec)
    public={"candidate":cand,"L_exact_fraction":frac,
            "ground":bundle.get("record",{"status":bundle.get("status")})}
    if "H" not in bundle:
        public["status"]="GROUND_UNRESOLVED";return public
    response=validated_bordered_response(bundle);qrep=q_representations(L,K,Q,bundle)
    curv=curvature_enclosure(bundle,response);defect=projected_dilation_defect(K,bundle,response,L)
    public.update({"response":{k:v for k,v in response.items() if k!="W"},
        "Q":{k:v for k,v in qrep.items() if not k.startswith("_")},
        "curvature":{k:v for k,v in curv.items() if not k.startswith("_")},
        "projected_dilation":defect,
        "physical_remainder":{"status":"RIGOROUS_DIRECT_PHYSICAL_INTEGRAL_NOT_RESOLVED","used_for_certificate":False},
        "saturation_gap":{"status":"UNRESOLVED_UNTIL_INDEPENDENT_PHYSICAL_REMAINDER","used_for_certificate":False},
        "rho":{"status":"INELIGIBLE_WITHOUT_INDEPENDENT_REMAINDER"}})
    try:
        frow=floating.evaluate(float(L.mid()),K)
        public["floating_crosscheck"]={k:frow.get(k) for k in (
            "Q_arithmetic","Q_spectral_reduced","production_arithmetic_remainder",
            "production_remainder_integral_error_estimate","delta_sat_proxy",
            "kappa_fd","delta_minus_kappa_fd")}
        public["floating_crosscheck"]["certificate_authority"]=False
    except Exception as exc:
        public["floating_crosscheck"]={"status":"ERROR","error":str(exc),"certificate_authority":False}
    public["status"]="PARTIALLY_CERTIFIED_SPECTRAL_RESPONSE_Q";return public


def one_dimensional_calibration(L:arb,K:int,Q:int,parity:str,prec:int)->dict:
    bundle=simple_ground_bundle(L,K,Q,parity,prec)
    if "H" not in bundle:return {"status":bundle.get("status","UNRESOLVED")}
    response=validated_bordered_response(bundle);curvature=curvature_enclosure(bundle,response)
    return {"status":"CERTIFIED_ONE_DIMENSIONAL_DIRECTION" if bundle["H"].nrows()==1 else "NOT_ONE_DIMENSIONAL",
            "dimension":bundle["H"].nrows(),"energy":interval_record(bundle["lambda"]),
            "j1":interval_record(bundle["j1"]),"fixed_second":interval_record(bundle["fixed2"]),
            "response":{k:v for k,v in response.items() if k!="W"},
            "optimized_curvature":curvature.get("optimized_curvature")}


def log2_seam_calibration(prec:int)->dict:
    ctx.prec=int(prec);L=arb(2).log()
    left=one_dimensional_calibration(L,2,1,"even",prec);right=one_dimensional_calibration(L,2,2,"even",prec)
    def overlap(field):
        if field not in left or field not in right:return False
        a=DyadicInterval.from_json(left[field]["dyadic_interval"]);b=DyadicInterval.from_json(right[field]["dyadic_interval"])
        return not (a.hi<b.lo or b.hi<a.lo)
    energy_pos=left.get("energy",{}).get("sign")=="POSITIVE" and right.get("energy",{}).get("sign")=="POSITIVE"
    j1_neg=left.get("j1",{}).get("sign")=="NEGATIVE" and right.get("j1",{}).get("sign")=="NEGATIVE"
    widths=[]
    for side in (left,right):
        for field in ("energy","j1","fixed_second"):
            if field in side:widths.append(DyadicInterval.from_json(side[field]["dyadic_interval"]).width())
    width_ok=bool(widths) and all(w<=1/(1<<80) for w in widths)
    return {"name":"K2_LOG2_COMPRESSED_SEAM","K":2,"L_exact":"log(2)",
            "vector_exact":"(1,-4,6,-4,1)/sqrt(70)","precision_bits":prec,
            "left":left,"right":right,"value_overlap":overlap("energy"),
            "first_overlap":overlap("j1"),"second_overlap":overlap("fixed_second"),
            "energy_positive":energy_pos,"first_variation_negative":j1_neg,
            "width_le_2^-80":width_ok,
            "qualified":overlap("energy") and overlap("j1") and overlap("fixed_second") and energy_pos and j1_neg and width_ok}


def seam_probe(q:int,K:int,prec:int)->dict:
    L=arb(q).log()
    return {"q":q,"K":K,"precision_bits":prec,
            "left":one_dimensional_calibration(L,K,max(1,q-1),"even",prec),
            "right":one_dimensional_calibration(L,K,q,"even",prec)}


def replay_selected_case(cand:dict,precisions:list[int])->dict:
    Q=int(cand["Q"]);K=int(cand["K"])
    if cand["reason"]=="sign_bracket":
        left=ladder_point(Q,K,precisions,fraction=cand["fraction_left"]);right=ladder_point(Q,K,precisions,fraction=cand["fraction_right"])
        opposite={left["global_sign"],right["global_sign"]}=={"POSITIVE","NEGATIVE"}
        return {"candidate":cand,"kind":"BRACKET","left":left,"right":right,
                "certified_endpoint_opposition":opposite,"first_boundary_claimed":False}
    return {"candidate":cand,"kind":"POINT","point":ladder_point(Q,K,precisions,fraction=cand["cell_fraction"]),
            "first_boundary_claimed":False}


def campaign(protocol:dict)->dict:
    ladder=[int(x) for x in protocol["precision_bits"]];calibration=None
    for prec in ladder:
        calibration=log2_seam_calibration(prec)
        if calibration["qualified"]:break
    seams=[seam_probe(int(x["q"]),int(x["K"]),ladder[-1]) for x in protocol["seam_controls"]]
    selected=[replay_selected_case(c,ladder) for c in protocol["selected_neighborhoods"]]
    balances=[selected_balance(c,ladder[-1]) for c in protocol["selected_neighborhoods"]]
    return {"schema_version":"POST282_CONTACT_BALANCE_ARB_v2","claim_cap":"EXPERIMENTAL_SIGNAL_ONLY",
            "calibration":calibration,"seam_controls":seams,"selected_replay":selected,"balance_rows":balances,
            "hypothesis_dispositions":{
                "X01_INHERITED_RESPONSE_BALANCE":{"status":"NO_CERTIFIED_GENERATED_INHERITED_CONTACT_IN_FROZEN_PANEL",
                    "proxy_rows_evaluated":len(balances),"theorem_promotion":False},
                "X02_PROJECTED_DILATION_RESIDUAL":{"status":"NEAR_CONTACT_TRANSPORT_DEFECT_PANEL_COMPLETED",
                    "rows_evaluated":len(balances),"exact_contact_authority":False,"theorem_promotion":False}},
            "summary":{"calibration_qualified":bool(calibration and calibration["qualified"]),
                "seam_control_count":len(seams),"selected_count":len(selected),
                "selected_sign_bracket_count":sum(1 for r in selected if r["kind"]=="BRACKET"),
                "selected_certified_endpoint_opposition_count":sum(1 for r in selected if r["kind"]=="BRACKET" and r["certified_endpoint_opposition"]),
                "balance_row_count":len(balances),
                "certified_response_count":sum(1 for r in balances if r.get("response",{}).get("status") in {"CERTIFIED_BORDERED_RESPONSE","CERTIFIED_ZERO_COMPLEMENT_RESPONSE"}),
                "Q_representation_overlap_count":sum(1 for r in balances if r.get("Q",{}).get("overlap") is True),
                "independent_physical_remainder_certified_count":0,
                "theorem_promotion":False,"terminal_claim":"RH_OPEN"}}


if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument("--protocol",required=True);ap.add_argument("--output",required=True)
    a=ap.parse_args();out=campaign(json.loads(Path(a.protocol).read_text()))
    Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps(out["summary"],indent=2,sort_keys=True))
