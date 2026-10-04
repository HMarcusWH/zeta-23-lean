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
from flint import acb, arb, arb_mat, ctx

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
    direct_arch_component_second,
    pole_component_second,
    prime_component_second,
    fixed_unit_primitive_second_derivative_caches,
)
from post177_fb05_q13_fixed_unit_derivative import (
    direct_arch_component_prime,
    pole_component_prime,
    prime_component_prime,
    fixed_unit_primitive_derivative_caches,
)
from certify_post281_generated_contact_frontier import ladder_point
import post280_saturation_frontier as floating
import canonical_source_arb as canonical_arb


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


def simple_ground_bundle_from_jets(H:arb_mat,Hp:arb_mat,Hpp:arb_mat)->dict:
    """Certify an isolated ground state for an already matched jet triple."""
    try:
        eigs=_eigs(H)
    except ValueError as exc:
        return {"status":"EIGENSOLVER_UNRESOLVED","error":str(exc)}
    d=H.nrows()
    if d==0:return {"status":"ZERO_DIMENSIONAL_CARRIER"}
    Hmid=_mid_matrix(H);_,vecs=np.linalg.eigh((Hmid+Hmid.T)/2)
    v0=np.asarray(vecs[:,0],dtype=float);v0/=np.linalg.norm(v0)
    V0=_arb_col(v0);theta=_quad_quotient(H,V0)
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
        if bool(angle>1):angle=arb(1)
        status="SIMPLE_GROUND_RESOLVED"
    V=_vec_ball(v0,angle);j1=_quad_quotient(Hp,V);fixed2=_quad_quotient(Hpp,V)
    return {"status":status,"H":H,"Hp":Hp,"Hpp":Hpp,"eigs":eigs,"v0":v0,
            "V":V,"angle":angle,"lambda":eigs[0],"gap":gap,"j1":j1,"fixed2":fixed2,
            "record":{"status":status,"lambda":_ball_record_full(eigs[0]),
                      "j1":_ball_record_full(j1),
                      "fixed_second":_ball_record_full(fixed2),"dimension":d}}

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



I=acb(0,1)

def _source_matrix_omega_acb(omega:acb,K:int):
    ns=list(range(-K,K+1));pi=acb(arb.pi())
    A=[[acb(0) for _ in ns] for _ in ns]
    for i,n in enumerate(ns):
        for j,m in enumerate(ns):
            if n==m:
                A[i][j]=2*omega*(2*pi*n*omega).cos()
            else:
                A[i][j]=((2*pi*n*omega).sin()-(2*pi*m*omega).sin())/(pi*(n-m))
    return A

def _source_matrix_omega_derivative_acb(omega:acb,K:int):
    ns=list(range(-K,K+1));pi=acb(arb.pi())
    A=[[acb(0) for _ in ns] for _ in ns]
    for i,n in enumerate(ns):
        for j,m in enumerate(ns):
            if n==m:
                u=2*pi*n*omega
                A[i][j]=2*u.cos()-4*pi*n*omega*u.sin()
            else:
                A[i][j]=2*(n*(2*pi*n*omega).cos()-m*(2*pi*m*omega).cos())/(n-m)
    return A

def _source_matrix_one_sub_over_t_acb(t:acb,L:arb,K:int):
    """(sourceMatrix(1-t/L)-2I)/t in removable form."""
    ns=list(range(-K,K+1));pi=acb(arb.pi());Lc=acb(L)
    B=[[acb(0) for _ in ns] for _ in ns]
    for i,n in enumerate(ns):
        cn=2*pi*n/Lc
        for j,m in enumerate(ns):
            cm=2*pi*m/Lc
            if n==m:
                h=cn*t/2
                B[i][j]=-(cn*cn)*t*(h.sinc()**2)-2*(cn*t).cos()/Lc
            else:
                B[i][j]=(cn*(cn*t).sinc()-cm*(cm*t).sinc())/(pi*(m-n))
    return B

def _mat_vec_acb(A,x):
    out=[acb(0) for _ in range(len(A))]
    for i in range(len(A)):
        for j in range(len(A)):
            out[i]+=A[i][j]*acb(x[j,0])
    return out

def _bilinear_acb(x,A,y):
    Ay=_mat_vec_acb(A,y);s=acb(0)
    for i in range(len(Ay)): s+=acb(x[i,0])*Ay[i]
    return s

def _ambient_contact_vectors(K:int,bundle:dict,response:dict):
    U=_orthonormal_full_basis(K,"even")
    return U*bundle["V"],U*response["W"]

def _quadratic_normal_vector(K:int):
    ns=list(range(-K,K+1));mean=arb(sum(n*n for n in ns))/arb(len(ns))
    v=arb_mat([[arb(n*n)-mean] for n in ns]);den=(v.transpose()*v)[0,0]
    return v,den

def _m4(K:int,z:arb_mat)->arb:
    return sum((arb(n**4)*z[i,0] for i,n in enumerate(range(-K,K+1))),arb(0))

def _remainder_over_t_acb(t:acb,L:arb,K:int,z:arb_mat,w:arb_mat):
    """R(t)/t in a removable form valid at t=0."""
    ns=list(range(-K,K+1));a2=acb((2*arb.pi())**2);Lc=acb(L)
    normal,den=_quadratic_normal_vector(K);m4=acb(_m4(K,z))
    B=_source_matrix_one_sub_over_t_acb(t,L,K)
    n_over_t=m4*_bilinear_acb(normal,B,z)/acb(den)
    omega=acb(1)-t/Lc
    A=_source_matrix_omega_acb(omega,K)
    Ap=_source_matrix_omega_derivative_acb(omega,K)
    Dz=arb_mat([[arb(n)*z[i,0]] for i,n in enumerate(ns)])
    d=_bilinear_acb(Dz,A,Dz);mixed=_bilinear_acb(z,Ap,w)
    return a2/(Lc*Lc)*n_over_t-a2*t/(Lc**4)*d+2/(Lc*Lc)*mixed

def _production_kernel_integrand_acb(t:acb,L:arb,K:int,z:arb_mat,w:arb_mat):
    r_over_t=_remainder_over_t_acb(t,L,K,z,w)
    pole=(-t/2).exp()+(t/2).exp()
    reg=(t/2).exp()/(2*(I*t).sinc())
    return t*r_over_t*pole-r_over_t*reg

def direct_physical_remainder_certificate(L:arb,K:int,Q:int,bundle:dict,response:dict)->dict:
    if response.get("status") not in {"CERTIFIED_BORDERED_RESPONSE","CERTIFIED_ZERO_COMPLEMENT_RESPONSE"}:
        return {"status":"RESPONSE_UNRESOLVED"}
    z,w=_ambient_contact_vectors(K,bundle,response)
    try:
        integral=acb.integral(
            lambda t,_analytic:_production_kernel_integrand_acb(t,L,K,z,w),
            acb(0),acb(L),abs_tol=arb(2)**(-120),eval_limit=200000,depth_limit=40)
        if not integral.imag.contains(0):
            return {"status":"NONREAL_INTEGRAL_ENCLOSURE","integral":str(integral)}
        prime=acb(0)
        for q in range(2,Q+1):
            vm=canonical_arb.von_mangoldt(q)
            if vm.is_zero(): continue
            t=acb(arb(q).log())
            prime+=acb(vm/arb(q).sqrt())*(t*_remainder_over_t_acb(t,L,K,z,w))
        value=integral-prime
        if not value.imag.contains(0):
            return {"status":"NONREAL_RHS_ENCLOSURE","value":str(value)}
        R=value.real
        return {"status":"CERTIFIED","production_remainder":interval_record(R),
                "integral":interval_record(integral.real),
                "prime_sum":interval_record(prime.real),"_R":R}
    except Exception as exc:
        return {"status":"DIRECT_PHYSICAL_INTEGRAL_UNRESOLVED","error":str(exc)}

def saturation_certificate(L:arb,qrep:dict,curv:dict,remainder:dict,bundle:dict)->dict:
    if remainder.get("status")!="CERTIFIED" or "_q_arith" not in qrep or "_kappa" not in curv:
        return {"status":"UNRESOLVED"}
    scale=(2*arb.pi())**2/(L*L)
    delta=remainder["_R"]-scale*qrep["_q_arith"]
    rhs=curv["_kappa"]+2*bundle["j1"]/L
    out={"status":"CERTIFIED_INDEPENDENT_SIDES",
         "delta_sat":interval_record(delta),"kappa_plus_euler":interval_record(rhs),
         "identity_overlap":_interval_overlap(delta,rhs)}
    if bool(qrep["_q_arith"]>0):
        out["rho"]={"status":"ELIGIBLE",
                    "value":interval_record(L*L*remainder["_R"]/((2*arb.pi())**2*qrep["_q_arith"]))}
    else:
        out["rho"]={"status":"INELIGIBLE_Q_NOT_CERTIFIED_POSITIVE"}
    return out


def direct_signed_channel_jets(L:arb,K:int,Q:int)->dict:
    """Rigorous value/first/second jets for the three signed production channels."""
    ns=list(range(-K,K+1));dim=len(ns)
    vals={
        "alpha":{n:canonical_arb.alpha_L(n,L) for n in ns},
        "beta":{n:canonical_arb.beta_L(n,L) for n in ns},
        "gamma":{n:canonical_arb.source_eq44_gamma_L(n,L) for n in ns},
    }
    d1=fixed_unit_primitive_derivative_caches(L,K)
    d2=fixed_unit_primitive_second_derivative_caches(L,K)
    out={}
    for name in ("POLE","ARCH","PRIME"):
        A=arb_mat(dim,dim);Ap=arb_mat(dim,dim);App=arb_mat(dim,dim)
        for i,n in enumerate(ns):
            for j,m in enumerate(ns):
                if name=="POLE":
                    a=canonical_arb.pole_component(n,m,L)
                    ap=pole_component_prime(n,m,L)
                    app=pole_component_second(n,m,L)
                elif name=="ARCH":
                    a=-canonical_arb.direct_arch_component(
                        n,m,L,vals["alpha"],vals["beta"],vals["gamma"])
                    ap=-direct_arch_component_prime(
                        n,m,d1["alpha"],d1["beta"],d1["gamma"])
                    app=-direct_arch_component_second(
                        n,m,d2["alpha"],d2["beta"],d2["gamma"])
                else:
                    a=-canonical_arb.prime_component(n,m,L,Q)
                    ap=-prime_component_prime(n,m,L,Q)
                    app=-prime_component_second(n,m,L,Q)
                A[i,j]=a;Ap[i,j]=ap;App[i,j]=app
        out[name]=(A,Ap,App)
    return out

def matched_ablation_records(L:arb,K:int,Q:int,bundle:dict,response:dict)->list[dict]:
    """Channel deletions with frozen-state and reoptimized operator states kept distinct."""
    if response.get("status") not in {"CERTIFIED_BORDERED_RESPONSE","CERTIFIED_ZERO_COMPLEMENT_RESPONSE"}:
        return [{"name":"ALL","status":"RESPONSE_UNRESOLVED"}]
    U=_orthonormal_full_basis(K,"even");V=bundle["V"];W=response["W"]
    channels=direct_signed_channel_jets(L,K,Q);out=[]
    for name,(A,Ap,App) in channels.items():
        C=U.transpose()*A*U;Cp=U.transpose()*Ap*U;Cpp=U.transpose()*App*U
        Halt=bundle["H"]-C;Hpalt=bundle["Hp"]-Cp;Hppalt=bundle["Hpp"]-Cpp
        frozen_kappa=(V.transpose()*Hppalt*V)[0,0]/(V.transpose()*V)[0,0]+2*(V.transpose()*Hpalt*W)[0,0]
        out.append({"name":"DROP_"+name,"mode":"FROZEN_STATE",
                    "status":"CERTIFIED_MATCHED_OPERATOR_JETS",
                    "optimized_curvature":interval_record(frozen_kappa),
                    "arithmetic_comparison":{"status":"NOT_APPLICABLE_NO_MATCHED_PHYSICAL_FUNCTIONAL"},
                    "complete_model_inverse_used":True})
        alt=simple_ground_bundle_from_jets(Halt,Hpalt,Hppalt)
        alt_pub={"name":"DROP_"+name,"mode":"REOPTIMIZED",
                 "ground":alt.get("record",{"status":alt.get("status")}),
                 "arithmetic_comparison":{"status":"NOT_APPLICABLE_NO_MATCHED_PHYSICAL_FUNCTIONAL"}}
        if "H" in alt:
            ar=validated_bordered_response(alt);ac=curvature_enclosure(alt,ar)
            alt_pub["response"]={k:v for k,v in ar.items() if k!="W"}
            alt_pub["curvature"]={k:v for k,v in ac.items() if not k.startswith("_")}
            alt_pub["status"]="REOPTIMIZED_OPERATOR_CERTIFIED" if ac.get("status")=="CERTIFIED_FROM_JETS_AND_RESPONSE" else "REOPTIMIZED_RESPONSE_UNRESOLVED"
        else:
            alt_pub["status"]="REOPTIMIZED_GROUND_UNRESOLVED"
        out.append(alt_pub)
    return out

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
    remainder=direct_physical_remainder_certificate(L,K,Q,bundle,response)
    saturation=saturation_certificate(L,qrep,curv,remainder,bundle)
    public.update({"response":{k:v for k,v in response.items() if k!="W"},
        "Q":{k:v for k,v in qrep.items() if not k.startswith("_")},
        "curvature":{k:v for k,v in curv.items() if not k.startswith("_")},
        "projected_dilation":defect,
        "physical_remainder":{k:v for k,v in remainder.items() if not k.startswith("_")},
        "saturation_gap":saturation,
        "rho":saturation.get("rho",{"status":"UNRESOLVED"}),
        "matched_ablations":matched_ablation_records(L,K,Q,bundle,response),
        "certification_contract":{
            "shifted_eigenvalue_subtraction":True,
            "euler_correction_in_balance":True,
            "response_gauge":"ORTHOGONAL_TO_CERTIFIED_GROUND",
            "independent_physical_remainder":True,
            "midpoint_inverse_requires_rho_lt_one":True,
            "exact_interval_codec":"DYADIC_DIRECTED_ARB_ENDPOINTS",
            "theorem_promotion":False}})
    try:
        frow=floating.evaluate(float(L.mid()),K)
        public["floating_crosscheck"]={k:frow.get(k) for k in (
            "Q_arithmetic","Q_spectral_reduced","production_arithmetic_remainder",
            "production_remainder_integral_error_estimate","delta_sat_proxy",
            "kappa_fd","delta_minus_kappa_fd")}
        public["floating_crosscheck"]["certificate_authority"]=False
    except Exception as exc:
        public["floating_crosscheck"]={"status":"ERROR","error":str(exc),"certificate_authority":False}
    public["status"]=("CERTIFIED_RESPONSE_Q_REMAINDER_BALANCE"
        if remainder.get("status")=="CERTIFIED" and saturation.get("status")=="CERTIFIED_INDEPENDENT_SIDES"
        else "PARTIALLY_CERTIFIED_SPECTRAL_RESPONSE_Q")
    return public


def one_dimensional_calibration(L:arb,K:int,Q:int,parity:str,prec:int)->dict:
    bundle=simple_ground_bundle(L,K,Q,parity,prec)
    if "H" not in bundle:return {"status":bundle.get("status","UNRESOLVED")}
    response=validated_bordered_response(bundle);curvature=curvature_enclosure(bundle,response)
    return {"status":"CERTIFIED_ONE_DIMENSIONAL_DIRECTION" if bundle["H"].nrows()==1 else "NOT_ONE_DIMENSIONAL",
            "dimension":bundle["H"].nrows(),"energy":interval_record(bundle["lambda"]),
            "j1":interval_record(bundle["j1"]),"fixed_second":interval_record(bundle["fixed2"]),
            "response":{k:v for k,v in response.items() if k!="W"},
            "optimized_curvature":curvature.get("optimized_curvature")}


def _calibration_balance_side(L:arb,Q:int,prec:int)->dict:
    """Independent derivative/remainder/balance certificate on the K=2 seam carrier."""
    bundle=simple_ground_bundle(L,2,Q,"even",prec)
    if "H" not in bundle:
        return {"status":"GROUND_UNRESOLVED","ground":bundle.get("record",{"status":bundle.get("status")})}
    response=validated_bordered_response(bundle)
    qrep=q_representations(L,2,Q,bundle)
    curv=curvature_enclosure(bundle,response)
    remainder=direct_physical_remainder_certificate(L,2,Q,bundle,response)
    saturation=saturation_certificate(L,qrep,curv,remainder,bundle)
    return {
        "status":"CALIBRATION_CERTIFIED" if (
            response.get("status") in {"CERTIFIED_BORDERED_RESPONSE","CERTIFIED_ZERO_COMPLEMENT_RESPONSE"}
            and remainder.get("status")=="CERTIFIED"
            and saturation.get("status")=="CERTIFIED_INDEPENDENT_SIDES"
        ) else "CALIBRATION_UNRESOLVED",
        "derivative":interval_record(bundle["j1"]),
        "fixed_second":interval_record(bundle["fixed2"]),
        "remainder":remainder.get("production_remainder"),
        "balance_delta":saturation.get("delta_sat"),
        "balance_rhs":saturation.get("kappa_plus_euler"),
        "identity_overlap":saturation.get("identity_overlap"),
        "response_status":response.get("status"),
    }


def _interval_width(record:dict|None):
    if not isinstance(record,dict) or "dyadic_interval" not in record:
        return None
    return DyadicInterval.from_json(record["dyadic_interval"]).width()


def log2_seam_calibration(prec:int)->dict:
    ctx.prec=int(prec);L=arb(2).log()
    left=one_dimensional_calibration(L,2,1,"even",prec)
    right=one_dimensional_calibration(L,2,2,"even",prec)
    left_balance=_calibration_balance_side(L,1,prec)
    right_balance=_calibration_balance_side(L,2,prec)
    def overlap(field):
        if field not in left or field not in right:return False
        a=DyadicInterval.from_json(left[field]["dyadic_interval"])
        b=DyadicInterval.from_json(right[field]["dyadic_interval"])
        return not (a.hi<b.lo or b.hi<a.lo)
    def balance_overlap(field):
        a=left_balance.get(field);b=right_balance.get(field)
        if not isinstance(a,dict) or not isinstance(b,dict):return False
        aa=DyadicInterval.from_json(a["dyadic_interval"])
        bb=DyadicInterval.from_json(b["dyadic_interval"])
        return not (aa.hi<bb.lo or bb.hi<aa.lo)
    energy_pos=left.get("energy",{}).get("sign")=="POSITIVE" and right.get("energy",{}).get("sign")=="POSITIVE"
    j1_neg=left.get("j1",{}).get("sign")=="NEGATIVE" and right.get("j1",{}).get("sign")=="NEGATIVE"
    derivative_widths=[_interval_width(left_balance.get("derivative")),
                       _interval_width(right_balance.get("derivative"))]
    remainder_widths=[_interval_width(left_balance.get("remainder")),
                      _interval_width(right_balance.get("remainder"))]
    balance_widths=[_interval_width(left_balance.get("balance_delta")),
                    _interval_width(right_balance.get("balance_delta")),
                    _interval_width(left_balance.get("balance_rhs")),
                    _interval_width(right_balance.get("balance_rhs"))]
    limit=1/(1<<80)
    derivative_width_ok=all(w is not None and w<=limit for w in derivative_widths)
    remainder_width_ok=all(w is not None and w<=limit for w in remainder_widths)
    balance_width_ok=all(w is not None and w<=limit for w in balance_widths)
    width_ok=derivative_width_ok and remainder_width_ok and balance_width_ok
    seam_balance_overlap=(
        balance_overlap("derivative")
        and balance_overlap("remainder")
        and balance_overlap("balance_delta")
        and balance_overlap("balance_rhs")
    )
    balance_identity_ok=(
        left_balance.get("identity_overlap") is True
        and right_balance.get("identity_overlap") is True
    )
    return {"name":"K2_LOG2_COMPRESSED_SEAM","K":2,"L_exact":"log(2)",
            "vector_exact":"(1,-4,6,-4,1)/sqrt(70)","precision_bits":prec,
            "left":left,"right":right,
            "left_independent_balance":left_balance,
            "right_independent_balance":right_balance,
            "value_overlap":overlap("energy"),
            "first_overlap":overlap("j1"),"second_overlap":overlap("fixed_second"),
            "derivative_overlap":balance_overlap("derivative"),
            "remainder_overlap":balance_overlap("remainder"),
            "balance_overlap":balance_overlap("balance_delta") and balance_overlap("balance_rhs"),
            "seam_balance_overlap":seam_balance_overlap,
            "independent_balance_identity_overlap":balance_identity_ok,
            "energy_positive":energy_pos,"first_variation_negative":j1_neg,
            "derivative_width_le_2^-80":derivative_width_ok,
            "remainder_width_le_2^-80":remainder_width_ok,
            "balance_width_le_2^-80":balance_width_ok,
            "width_le_2^-80":width_ok,
            "qualified":(
                overlap("energy") and overlap("j1") and overlap("fixed_second")
                and energy_pos and j1_neg and width_ok
                and seam_balance_overlap and balance_identity_ok)}


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


def inherited_response_investigation(protocol:dict,balances:list[dict])->dict:
    """Execute X01 only on rows carrying certified generated inherited-contact metadata."""
    selected=protocol.get("selected_neighborhoods") or []
    eligible=[]
    rejected=[]
    for i,(cand,row) in enumerate(zip(selected,balances)):
        meta=cand.get("generated_contact")
        if not isinstance(meta,dict):
            rejected.append({"row":i,"reason":"NO_GENERATED_CONTACT_METADATA"})
            continue
        n=meta.get("n");k=meta.get("k")
        if not (isinstance(n,int) and not isinstance(n,bool)
                and isinstance(k,int) and not isinstance(k,bool) and n<k):
            rejected.append({"row":i,"reason":"NOT_CERTIFIED_INHERITED_INDEX"})
            continue
        if meta.get("certified") is not True:
            rejected.append({"row":i,"reason":"GENERATED_CONTACT_NOT_CERTIFIED"})
            continue
        if row.get("response",{}).get("status") not in {
            "CERTIFIED_BORDERED_RESPONSE","CERTIFIED_ZERO_COMPLEMENT_RESPONSE"}:
            rejected.append({"row":i,"reason":"RESPONSE_UNRESOLVED"})
            continue
        if row.get("physical_remainder",{}).get("status")!="CERTIFIED":
            rejected.append({"row":i,"reason":"REMAINDER_UNRESOLVED"})
            continue
        eligible.append({
            "row":i,"n":n,"k":k,
            "response_status":row["response"]["status"],
            "saturation_gap":row.get("saturation_gap"),
            "rho":row.get("rho"),
        })
    if not eligible:
        return {
            "status":"NO_ELIGIBLE_INHERITED_CONTACT",
            "eligible_count":0,
            "rows_examined":len(balances),
            "rejections":rejected,
            "theorem_promotion":False,
        }
    return {
        "status":"ELIGIBLE_INHERITED_CONTACTS_EVALUATED",
        "eligible_count":len(eligible),
        "rows_examined":len(balances),
        "eligible_rows":eligible,
        "rejections":rejected,
        "theorem_promotion":False,
    }


def campaign(protocol:dict)->dict:
    ladder=[int(x) for x in protocol["precision_bits"]];calibration=None
    for prec in ladder:
        calibration=log2_seam_calibration(prec)
        if calibration["qualified"]:break
    seams=[seam_probe(int(x["q"]),int(x["K"]),ladder[-1]) for x in protocol["seam_controls"]]
    selected=[replay_selected_case(c,ladder) for c in protocol["selected_neighborhoods"]]
    balances=[selected_balance(c,ladder[-1]) for c in protocol["selected_neighborhoods"]]
    x01=inherited_response_investigation(protocol,balances)
    return {"schema_version":"POST282_CONTACT_BALANCE_ARB_v2","claim_cap":"EXPERIMENTAL_SIGNAL_ONLY",
            "calibration":calibration,"seam_controls":seams,"selected_replay":selected,"balance_rows":balances,
            "hypothesis_dispositions":{
                "X01_INHERITED_RESPONSE_BALANCE":x01,
                "X02_PROJECTED_DILATION_RESIDUAL":{"status":"NEAR_CONTACT_TRANSPORT_DEFECT_PANEL_COMPLETED",
                    "rows_evaluated":len(balances),"exact_contact_authority":False,"theorem_promotion":False}},
            "summary":{"calibration_qualified":bool(calibration and calibration["qualified"]),
                "seam_control_count":len(seams),"selected_count":len(selected),
                "selected_sign_bracket_count":sum(1 for r in selected if r["kind"]=="BRACKET"),
                "selected_certified_endpoint_opposition_count":sum(1 for r in selected if r["kind"]=="BRACKET" and r["certified_endpoint_opposition"]),
                "balance_row_count":len(balances),
                "certified_response_count":sum(1 for r in balances if r.get("response",{}).get("status") in {"CERTIFIED_BORDERED_RESPONSE","CERTIFIED_ZERO_COMPLEMENT_RESPONSE"}),
                "Q_representation_overlap_count":sum(1 for r in balances if r.get("Q",{}).get("overlap") is True),
                "independent_physical_remainder_certified_count":sum(1 for r in balances if r.get("physical_remainder",{}).get("status")=="CERTIFIED"),
                "independent_balance_overlap_count":sum(1 for r in balances if r.get("saturation_gap",{}).get("identity_overlap") is True),
                "x01_eligible_count":x01.get("eligible_count",0),
                "theorem_promotion":False,"terminal_claim":"RH_OPEN"}}


if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument("--protocol",required=True);ap.add_argument("--output",required=True)
    a=ap.parse_args();out=campaign(json.loads(Path(a.protocol).read_text()))
    Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps(out["summary"],indent=2,sort_keys=True))
