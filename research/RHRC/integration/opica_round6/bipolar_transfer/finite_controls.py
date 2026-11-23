"""Exact finite algebra control; not a Lean compiler or arithmetic asymptotic proof."""
from fractions import Fraction as F
import json
from pathlib import Path
import argparse

def need(ok, msg):
    if not ok:
        raise ArithmeticError(msg)

def cell(e,o,re,ro,t):
    n=e+o
    q=e-o
    s=(e-re)-(o-ro)
    c=(t-re-ro)/2
    a=e-re-c
    b=o-ro-c
    d=n-t
    p=4*max(a,0)*max(-b,0)
    m=4*max(b,0)*max(-a,0)
    u=d*d
    r=2*n*abs(re-ro)
    qp=max(q,0)**2
    qm=max(-q,0)**2
    sp=max(s,0)**2
    sm=max(-s,0)**2
    need(a-b==s and a+b==d,"wrong centre/conservation")
    need(p==max(sp-u,0) and m==max(sm-u,0),"wrong exact opposed identity")
    need(p+m==max(s*s-u,0),"incorrect bipolar discrepancy identity")
    need(abs(qp-sp)<=r and abs(qm-sm)<=r and abs(q*q-s*s)<=r,"removal bound")
    need(p<=qp+r and qp<=p+u+r,"positive bracket")
    need(m<=qm+r and qm<=m+u+r,"negative bracket")
    need(p+m<=q*q+r and q*q<=p+m+u+r,"single-remainder combined bracket")
    need(q*q==qp+qm,"square split")
    return {"raw":q*q,"positive":qp,"negative":qm,"paired":p+m,"unsigned":u,"removal":r}

def replay():
    count=0
    unsigned_necessary=None
    removal_necessary=None
    sign_flip=None
    for e in range(9):
        for o in range(9):
            for re in range(e+1):
                for ro in range(o+1):
                    for k in range(25):
                        z=cell(e,o,re,ro,F(k,2));count+=1
                        if unsigned_necessary is None and z["raw"]>z["paired"]+z["removal"]:
                            unsigned_necessary=[e,o,re,ro,k]
                        if removal_necessary is None and z["raw"]>z["paired"]+z["unsigned"]:
                            removal_necessary=[e,o,re,ro,k]
                        if sign_flip is None and (e-o)*((e-re)-(o-ro))<0:
                            sign_flip=[e,o,re,ro,k]
    need(count==50625 and unsigned_necessary is not None and removal_necessary is not None and sign_flip is not None,
         "incomplete finite control census")
    # Counterexample to adding arbitrary cofinal estimates on different subsequences:
    # f(n)=n on odd n, 0 on even n, g(n)=n-f(n). Each has zeros arbitrarily far out;
    # f+g=n cannot satisfy a square-root upper bound with fixed C on arbitrarily large n.
    # The proof of the latter is on paper (n > C^2); this finite replay checks the construction.
    for n in range(64,4097):
        f=n if n%2 else 0;g=n-f
        need(f+g==n and min(f,g)==0,"invalid disjoint witness construction")
    return {"schema":"OPICA_BIPOLAR_FINITE_CONTROLS_V1","status":"EXACT_FINITE_ALGEBRA_REPLAY_PASS",
            "tested_cells":count,"target_population_grid":"k/2 for k=0..24",
            "unsigned_error_necessary_example":unsigned_necessary,
            "removal_error_necessary_example":removal_necessary,
            "sign_flip_example":sign_flip,
            "different_cofinal_witnesses":"NOT_A_VALID_SUM_RULE; f+g=n",
            "proof_acceptance":False,"RH":"OPEN","C1":"OPEN","Step4":"OPEN"}

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--output",required=True,type=Path);a=p.parse_args()
    need(not a.output.exists(),"refuse stale output");a.output.parent.mkdir(parents=True,exist_ok=True)
    result=replay();a.output.write_text(json.dumps(result,indent=2)+"\n");print(json.dumps(result))
