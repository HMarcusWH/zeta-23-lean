#!/usr/bin/env python3
"""Numerical consistency of the log-Mellin force and resolvent; not interval certified."""
from __future__ import annotations
import mpmath as mp, json, argparse, hashlib
from pathlib import Path
mp.mp.dps=45

def power_integral(a,lo,hi):
    q=a+1
    return (mp.power(hi,q)-mp.power(lo,q))/q

def finite_resolvent_transform(rho,xi,N):
    b=1/rho-1/(1-rho); zz=mp.zeta(rho)
    # (0,1): exact L2 solution, not a gapped source when zeta(rho) != 0.
    ans=1/(mp.mpf('.5')-mp.j*xi) - (zz/b)/(rho-mp.mpf('.5')-mp.j*xi)
    A=mp.mpc(0);B=mp.mpc(0)
    for n in range(1,N):
        A+=mp.power(n,rho-1);B+=mp.power(n,-rho)
        ans+=power_integral(-mp.mpf('.5')-mp.j*xi,n,n+1)
        ans-=A/b*power_integral(-rho-mp.mpf('.5')-mp.j*xi,n,n+1)
        ans+=(B-zz)/b*power_integral(rho-mp.mpf('1.5')-mp.j*xi,n,n+1)
    # Retain the leading tail, rather than truncating a slowly decaying profile.
    D=-mp.zeta(1-rho)/b
    tail=D*mp.power(N,mp.mpf('.5')-rho-mp.j*xi)/(rho-mp.mpf('.5')+mp.j*xi)
    return ans+tail

def run():
    rows=[]
    for rr,ii,xi in [('0.7','2','0'),('0.75','3','1.25'),('0.8','1.5','-0.75'),('0.65','4','2')]:
        rho=mp.mpc(rr,ii);xi=mp.mpf(xi);k=rho*(1-rho)
        target=k*mp.zeta(mp.mpf('.5')+mp.j*xi)/(xi*xi+mp.mpf('.25')-k)
        errs=[]
        for N in [400,1600]:
            approx=finite_resolvent_transform(rho,xi,N)
            err=abs(approx-target);errs.append(err)
            if err>mp.mpf('2e-5'): raise RuntimeError((rho,xi,N,err))
            rows.append({'test':'physical_resolvent_log_transform','rho':str(rho),'xi':str(xi),'N':N,'absolute_error':mp.nstr(err,18),'generic_nonzero_zeta_argument':True})
        if errs[1]>=errs[0]: raise RuntimeError('tail control did not improve')
    C0=mp.log(2*mp.pi)-mp.euler
    for N in [2,10,100,1000]:
        finite=2*N-mp.harmonic(N)-2*(N-1)*mp.log(N)+2*mp.loggamma(N)
        difference=C0-finite
        if not 0<difference<mp.mpf(1)/N:raise RuntimeError('sawtooth norm tail')
        rows.append({'test':'sawtooth_norm_exact_partial_sum','N':N,'remaining_integral':mp.nstr(difference,18),'elementary_tail_upper':str(mp.mpf(1)/N)})
    return rows
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 rows=run();out={'status':'PASS_NUMERICAL_CONSISTENCY_ONLY','cases':len(rows),'controls':rows,'mpmath':mp.__version__,'dps':mp.mp.dps,'interval_certified':False,'actual_zeta_zeros_used':False,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
 a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
