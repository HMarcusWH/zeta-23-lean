"""Non-interval-certified numerical consistency tests for OPICA Round 2.

Generic nonzero zeta arguments are deliberately used for the finite-window
Green identity: the omitted exterior boundary is retained. No hypothetical
zeta zero, infinite limit or universal estimate is certified by this script.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import platform
from pathlib import Path
import mpmath as mp

mp.mp.dps = 50

def st(x: mp.mpf, rho: mp.mpc):
    n = int(mp.floor(x))
    if n == 0:
        return mp.mpc(0), mp.mpc(0)
    a = mp.fsum(mp.power(j, rho-1) for j in range(1,n+1))
    b = mp.fsum(mp.power(j, -rho) for j in range(1,n+1))
    s = mp.power(x,-rho)*a - mp.power(x,rho-1)*b
    ds = -rho*mp.power(x,-rho-1)*a - (rho-1)*mp.power(x,rho-2)*b
    return s, ds

def hval(x, rho):
    if x == 0:
        return mp.mpc(1), mp.mpc(0)
    b = 1/rho-1/(1-rho)
    s, ds = st(x,rho)
    return 1-s/b, -ds/b

def piecewise(fun, endpoint):
    endpoints = [mp.mpf(0)] + [mp.mpf(n) for n in range(1,int(mp.floor(endpoint))+1)]
    if endpoints[-1] != endpoint:
        endpoints.append(endpoint)
    return mp.fsum(mp.quad(fun,[a,b]) for a,b in zip(endpoints,endpoints[1:]))

def fmt(z):
    if isinstance(z,mp.mpc):
        return {'re':mp.nstr(z.real,35),'im':mp.nstr(z.imag,35)}
    return mp.nstr(z,35)

def main(output):
    tests=[]
    for re, im, end in [('0.7','2','6.25'),('0.5','4','7.3'),('0.25','7','5.4')]:
        rho=mp.mpc(re,im); k=rho*(1-rho); R=mp.mpf(end)
        N=piecewise(lambda x: abs(hval(x,rho)[0])**2,R)
        E=piecewise(lambda x: x*x*abs(hval(x,rho)[1])**2,R)
        I=piecewise(lambda x: mp.conj(hval(x,rho)[0]),R)
        S=mp.fsum(mp.conj(hval(mp.mpf(n),rho)[0]) for n in range(1,int(mp.floor(R))+1))
        h,dh=hval(R,rho)
        boundary=R*R*dh*mp.conj(h)
        lhs=E-boundary; rhs=k*(N-I+S)
        error=abs(lhs-rhs); scaled=error/(1+abs(lhs)+abs(rhs))
        if scaled > mp.mpf('1e-38'):
            raise RuntimeError(f'Finite Green mismatch {rho}: {scaled}')
        tests.append({'test':'finite_Green_with_boundary','rho':fmt(rho),'R':fmt(R),
            'absolute_error':fmt(error),'scaled_error':fmt(scaled),'boundary':fmt(boundary),
            'boundary_free_mismatch':fmt(abs(E-rhs))})
    # Euler--Maclaurin expansion: compare the finite definition through Hurwitz
    # recurrence. These arguments are not zeta zeros; retain both zeta terms.
    for re,im in [('0.7','2'),('0.5','4'),('0.25','7')]:
        rho=mp.mpc(re,im); b=1/rho-1/(1-rho)
        rows=[]
        for size in [100,200,400,800]:
            x=mp.mpf(size)+mp.mpf('0.37'); n=int(mp.floor(x)); u=x-n
            a=mp.zeta(1-rho)-mp.zeta(1-rho,n+1)
            c=mp.zeta(rho)-mp.zeta(rho,n+1)
            actual=x**(-rho)*a-x**(rho-1)*c
            B2=u*u-u+mp.mpf(1)/6
            model=b+mp.zeta(1-rho)*x**(-rho)-mp.zeta(rho)*x**(rho-1)+(2*rho-1)*B2/(2*x*x)
            error=abs(actual-model)
            rows.append({'x':fmt(x),'error':fmt(error),'scaled_x_cubed':fmt(error*x**3)})
        scaled_values=[mp.mpf(row['scaled_x_cubed']) for row in rows]
        if max(scaled_values)>mp.mpf(100) or min(scaled_values)<=0:
            raise RuntimeError('Unexpected EM consistency profile')
        tests.append({'test':'finite_sum_EM_consistency','rho':fmt(rho),'rows':rows,
                      'scope':'finite sample; not a certified asymptotic bound'})
    for delta in ['-0.4','0','0.25']:
        for gamma in [16,20,40]:
            lam=mp.mpc(delta,gamma)
            margins=[]
            for i in range(17):
                u=(4*mp.pi/(3*gamma)) + i*(mp.pi/(3*gamma))/16
                density=mp.re(mp.exp(-u/2)*(mp.mpf('0.25')-lam*lam)/lam*mp.sinh(lam*u))
                target=-mp.mpf(gamma)/2*mp.exp(-u/2)
                margins.append(target-density)
            if min(margins)<=0:
                raise RuntimeError('Negative interval consistency failure')
            tests.append({'test':'explicit_negative_interval_samples','delta':delta,'gamma':gamma,
                          'sample_count':17,'min_margin':fmt(min(margins)),
                          'scope':'synthetic parameters; not a hypothetical zero computation'})
    rec={'status':'PASS_NUMERICAL_CONSISTENCY_NOT_INTERVAL_CERTIFIED',
         'python':platform.python_version(),'mpmath':mp.__version__,'decimal_precision':mp.mp.dps,
         'cases':len(tests),'controls':tests,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'infinite_theorem_certification':False,'new_Lean_roots':0,'independent_review':False}
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps(rec,indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True,type=Path)
    main(ap.parse_args().output)
