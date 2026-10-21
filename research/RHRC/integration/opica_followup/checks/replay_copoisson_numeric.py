#!/usr/bin/env python3
"""Numerical cross-representation control only. Not interval-certified or a zero test."""
from pathlib import Path
from hashlib import sha256
import json, platform
import mpmath as mp
mp.mp.dps=40
ROOT=Path(__file__).resolve().parents[1]
rows=[]
for rho in (mp.mpc('0.25'),mp.mpc('0.75','0.8'),mp.mpc('0.65','10')):
    for b in (mp.mpf('0.5'),mp.mpf('2')):
        # Rapidly convergent renormalized-comb pairing on Gaussian exp(-pi*b*x^2).
        def heat_integrand(t):
            u=mp.exp(t)
            a=sum(mp.exp(-mp.pi*b*u*u*n*n) for n in range(1,13))
            c=sum(mp.exp(-mp.pi*u*u*n*n/b) for n in range(1,13))
            return 2*mp.exp((1-rho)*t)*(a+c/mp.sqrt(b))
        direct=mp.quad(heat_integrand,[0,mp.mpf('0.5'),1,mp.log(10)])
        integral=mp.mpc(0)
        for n in range(1,10):
            A=sum(mp.power(k,rho-1) for k in range(1,n+1))
            B=sum(mp.power(k,-rho) for k in range(1,n+1))
            integral+=mp.quad(lambda x:(mp.power(x,-rho)*A-mp.power(x,rho-1)*B)*mp.exp(-mp.pi*b*x*x),[n,n+1])
        density=1/rho+1/((1-rho)*mp.sqrt(b))+mp.zeta(rho)*mp.gamma(rho/2)*mp.power(mp.pi*b,-rho/2)+2*integral
        error=abs(direct-density)
        if error>mp.mpf('1e-25'):
            raise RuntimeError(f'cross-representation discrepancy {rho} {b}: {error}')
        rows.append({'rho':str(rho),'gaussian_b':str(b),'absolute_difference':mp.nstr(error,12),'comparison_pass':True})
result={'status':'PASS_NUMERICAL_CONSISTENCY_ONLY','python':platform.python_version(),'mpmath':mp.__version__,'precision_decimal':mp.mp.dps,'cases':rows,'interval_certified':False,'hypothetical_zeta_zeros_evaluated':False,'full_analytic_proof':False,'scope':'Gaussian-test comparison of renormalized lattice integral with explicit density+atom formula at six NONZERO generic zeta arguments. Truncations are numerical controls, not rigorous remainder certificates.','script_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'receipts/copoisson_numeric.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
