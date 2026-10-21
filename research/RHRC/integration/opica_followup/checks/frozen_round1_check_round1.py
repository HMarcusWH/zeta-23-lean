#!/usr/bin/env python3
"""Exact finite regression controls for the beyond-PR paper, not analytic proofs.
Standard library only. Checks remain active under python -O.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from fractions import Fraction as F
from hashlib import sha256
from math import comb, factorial, gcd, isqrt
from pathlib import Path
import argparse, json, platform

COUNTS = Counter()
def check(ok: bool, group: str, detail: str = '') -> None:
    if not ok:
        raise RuntimeError(f'{group}: {detail}')
    COUNTS[group] += 1

def mu(n: int) -> int:
    result, p = 1, 2
    while p*p <= n:
        if n % p == 0:
            n //= p; result *= -1
            if n % p == 0: return 0
        p += 1
    return -result if n > 1 else result

def dl(n: int, k: int) -> int:
    result, p = 1, 2
    while p*p <= n:
        a = 0
        while n % p == 0: n //= p; a += 1
        result *= comb(a+k-1,k-1)
        p += 1
    return result * (k if n > 1 else 1)

def conv(a, b):
    N=len(a)-1; c=[0]*(N+1)
    for i in range(1,N+1):
        if a[i]:
            for j in range(1,N//i+1): c[i*j] += a[i]*b[j]
    return c

def power(a, k):
    e=[0]*len(a); e[1]=1
    for _ in range(k): e=conv(e,a)
    return e

def poly_mul(a,b):
    c=defaultdict(F)
    for i,x in a.items():
        for j,y in b.items(): c[i+j]+=x*y
    return {i:x for i,x in c.items() if x}

def poly_pow(a,k):
    c={0:F(1)}
    for _ in range(k): c=poly_mul(c,a)
    return c

def local_tests():
    # Native-shaped logarithmic derivative, not values of actual zeta at a zero.
    v={0:F(2),1:F(1),2:F(1)}; J={0:F(3),1:F(2),2:F(1)}
    inv={0:F(1,2)}
    for k in range(1,8): inv[k]=-sum(v.get(i,F(0))*inv.get(k-i,F(0)) for i in (1,2))/2
    vp_over_v=poly_mul({0:F(1),1:F(2)},inv)
    for m in range(1,6):
        base={-1:F(m),**vp_over_v}; f=poly_mul({k:-z for k,z in J.items()},base)
        Z={k+m:z for k,z in v.items()}
        residual={0:F(1),**{k:-z for k,z in poly_mul(Z,{0:F(2),1:F(-1)}).items()}}
        for p in range(5):
            for d in range(3):
                for r in range(3):
                    U=poly_mul(poly_pow({0:F(5),1:F(1)},d),poly_pow(residual,r))
                    product=poly_mul(poly_mul(poly_pow(Z,p),U),f)
                    order=min(product); expected=p*m-1
                    check(order==expected,'local_native_shaped_order')
                    leading=-F(m)*J[0]*(v[0]**p)*(F(5)**d)
                    check(product[order]==leading,'local_native_shaped_leading')
                    if order>=0:
                        check(factorial(order)*product[order]==factorial(order)*leading,'jet_normalization')
    # Analytic affine correction CAN cancel the completed observation.
    check(F(1)+F(-1)==0,'raw_jet_cancellation_control')

def rate_controls():
    values=[F(k,3) for k in range(-18,19)]
    for f in values:
        for b in values:
            s=abs(f-b); A=1+f*f; B=1+b*b
            check(A <= B*(1+s)**2,'square_root_log_comparison_forward')
            check(B <= A*(1+s)**2,'square_root_log_comparison_reverse')
    for A in (2,10,100,1000):
        check((A+1)**2-A*A==2*A+1,'energy_error_not_subexponential_fixture')

def arithmetic_controls():
    N=180; mus=[0]+[mu(n) for n in range(1,N+1)]
    for n in range(1,N+1):
        check(sum(mus[d] for d in range(1,n+1) if n%d==0)==(1 if n==1 else 0),'mobius_inverse_coefficients')
    for r in (2,3,4):
        for Q in (1,2,6):
            one=[0]+[int(gcd(n,Q)==1) for n in range(1,N+1)]
            v=[mus[n]*one[n] for n in range(N+1)]
            for Y in (2,5,10):
                lo=[v[n] if n<=Y else 0 for n in range(N+1)]
                hi=[v[n]-lo[n] for n in range(N+1)]
                s=[0]*(N+1)
                for i in range(1,r+1):
                    term=conv(power(lo,i),power(one,i-1)); k=(-1)**(i-1)*comb(r,i)
                    s=[a+k*b for a,b in zip(s,term)]
                c=conv(power(hi,r),power(one,r-1))
                ell=2*r-1
                for n in range(1,N+1):
                    check(v[n]==s[n]+c[n],'literal_dirichlet_partition')
                    check(abs(c[n])<=dl(n,ell),'balanced_coefficient_envelope')
                    check(abs(s[n])<=(2**r-1)*dl(n,ell),'typeI_coefficient_envelope')
                # Discrete rational observations: these are NOT the physical U_j.
                weights=[[F((n*(t+1))%7-3,n+1) for n in range(1,33)] for t in range(3)]
                fvals=[sum(v[n]*w[n-1] for n in range(1,33)) for w in weights]
                svals=[sum(s[n]*w[n-1] for n in range(1,33)) for w in weights]
                bvals=[sum(c[n]*w[n-1] for n in range(1,33)) for w in weights]
                EF=sum(x*x for x in fvals); ES=sum(x*x for x in svals); EB=sum(x*x for x in bvals)
                for B in (1,3,7,11):
                    L=sum(c[d]*c[e]*w[d-1]*w[e-1] for w in weights for d in range(1,33) for e in range(1,33) if max(d,e)//gcd(d,e)<=B)
                    High=sum(c[d]*c[e]*w[d-1]*w[e-1] for w in weights for d in range(1,33) for e in range(1,33) if max(d,e)//gcd(d,e)>B)
                    check(EB==High+L,'exact_mask_partition')
                    check(EF<=2*ES+2*max(High,F(0))+2*abs(L),'native_partition_energy_triage')
                if r==2 and Q==2 and Y==10:
                    check((v[121],s[121],c[121])==(0,-1,1),'repeated_prime_control')

def heat_controls():
    # h(t)=exp(-|t|)-(5/2)exp(-2|t|): origin moment exactly zero.
    I1=F(1,1-F(1,2))+F(1,1+F(1,2))
    I2=F(1,2-F(1,2))+F(1,2+F(1,2))
    check(I1-F(5,2)*I2==0,'noncompact_origin_moment')
    check(1-F(5,2)*F(1,8)*F(5,3)==F(23,48),'positive_gap_density_lower_coefficient')
    # Exact atoms of D_log(r)+D_-log(r)-(sqrt(r)+1/sqrt(r))*D_0.
    for k in range(11,41):
        q=F(k+1,k); r=q*q; a=1/r; R=F(2)
        atoms=defaultdict(F)
        for spacing,mass in ((r,q),(1/r,1/q),(F(1),-(q+1/q))):
            nmax=int(R/spacing)
            for n in range(-nmax,nmax+1): atoms[spacing*n]+=mass
        atoms={x:w for x,w in atoms.items() if w}
        check(atoms.get(F(0),0)==0,'subcritical_gap_zero_origin')
        check(all(abs(x)>=a for x in atoms),'subcritical_gap_support')
        check(all(w>=0 for x,w in atoms.items() if x.denominator!=1),'subcritical_gap_off_lattice_positive')
        check(bool(atoms),'subcritical_gap_nonzero')
        check(sum(abs(w) for w in atoms.values())>=2/q,'normalization_TV_lower')
        tau_pair=2/q*(1-1/r)
        sinc_pair=3/q-2/(q**3)+q-(q+1/q)
        check(tau_pair==sinc_pair,'sinc_triangle_floor_formula_fixture')
        tv1=sum(abs(w) for x,w in atoms.items() if abs(x)<=1)
        check(tau_pair<=(1-a)*tv1,'approximate_gap_pairing_bound_fixture')
    for k in range(13):
        # Second dilation derivative minus (1/4)D0 on a monomial local test.
        check((F(k)+F(1,2))**2-F(1,4)==k*(k+1),'normalized_dilation_distribution_coefficients')

def collision_controls():
    for n in range(2,42):
        h=F(1,n)
        G11=1/(2*(1-h)); G22=1/(2*(1+h)); G12=F(1,2)
        det=G11*G22-G12*G12
        b1=h/(2*(1-h)); b2=-h/(2*(1+h))
        energy=(G22*b1*b1-2*G12*b1*b2+G11*b2*b2)/det
        check(det==h*h/(4*(1-h*h)),'two_zero_gram_determinant')
        check(energy==(2-h*h)/(1-h*h),'coupled_zero_data_cancels_conditioning_blowup')
        check(2<energy<3,'collision_energy_bounded_fixture')

def copoisson_controls():
    # Exact complex-rational coefficients; no hypothetical zeta zero is evaluated.
    def add(z,w): return (z[0]+w[0],z[1]+w[1])
    def neg(z): return (-z[0],-z[1])
    def sub(z,w): return add(z,neg(w))
    def mul(z,w): return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
    def scale(a,z): return (a*z[0],a*z[1])
    def div(z,w):
        den=w[0]*w[0]+w[1]*w[1]
        if den==0: raise RuntimeError('zero complex-rational denominator')
        return ((z[0]*w[0]+z[1]*w[1])/den,(z[1]*w[0]-z[0]*w[1])/den)
    one=(F(1),F(0)); quarter=(F(1,4),F(0))
    for delta in (F(-2,5),F(-1,4),F(0),F(1,4),F(2,5)):
        for gamma in (F(1),F(3),F(7),F(10),F(20),F(-7),F(-10)):
            lam=(delta,gamma); rho=add((F(1,2),F(0)),lam)
            b=sub(div(one,rho),div(one,sub(one,rho)))
            b_formula=div(scale(F(-2),lam),sub(quarter,mul(lam,lam)))
            check(b==b_formula,'copoisson_origin_correction_identity')
            check(sub(sub(div(one,rho),div(one,sub(one,rho))),b)==(0,0),'copoisson_final_origin_zero')
            C=div(sub(quarter,mul(lam,lam)),lam)
            D=delta*delta+gamma*gamma
            check(C==(delta*(F(1,4)/D-1),-gamma*(1+F(1,4)/D)),'copoisson_first_interval_coefficient')
            # At gamma*u=sgn(gamma)*3*pi/2, sinh(lam*u) is -i*sgn(gamma)*cosh(delta*u).
            unit=(F(0),F(-1 if gamma>0 else 1))
            val=mul(C,unit)[0]
            check(val==-abs(gamma)*(1+F(1,4)/D) and val<0,'copoisson_explicit_negative_density_factor')
    # Swapping rho and 1-rho interchanges the two finite sum terms.
    for a in (F(1,3),F(2),F(-5,7)):
        for b in (F(2,9),F(3),F(-8)):
            for u,v in ((F(2),F(3)),(F(-1),F(7)),(F(4,5),F(-3,2))):
                check((a*u-b*v)+(b*v-a*u)==0,'copoisson_reflection_finite_sum_cancellation')

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--output',type=Path,required=True); args=ap.parse_args()
    local_tests(); rate_controls(); arithmetic_controls(); heat_controls(); collision_controls(); copoisson_controls()
    result={'status':'PASS_FINITE_EXACT_CONTROLS_ONLY','python':platform.python_version(),'optimized':not __debug__,'checks':dict(COUNTS),'total_checks':sum(COUNTS.values()),'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'infinite_analytic_proof':False,'native_zeta_zeros_computed':False,'lean_compiled':False,'native_source_simulated':False,'scope':'Algebraic identities and rational fixtures only; universal arguments are in the paper.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result,indent=2))
if __name__=='__main__': main()
