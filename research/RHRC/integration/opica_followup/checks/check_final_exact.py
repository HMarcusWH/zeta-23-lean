#!/usr/bin/env python3
"""Exact finite tests for the final paper. No analytic/zero-location authority."""
from __future__ import annotations
import argparse, json, hashlib, platform
from collections import Counter
from fractions import Fraction as F
from pathlib import Path
import sympy as s
COUNTS=Counter()
def check(value, group):
    if not bool(value): raise RuntimeError(group)
    COUNTS[group]+=1

def run():
    x, rho, A, B, z, c = s.symbols('x rho A B z c', nonzero=True)
    kap=rho*(1-rho); b=(1-2*rho)/kap
    hh=1-(A*x**(-rho)-B*x**(rho-1))/b-c*x**(rho-1)
    L=lambda f: -s.diff(x*x*s.diff(f,x),x)
    check(s.simplify(L(hh)-kap*(hh-1))==0, 'corrected_resolvent_cell_equation')
    check(s.simplify(L(x**(rho-1))-kap*x**(rho-1))==0,'homogeneous_tail_subtraction')
    t,n=s.symbols('t n', real=True)
    w=s.exp(t/2)-n*s.exp(-t/2)
    check(s.simplify(-s.diff(w,t)-w/2+s.exp(t/2))==0,'sawtooth_force_between_jumps')
    check(s.simplify((rho-1)*rho+kap)==0,'spectral_coordinate_exact')
    check(s.simplify((s.Rational(1,2)-rho)**2-(s.Rational(1,4)-kap))==0,'spectral_shift_exact')
    # Integer-log telescoping proves the partial sawtooth squared norm formula.
    for N in range(1,301):
        left=Counter()
        for k in range(1,N):
            left[k+1]+=k
            left[k]-=k
        right=Counter({N:N-1})
        for k in range(1,N): right[k]-=1
        left.pop(1,None);right.pop(1,None)
        check(all(left[k]==right[k] for k in set(left)|set(right)), 'log_telescoping_exact')
        harmonic=sum((F(1,k) for k in range(1,N+1)),F(0))
        rational=F(1)+sum((F(1)+F(k,k+1) for k in range(1,N)),F(0))
        check(rational==2*N-harmonic,'sawtooth_partial_norm_rational_part')
    # Positive spectral fixtures. The frequencies and parameters are NOT zeta zeros.
    for massscale in (1,2,5):
      aa=[s.Rational(1,4),s.Rational(5,4),s.Rational(17,4)]
      ww=[s.Rational(massscale,2),s.Rational(2,3),s.Rational(1,5)]
      for real in (-2,-1,0,1,2,3,4):
       for imag in (-3,-2,-1,1,2,3):
        k=s.Rational(real,2)+s.I*s.Rational(imag,3)
        M=sum(weight/(a-k) for a,weight in zip(aa,ww))
        b0=k*M
        NN=s.expand_complex(k*s.conjugate(k))*sum(weight/((a-k)*(a-s.conjugate(k))) for a,weight in zip(aa,ww))
        QQ=s.expand_complex(k*s.conjugate(k))*sum(a*weight/((a-k)*(a-s.conjugate(k))) for a,weight in zip(aa,ww))
        NN=s.simplify(NN);QQ=s.simplify(QQ)
        check(s.simplify(QQ-k*(NN+s.conjugate(b0)))==0,'native_shape_sampling_identity')
        check(s.simplify(s.im(s.expand_complex(M))/s.im(k)-NN/(k*s.conjugate(k)))==0,'herglotz_norm_identity')
        check(s.simplify(s.im(s.expand_complex(b0))/s.im(k)-QQ/(k*s.conjugate(k)))==0,'source_pairing_imaginary_identity')
        check(NN>0 and QQ>=NN/4,'positive_spectral_form')
        # Safe coarse moment envelope, with no source-specific positivity assumption.
        M0=sum(weight/a for a,weight in zip(aa,ww))
        # square the bound |b| <= |k| M0 (1+|k|/|Im k|)
        modk=s.sqrt(s.re(k)**2+s.im(k)**2)
        rhs=modk*M0*(1+modk/abs(s.im(k)))
        check(s.simplify(rhs**2-b0*s.conjugate(b0))>=0,'priced_nonreal_sampling_upper')
    # Rational cell integrals for generic exponents; direct antiderivative identity.
    ss=s.symbols('ss', nonzero=True)
    for N in range(1,31):
        # Coefficient identities behind s I_N = N^(1-s)/(1-s)-H_N(s).
        coeff=Counter()
        for k in range(1,N):
            coeff[k]+=k;coeff[k+1]-=k
        desired=Counter({k:1 for k in range(1,N)})
        desired[N]=-(N-1)
        check(all(coeff[k]==desired[k] for k in set(coeff)|set(desired)), 'finite_mellin_telescoping')
    # Coupled kernel identities at distinct nodes of a finite positive model.
    aa=[s.Rational(1,4),s.Rational(5,4),s.Rational(17,4)]
    ww=[s.Rational(1,2),s.Rational(2,3),s.Rational(1,5)]
    zz=[s.Rational(-1,2)+s.I,s.Rational(3,2)+2*s.I,3-s.I]
    for ki in zz:
      for kj in zz:
        Mi=sum(v/(a-ki) for a,v in zip(aa,ww))
        Mj=sum(v/(a-kj) for a,v in zip(aa,ww))
        K=sum(v/((a-ki)*(a-s.conjugate(kj))) for a,v in zip(aa,ww))
        check(s.simplify((Mi-s.conjugate(Mj))-(ki-s.conjugate(kj))*K)==0,'undivided_stieltjes_kernel')
    return dict(COUNTS)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',required=True,type=Path);a=p.parse_args()
    groups=run();out={'status':'PASS_FINITE_EXACT_ONLY','counts':groups,'total_checks':sum(groups.values()),'optimized':not __debug__,'python':platform.python_version(),'sympy':s.__version__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'actual_offline_zeros_used':False,'analytic_theorems_certified':False}
    a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
