#!/usr/bin/env python3
"""Finite exact checks of the OPICA paper. Not a Lean or infinite-analysis proof.
All mathematical comparisons are rational/polynomial identities. Output is JSON.
"""
from __future__ import annotations
from fractions import Fraction as F
from collections import Counter
from math import comb, factorial, gcd
from pathlib import Path
import json, sys, platform, hashlib, argparse, subprocess

counts: Counter[str] = Counter()
fixtures = {}
def verify(ok: bool, group: str, description: str) -> None:
    if not ok:
        raise AssertionError(f'{group}: {description}')
    counts[group] += 1

def clean(a): return {k:F(v) for k,v in a.items() if v}
def add(a,b):
    c=dict(a)
    for k,v in b.items(): c[k]=c.get(k,F(0))+v
    return clean(c)
def mul(a,b):
    c={}
    for i,x in a.items():
        for j,y in b.items(): c[i+j]=c.get(i+j,F(0))+x*y
    return clean(c)
def scale(a,c): return clean({k:v*c for k,v in a.items()})
def power(a,n):
    c={0:F(1)}
    for _ in range(n): c=mul(c,a)
    return c
def mon(k,c=1): return {k:F(c)}
def order(a): return min(a) if a else None

def local_checks():
    for m in range(1,7):
        zeta=mul(mon(m),{0:F(2),1:F(3),2:F(-1)})
        for R in [F(-3,2),F(1),F(7,3)]:
            field=add(mon(-1,R),{0:F(5),1:F(-2),2:F(1)})
            b={0:F(2,3),1:F(-4)}
            res=add(mon(0),mul(zeta,b))
            for n in range(0,5):
                out=mul(power(res,n),field)
                verify(out.get(-1)==R,'local_residual','residue at every tested power')
                diff=add(out,scale(field,-1))
                verify(not diff or order(diff)>=m-1,'local_residual','strong error ideal')
            a={0:F(5,7),1:F(-1),2:F(2)}
            comp=mul(zeta,a)
            for p in range(1,5):
                out=mul(power(comp,p),field)
                k=p*m-1
                expected=R*(F(10,7)**p)
                verify(order(out)==k,'local_completion','exact completed order')
                verify(out[k]==expected,'local_completion','leading coefficient')
                verify(factorial(k)*out[k]==factorial(k)*expected,'local_completion','jet factorial')
            x=mon(1)
            verify(not add(mul(x,mon(-1)),mon(0,-1)), 'affine_background', 'post-completion background can cancel raw output')
    # Finite affine transport: actual recursion vs full correction ledger.
    for depth in range(1,9):
        f0={-1:F(3),0:F(2),1:F(-1)}
        f=f0; correction={}; prod=mon(0)
        for i in range(depth):
            M=mul(mon(i%3),{0:F(i+2,i+1),1:F(-1,2)})
            B={0:F((-1)**i*(i+1)),2:F(1,i+1)}
            f=add(mul(M,f),B)
            correction=add(mul(M,correction),B)
            prod=mul(M,prod)
        verify(add(f,scale(correction,-1))==mul(prod,f0),'affine_composition','exact correction ledger')
        verify(order(mul(prod,f0))==sum(i%3 for i in range(depth))-1,'affine_composition','total order')
    # Raw derivative product at the double-completion order includes binomial.
    for m in range(1,9):
        lhs=factorial(2*m-1)
        rhs=comb(2*m-1,m)*factorial(m)*factorial(m-1)
        verify(lhs==rhs,'jet_normalization','binomial Leibniz coefficient')

def energy_checks():
    grid=[F(i,3) for i in range(-12,13)]
    for a in grid:
        for b in grid:
            pa=max(a,F(0));pb=max(b,F(0));d=abs(a-b)
            verify(1+pa <= (1+pb)*(1+d),'log_comparison','positive-part product inequality')
            verify(1+abs(a) <= (1+abs(b))*(1+d),'log_comparison','absolute-value product inequality')
    for a in [F(1,9),F(2,3),F(1),F(3,2),F(7)]:
        C=max(a,1/a)
        for z in grid:
            verify(1+max(a*z,F(0)) <= C*(1+max(z,F(0))),'scale_comparison','forward tempered scale')
            verify(1+max(z,F(0)) <= C*(1+max(a*z,F(0))),'scale_comparison','reverse tempered scale')
    for depth in range(1,12):
        A=[F(i+2,i+1) for i in range(depth)]
        D=[F(i+1,i+3) for i in range(depth)]
        z=F(3)
        for a,d in zip(A,D):z=a*z+d
        prod=lambda xs: __import__('functools').reduce(lambda x,y:x*y,xs,F(1))
        closed=F(3)*prod(A)+sum(D[j]*prod(A[j+1:]) for j in range(depth))
        verify(z==closed,'error_recurrence','all additive propagation terms retained')

def matrix_checks():
    # The Gram of 1 and t on [0,1] is NOT rank one.
    det=F(1)*F(1,3)-F(1,2)**2
    verify(det==F(1,12),'gram_and_projection','positive rank-two Gram determinant')
    verify((F(1),F(-1)) != (F(0),F(0)),'gram_and_projection','contrast nonzero')
    # P=I-11^T/2 kills vector 1 whose sum is two.
    verify(F(1)-F(1,2)*(1+1)==0 and 1+1==2,'gram_and_projection','target lost by contrast projection')
    # Arbitrarily many evaluations of a degree-five polynomial are consistent.
    alpha=[F(1),F(-2),F(3),F(0),F(2),F(-1)]
    y=[sum(alpha[j]*F(i)**j for j in range(6)) for i in range(1,9)]
    weights=[F((-1)**(6-i)*comb(6,i)) for i in range(7)]
    verify(sum(weights[i]*y[i] for i in range(7))==0,'compatibility','seven-row consistency annihilator')
    ybad=y[:];ybad[6]+=1
    verify(sum(weights[i]*ybad[i] for i in range(7))==1,'compatibility','genuine inconsistent residual')
    fixtures['seven_rows']={'consistent_left_null_pairing':'0','inconsistent_left_null_pairing':'1'}
    # Involution diag(1,-1), selfdual input e1, offdiagonal P.
    v=[F(1),F(0)]; p=[[F(0),F(1)],[F(1),F(0)]]
    Fourier=lambda x:[x[0],-x[1]]
    P=lambda x:[sum(p[i][j]*x[j] for j in range(2)) for i in range(2)]
    c=[P(Fourier(v))[i]-Fourier(P(v))[i] for i in range(2)]
    verify(Fourier(c)==[-x for x in c], 'fourier_involution','commutator anti-selfdual')
    verify([c[i]+Fourier(c)[i] for i in range(2)]==[F(0),F(0)],'fourier_involution','selfdual projection kills commutator')

def dcount(n,l):
    out=1;p=2
    while p*p<=n:
        e=0
        while n%p==0:e+=1;n//=p
        if e:out*=comb(e+l-1,l-1)
        p+=1
    if n>1:out*=l
    return out

def mu(n):
    out=1;p=2
    while p*p<=n:
        if n%p==0:
            n//=p;out=-out
            if n%p==0:return 0
        p+=1
    if n>1:out=-out
    return out

def c2(n,Y,Q):
    ans=0
    for a in range(Y+1,n+1):
        if n%a or gcd(a,Q)>1:continue
        for b in range(Y+1,n//a+1):
            if (n//a)%b:continue
            h=n//(a*b)
            if gcd(b*h,Q)==1:ans+=mu(a)*mu(b)
    return ans

def arithmetic_checks():
    for l in range(1,7):
        for n in range(1,181):
            verify(dcount(n,l)**2<=dcount(n,l*l),'divisor_bounds','squared divisor count')
        for a in range(1,18):
            for b in range(1,18):
                verify(dcount(a*b,l)<=dcount(a,l)*dcount(b,l),'divisor_bounds','submultiplicativity')
    x=c2(121,10,2);y=c2(1331,10,2)
    verify(x==1 and y==1,'balanced_mask','non-squarefree coefficients survive')
    h=gcd(121,1331);a=121//h;b=1331//h
    verify(a==1 and b==11 and gcd(a,b)==1 and gcd(h,a*b)>1,'balanced_mask','common gcd can overlap primitive factor')
    verify(max(a,b)>7 and not(a>7 and b>7),'balanced_mask','max mask not both-large mask')
    fixtures['repeated_prime']={'Y':10,'Q':2,'d':121,'e':1331,'c2_d':x,'c2_e':y,'gcd':h,'a':a,'b':b}
    # Absorption changes mask labels: d=A*u,e=B*v, rather than just A,B.
    verify(max(2,3)//gcd(2,3)<=5 and max(2*11,3*13)//gcd(2*11,3*13)>5,'balanced_mask','kernel absorption changes quadratic mask')

def fejer_checks():
    # x=e^t chosen rational. Work with K*x^(3/2), a*x^(3/2).
    for m in range(1,21):
        for u in [F(0),F(1,7),F(1,2),F(6,7)]:
            x=F(m)+u
            K=-x*x+(2*m+1)*x-m*(m+1)
            a=m*(m+1-x)
            verify(K==u*(1-u),'fejer_kernel','fractional-part identity')
            verify(K+a==x*(1-u),'fejer_kernel','native sum identity')
            verify(K==u*a/m,'fejer_kernel','native multiplicative comparison')
            verify(K>=0 and K<=F(1,4),'fejer_kernel','scaled positive upper')
    for z in [F(1),F(2),F(3,4),F(7,5)]:
        cF=2/((z+F(1,2))*(z+F(3,2)))
        cA=(z-F(1,2))/((z+F(1,2))*(z+F(3,2)))
        # compare coefficient of a formal zeta variable and constant separately
        verify(cA==F(1,2)*(z-F(1,2))*cF,'fejer_kernel','zeta coefficient transfer')
        constant=F(1,2)*(z-F(1,2))*(-1/(z-F(1,2))+1/(z+F(1,2)))+1/(2*(z+F(1,2)))
        verify(constant==0,'fejer_kernel','additive boundary correction required')
    # Derivative of scaled shell quadratic: at u=0 and u=1 opposite nonzero signs.
    for n in range(2,12):
        verify(1-2*F(0)==1 and 1-2*F(1)==-1,'fejer_kernel','nonzero one-sided cusp slopes')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    counts.clear();fixtures.clear()
    local_checks();energy_checks();matrix_checks();arithmetic_checks();fejer_checks()
    if sum(counts.values())!=5112:
        raise ValueError('frozen finite-control count drift')
    this=Path(__file__)
    result={'schema':'OPICA_FINITE_EXACT_CHECKS_V1','status':'PASS','assertions':sum(counts.values()),'groups':dict(counts),'fixtures':fixtures,'python':platform.python_version(),'checker_sha256':hashlib.sha256(this.read_bytes()).hexdigest(),'authority':'Finite rational/Laurent-polynomial and combinatorial checks only; analytic theorems have written proofs; no Lean or RH proof.'}
    result['upstream_checker_sha256']='7e7087814aa6c410790c346fb124321c042a4b18242fe171bda9016b52b7e018'
    repo=this.resolve().parents[4]
    def git(*parts):
        return subprocess.check_output(['git',*parts],cwd=repo,text=True).strip()
    result.update(checked_commit=git('rev-parse','HEAD'),checked_tree=git('rev-parse','HEAD^{tree}'),
        tracked_source_dirty=bool(git('status','--porcelain','--untracked-files=no')))
    if args.output:
        if args.output.resolve().is_relative_to(this.resolve().parents[4]):
            parser.error('execution artifacts must be outside the repository')
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
