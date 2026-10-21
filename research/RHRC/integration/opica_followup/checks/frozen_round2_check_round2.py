#!/usr/bin/env python3
"""Exact algebraic/rational controls. Not proofs of the infinite analytic statements."""
from __future__ import annotations
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import prod, factorial
from pathlib import Path
import argparse, json, platform
import sympy as s
COUNT=Counter()
def check(ok, group, detail=''):
    if not bool(ok):
        raise RuntimeError(f'{group}: {detail}')
    COUNT[group]+=1

def saddle_controls():
    for a in range(1,9):
        for b in range(1,13):
            for n in range(1,21):
                p=a*n+b
                check(2*p+2 == 2*a*n+2*b+2, 'moving_contour_degree_bookkeeping')
                check(p <= (a+b)*n, 'factorial_exponent_envelope')
    for L in range(1,100):
        for n in range(1,L+1):
            check(F(16*L*L,n*(n+1))>=8,'box_block_factor_bound')

def corridor_controls():
    for r in range(2,7):
        for C in [F(3,2),F(2),F(4)]:
            for eta in [F(0),F(1,3),F(2)]:
                for margin in [F(1,2),F(1),F(3)]:
                    K=C+r*eta+2*r+margin
                    p=(K-C-r*eta)/(2*r)
                    check(p>1,'logarithmic_slack_exponent')
                    for L in [F(1),F(3),F(10)]:
                        T=(K+10)*L
                        logY=(T-K*L)/r
                        check(logY>0,'cutoff_nonempty_scale')
                        for i in range(1,r+1):
                            arg=T-C*L-i*logY-i*eta*L
                            check(arg >= (K-C-r*eta)*L,'all_TypeI_remaining_arguments')
                    check((T - F(1,2))-(r-1)*logY == T/r-F(1,2)+K*(r-1)*L/r,'balanced_upper_endpoint_identity')
    # Finite product support, with actual integer labels and no squarefree simplification.
    for r in (2,3):
        for Y in (1,2,3):
            X=100
            for ns in product(range(Y+1,13),repeat=r):
                if prod(ns)<=X:
                    check(all(F(n)<=F(X,Y**(r-1)) for n in ns),'balanced_product_support')

def jet_controls():
    for m in range(1,7):
        for p in range(0,7):
            j=p*m-1
            for rad in [F(1,4),F(1,2),F(1),F(2)]:
                for a in [F(1,3),F(1),F(5)]:
                    E=a*rad**j
                    check(rad**(-j)*E==a,'sharp_contour_monomial_cancellation')
                    check(rad**(-j)*(E/2)<a,'strict_coefficient_recovery_margin')
                    if j>=0:
                        check(factorial(j)*rad**(-j)*E==factorial(j)*a,'Taylor_vs_derivative_factorial')

def hermite_controls():
    z=s.symbols('z')
    families=[([s.Rational(2),s.Rational(5)],[1,1]),
              ([s.Rational(2),s.Rational(5)],[2,3]),
              ([s.Rational(1,3),s.Rational(7,4),s.Rational(4)],[2,1,2]),
              ([1+s.I,1-s.I,5],[2,2,1]),
              ([2,5,11],[3,2,2]),
              ([s.Rational(1,4)],[5])]
    for nodes,mults in families:
        N=sum(mults)
        A=s.Matrix([[s.diff(z*(s.Rational(1,4)-z)**n,z,k).subs(z,node)/s.factorial(k)
                   for node,m in zip(nodes,mults) for k in range(m)] for n in range(N)])
        det=s.factor(A.det())
        formula=(-1)**(N*(N-1)//2)*s.prod(node**m for node,m in zip(nodes,mults))
        formula*=s.prod((nodes[j]-nodes[i])**(mults[i]*mults[j]) for i in range(len(nodes)) for j in range(i+1,len(nodes)))
        check(s.simplify(det-formula)==0,'confluent_profile_jet_determinant')
        check(det!=0,'finite_zero_jet_independence_fixture')
        check(A.rank()==N,'confluent_rank')

def recovery_controls():
    # Joint recovery can restore a contrast's missing coordinate.
    for dim in range(2,7):
        for eps in [s.Rational(1,2),s.Rational(1,8),s.Rational(2),s.Rational(-3)]:
            P=s.diag(*([0]+[1]*(dim-1)))
            C=s.Matrix([[eps]+[0]*(dim-1)])
            A=P.col_join(C)
            ell=s.Matrix([[1]+[0]*(dim-1)])
            R=s.Matrix([[0]*dim+[1/eps]])
            check(R*A==ell,'joint_history_recovery_identity')
            check((R*R.conjugate().T)[0]==1/(eps*eps),'exact_recovery_norm_squared')
            check(P.rank()<A.rank(),'contrast_alone_loses_observation')
    B=s.Matrix([[1,x,x*x] for x in range(1,6)])
    alpha=s.Matrix([2,-3,5]); b=B*alpha
    for y in B.T.nullspace():
        check((y.T*b)[0]==0,'oversampled_identity_has_no_fake_incompatibility')

def euler_controls():
    x=s.symbols('x',positive=True)
    rho,A,B=s.symbols('rho A B')
    k=rho*(1-rho); beta=(1-2*rho)/k
    g=(A*x**(-rho)-B*x**(rho-1))/beta
    h=1-g
    check(s.simplify(s.diff(x*x*s.diff(h,x),x)+k*h-k)==0,'Euler_cell_symbolic_identity')
    n=s.symbols('n',positive=True)
    jump=((-rho)-(rho-1))/(beta*n*n)
    check(s.factor(jump-k/n**2)==0,'actual_integer_derivative_jump')
    check(s.simplify((2*rho-1)/(2*beta)+k/2)==0,'Bernoulli_tail_sign')
    for a in [s.Rational(1,4),s.Rational(1,2),s.Rational(3,4)]:
        for b in range(1,8):
            r=a+s.I*b
            for n0 in range(1,25):
                j0=jump.subs({rho:r,n:n0})
                check(s.simplify(j0-r*(1-r)/n0**2)==0,'rational_complex_jump_controls')

def forced_gram_controls():
    for vals in [(1,3,7),(2,4,9),(1,6,10)]:
        D=s.diag(*vals); gg=s.Matrix([1,2,-1]); z=[1+s.I,2+2*s.I,4+s.I]
        hs=[a*(D-a*s.eye(3)).inv()*gg for a in z]
        # Linear-first inner product; each entry h_i dot conjugate(h_j).
        N=s.Matrix([[s.simplify((hs[i].T*hs[j].conjugate())[0]) for j in range(3)] for i in range(3)])
        Q=s.Matrix([[s.simplify(((D*hs[i]).T*hs[j].conjugate())[0]) for j in range(3)] for i in range(3)])
        bs=[s.simplify((gg.T*h)[0]) for h in hs]
        for i in range(3):
            for j in range(3):
                check(s.simplify(Q[i,j]-z[i]*(N[i,j]+s.conjugate(bs[j])))==0,'forced_source_Gram_identity')
                check(s.simplify((z[i]-s.conjugate(z[j]))*N[i,j]-(s.conjugate(z[j])*bs[i]-z[i]*s.conjugate(bs[j])))==0,'sampling_boundary_identity')
                lhs=N[i,j]/(z[i]*s.conjugate(z[j]));rhs=(bs[i]/z[i]-s.conjugate(bs[j]/z[j]))/(z[i]-s.conjugate(z[j]))
                check(s.simplify(lhs-rhs)==0,'divided_difference_Gram_identity')
            check(s.simplify(N[i,i])>0,'forced_model_positive_norm_with_nonreal_parameter')
        check(N==N.conjugate().T and Q==Q.conjugate().T,'Hermitian_Gram_controls')

def square_and_sign_controls():
    A,B,h,hb,hh=s.symbols('A B h hb hh')
    # Same constant/comb terms are represented by one formal symbol and cancel.
    constant=s.symbols('constant')
    orig=constant-B*h-A*hb+h*hb
    transformed=constant-B*h-A*hb+hh
    check(s.expand(transformed-orig-(hh-h*hb))==0,'square_duality_defect_algebra')
    for delta in [F(-2,5),F(-1,4),F(0),F(1,4),F(2,5)]:
        for gamma in range(16,101):
            D=delta*delta+gamma*gamma
            AA=delta*(F(1,4)/D-1)
            check(abs(AA)<=F(1,2),'negative_interval_coefficient_bound')
            check(-F(3,4)*gamma+F(1,8)<=-F(1,2)*gamma,'negative_interval_margin')
    check(F(5,48)*F(22,7)<F(1,3),'first_interval_stays_below_three_halves')
    check(F(16,9)*F(1,6)==F(8,27),'weighted_negative_mass_constant')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    saddle_controls();corridor_controls();jet_controls();hermite_controls();recovery_controls();euler_controls();forced_gram_controls();square_and_sign_controls()
    out={'status':'PASS_EXACT_ALGEBRA_CONTROLS_ONLY','python':platform.python_version(),'sympy':s.__version__,'optimized':not __debug__,'group_counts':dict(COUNT),'total_checks':sum(COUNT.values()),'script_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Finite rational, symbolic and matrix identities. No infinite-analytic proof, actual off-line-zero computation or Lean verification. Synthetic nonreal spectral parameters are not zeta zeros.','new_Lean_roots':0,'independent_review':False}
    args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
