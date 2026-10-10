"""Exact symbolic controls for RHRC source inertia research (not a proof).

Requires sympy. Uses the fact that at omega=1/2 the full source matrix is
Diag((-1)^n) on centered indices, and uses Chebyshev parity-polynomial bases.
Checks K=2..7 inertia and sample moment identities and rational convolution
asymptotics from Steps 36-48. These checks are REGRESSION/EXPERIMENTAL controls,
not Lean theorem authority. No internet or external files required.
"""
import sympy as s

x = s.symbols('x')

def polynomial_parity_basis(K, parity):
    # C_u = sum_n u_n cos(nt); for even u, C_u = u_0 + 2 sum u_n T_n
    # T_u = sum_n u_n sin(nt); for odd u, T_u/sin(t) = 2 sum u_n U_{n-1}
    if parity == 'even':
        trig_basis = [s.Integer(1)] + [2*s.chebyshevt(n, x) for n in range(1, K+1)]
        filtered = [s.expand((1-x)**2*x**j) for j in range(K-1)]
        diagonal = [1] + [2*(-1)**n for n in range(1, K+1)]
    else:
        trig_basis = [2*s.chebyshevu(n-1, x) for n in range(1, K+1)]
        filtered = [s.expand((1-x)*x**j) for j in range(K-1)]
        diagonal = [2*(-1)**n for n in range(1, K+1)]
    n = len(trig_basis)
    change = s.Matrix([[s.expand(p).coeff(x,k) for p in trig_basis] for k in range(n)])
    assert change.det() != 0
    inverse = change.inv()
    B = s.Matrix.hstack(*(inverse*s.Matrix([p.coeff(x,k) for k in range(n)]) for p in filtered))
    return B.T*s.diag(*diagonal)*B

def inertia_from_minors(H):
    # Valid only because each leading principal determinant is nonzero.
    principal = [s.sign(H[:r,:r].det()) for r in range(1,H.rows+1)]
    assert all(t != 0 for t in principal)
    pivots = [principal[0]] + [principal[j]*principal[j-1] for j in range(1,len(principal))]
    return pivots.count(1), pivots.count(-1), principal

def centered_moment(u,k,r):
    return sum(s.Integer(n-k)**r*v for n,v in enumerate(u))

def beta(i,j):
    return s.factorial(i)*s.factorial(j)/s.factorial(i+j+1)

def convolution_integral(poly):
    # integral_0^1 p(t)p(1-t) dt, via beta integrals
    terms=s.Poly(s.expand(poly),x).terms()
    return s.factor(sum(ci*cj*beta(i[0],j[0]) for i,ci in terms for j,cj in terms))

for K in range(2,8):
    for parity in ('even','odd'):
        pos, neg, minors = inertia_from_minors(polynomial_parity_basis(K,parity))
        d=K-1
        expected=((d+1)//2,d//2) if parity=='even' else (d//2,(d+1)//2)
        assert (pos,neg)==expected, (K,parity,(pos,neg),expected)
        print(f'K={K} {parity}: inertia +{pos}/-{neg}; minors {minors}')

witnesses={
  ('even',2):((1,-4,6,-4,1),4,24),
  ('odd',2):((-1,2,0,-2,1),3,12),
  ('even',3):((1,-6,15,-20,15,-6,1),6,720),
  ('odd',3):((-1,4,-5,0,5,-4,1),5,240),
}
for (par,K),(u,r,val) in witnesses.items():
    assert all(centered_moment(u,K,j)==0 for j in range(r))
    assert centered_moment(u,K,r)==val

# Fixed exact negative even K=3 source energy at omega=1/2.
u=(1,-4,7,-8,7,-4,1)
assert all(centered_moment(u,3,j)==0 for j in range(4))
assert centered_moment(u,3,4)==48
assert sum((-1)**(n-3)*v*v for n,v in enumerate(u))==-4

# Step 39 rational leading coefficients for moving carriers.
assert convolution_integral(-x**6+s.Rational(3,11)*x**4)==-s.Rational(23,660660)
assert -convolution_integral(2*x**5-s.Rational(5,9)*x**3)==s.Rational(19,24948)
print('All exact symbolic controls passed (not a Lean proof).')
