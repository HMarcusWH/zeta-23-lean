"""Exact SymPy/rational certificate, independent of floating-point sign decisions.
The only analytic identity used by the pi enclosure is Machin's formula.
No repository file is modified. Run with Python + SymPy.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import sympy as s

u = [-1, 3, 1, -15, 24, -15, 1, 3, -1]
ns = list(range(-4, 5))
a = s.Rational(1, 8)
H = s.zeros(9)
for i,n in enumerate(ns):
    for j,m in enumerate(ns):
        H[i,j] = (2*s.cos(2*s.pi*n*a)-4*s.pi*n*a*s.sin(2*s.pi*n*a)
                  if i == j else
                  2*(n*s.cos(2*s.pi*n*a)-m*s.cos(2*s.pi*m*a))/s.Integer(n-m))
v=s.Matrix(u)
value=s.simplify((v.T*H*v)[0])
expected=s.Rational(25432,21)-s.Rational(15962,35)*s.sqrt(2)-126*s.sqrt(2)*s.pi-2*s.pi
assert s.simplify(value-expected)==0
moments={k:sum(c*n**k for c,n in zip(u,ns)) for k in range(10)}
assert all(moments[k]==0 for k in range(4)) and moments[4]==-24
assert u==u[::-1]
# atan(1/q) alternating series: even number of terms lower, odd upper.
def atan_partial(q:int,n:int)->F:
    return sum((F((-1)**k,(2*k+1)*q**(2*k+1)) for k in range(n)),F(0))
pi_lower=16*atan_partial(5,16)-4*atan_partial(239,9)
pi_upper=16*atan_partial(5,17)-4*atan_partial(239,8)
r=F(1414213562373095,10**15)
p=F(3141592653589793,10**15)
assert r*r<2 and pi_lower>p and pi_lower<pi_upper
upper=F(25432,21)-F(15962,35)*r-126*r*p-2*p
assert upper<0
# Verify Taylor coefficients of the exact atom quadratic independently of jet theorem.
# coefficient of w^(2r+1), after factoring 2*(-1)^r*(2*pi)^(2r)/(2r+1)!, is
# sum_ij u_i u_j * ((n_i^(2r+1)-n_j^(2r+1))/(n_i-n_j)), diagonal limit (2r+1)n_i^(2r).
coeffs={}
for j in range(5):
    d=2*j+1
    P=sum(F(u[i]*u[k])*(F(d*n**(d-1)) if n==m else F(n**d-m**d,n-m))
          for i,n in enumerate(ns) for k,m in enumerate(ns))
    coeffs[d]=str(P)
assert all(coeffs[d]=='0' for d in (1,3,5,7))
assert coeffs[9]=='576'
res={
 'status':'PASS_EXACT_RATIONAL_AND_SYMBOLIC_CHECKS',
 'claim_cap':'DERIVED_COUNTEREXAMPLE_NOT_LEAN_THEOREM_NOT_RH_COUNTEREXAMPLE',
 'K':4,'centered_indices':ns,'real_even_vector':u,
 'moments':moments,'omega':'1/8','source_first_derivative_exact':str(value),
 'source_first_derivative_decimal_diagnostic':str(s.N(value,45)),
 'sqrt2_lower':str(r),'pi_rational_lower':str(p),
 'pi_lower_certificate':'Machin identity pi=16 atan(1/5)-4 atan(1/239), alternating series (16,9) terms',
 'machin_pi_lower':str(pi_lower),'machin_pi_upper':str(pi_upper),
 'negative_upper_bound_exact':str(upper),'negative_upper_bound_decimal_diagnostic':float(upper),
 'scaled_odd_taylor_moment_coefficients':coeffs,
 'g9_at_zero':'1152*(2*pi)^8',
 'prime_weight_at_t_7L_over_8':'strictly negative for every L>0',
 'prime_weight_endpoint_jets':'orders 0 through 7 vanish; order 8 equals 1152*(2*pi)^8/L^8 > 0',
 'falsifies':'pointwise nonnegativity of the prime-test weight on all even boundary-flat vectors',
 'does_not_falsify':['ground-eigenvector-specific sign hypotheses','canonical energy positivity','RiemannHypothesis']}
path=Path('/mnt/data/rh_audit/results/source_weight_counterexample_exact.json')
path.write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(res,indent=2))
