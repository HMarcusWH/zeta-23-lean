"""Exact algebraic falsifiers for proposed implications. NOT canonical RH counterexamples."""
import sympy as s, json
from pathlib import Path
O=Path('/mnt/data/rh_audit'); w=s.symbols('w',real=True)
records=[]
# Boundary-flat centered moments and genuine source-atom derivative at rational omega.
for K in [2,3,4]:
 idx=list(range(-K,K+1));dim=len(idx)
 constraints=s.Matrix([[s.Integer(n)**k for n in idx] for k in range(3)])
 # Columns are exact even vectors, then null out moments 0 and 2.
 C=s.zeros(dim,K+1)
 C[K,0]=1
 for n in range(1,K+1):C[K-n,n]=1;C[K+n,n]=1
 B=C*s.Matrix.hstack(*(constraints*C).nullspace())
 S=s.Matrix(dim,dim,lambda i,j:2*w*s.cos(2*s.pi*idx[i]*w) if i==j else (s.sin(2*s.pi*idx[i]*w)-s.sin(2*s.pi*idx[j]*w))/(s.pi*(idx[i]-idx[j])))
 Sp=S.diff(w)
 for a in [s.Rational(1,4),s.Rational(1,2),s.Rational(3,4)]:
  H=s.simplify(B.T*Sp.subs(w,a)*B)
  for c in ([s.Matrix([1]) ] if B.cols==1 else [s.eye(B.cols).col(i) for i in range(B.cols)]+[s.Matrix([(-1)**i for i in range(B.cols)]),s.ones(B.cols,1)]):
   u=B*c; val=s.simplify((c.T*H*c)[0]);m4=sum(s.Integer(n)**4*u[i] for i,n in enumerate(idx))
   if float(s.N(val)) < -1e-10 and m4 !=0:
    g=s.expand((u.T*S*u)[0]);jet=s.simplify(s.diff(g,w,9).subs(w,0))
    rec={'K':K,'omega':str(a),'u':[str(x) for x in u],'moments0to4':[str(sum(s.Integer(n)**k*u[i] for i,n in enumerate(idx))) for k in range(5)],'source_derivative':str(val),'source_ninth_derivative_at_zero':str(jet),'expected_ninth_jet':str(2*(2*s.pi)**8*m4**2),'moment_identity_check':s.simplify(jet-2*(2*s.pi)**8*m4**2)==0}
    records.append(rec)
    break
# Exact scalar examples: crossing contact and endpoint local-to-integral transfer.
t=s.symbols('t',real=True); f=-t**3;weight=(1-t)**8*(1-20*(1-t))
W=s.diag(-2,-1,1,2,3,4,5);U=s.eye(7)[:,3:]
example={'f':'-t^3','f_at0':str(f.subs(t,0)),'fprime_at0':str(s.diff(f,t).subs(t,0)),'f_at_minus1':str(f.subs(t,-1)),'f_at_plus1':str(f.subs(t,1)),'conclusion':'A nonnegative first derivative at contact does not exclude a higher-order downward crossing.'}
endpoint={'weight':str(weight),'jets0to8_at1':[str(s.diff(weight,t,j).subs(t,1)) for j in range(9)],'integral0to1':str(s.integrate(weight,(t,0,1))),'conclusion':'Vanishing through order7 and a positive eighth endpoint derivative do not imply global weight sign or a nonnegative integral.'}
carrier={'full_diagonal':list(map(int,W.diagonal())),'carrier_basis':'last four coordinate vectors, codimension3','restricted_diagonal':list(map(int,(U.T*W*U).diagonal())),'conclusion':'Negative full bottom does not force negative constrained bottom.'}
# Rank-two displacement and reversal leave scalar-shift freedom.
D=s.diag(*range(-3,4));A=s.eye(7);c=s.Integer(-2)
shift={'base':'I7','shift':'-2 I7','new':'-I7','commutator_difference_zero':D*(A+c*s.eye(7))-(A+c*s.eye(7))*D==D*A-A*D,'base_positive':True,'shifted_negative':True,'conclusion':'Displacement/reversal/nesting are insensitive to a scalar shift that reverses positivity.'}
out={'claim_cap':'EXACT_COUNTEREXAMPLES_TO_GENERIC_INFERENCES; NOT_CANONICAL_COUNTEREXAMPLES; RH_OPEN','canonical_source_weight_examples':records,'first_contact':example,'endpoint_weight':endpoint,'carrier':carrier,'scalar_shift':shift}
(O/'results/mathematical_falsifiers.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
