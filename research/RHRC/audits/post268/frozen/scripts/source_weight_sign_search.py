import numpy as np,sympy as sp,json
from pathlib import Path
out=[]
for K in range(2,11):
 idx=np.arange(-K,K+1); C=sp.zeros(2*K+1,K+1);C[K,0]=1
 for n in range(1,K+1): C[K-n,n]=C[K+n,n]=1
 F=sp.Matrix([[sp.Integer(int(n))**r for n in idx] for r in (0,2)])
 B=C*sp.Matrix.hstack(*(F*C).nullspace());b=np.array(B).astype(float)
 q=np.linalg.qr(b)[0]
 for a in np.arange(1,32)/32:
  H=np.zeros((2*K+1,2*K+1))
  for i,n in enumerate(idx):
   for j,m in enumerate(idx):
    H[i,j]= 2*np.cos(2*np.pi*n*a)-4*np.pi*n*a*np.sin(2*np.pi*n*a) if i==j else 2*(n*np.cos(2*np.pi*n*a)-m*np.cos(2*np.pi*m*a))/(n-m)
  vals,v=np.linalg.eigh(q.T@H@q)
  if vals[0]<-1e-6:
   # Small rational search for an exact witness in coefficient coordinates.
   for trial in range(2000):
    c=np.random.default_rng(1000+trial).integers(-4,5,size=B.cols)
    if c@(b.T@H@b)@c < -1e-6:
     u=B*sp.Matrix(c);t=sp.Rational(round(a*32),32)
     g=0
     for i,n0 in enumerate(idx):
      n=int(n0)
      for j,m0 in enumerate(idx):
       m=int(m0)
       h=2*sp.cos(2*sp.pi*n*t)-4*sp.pi*n*t*sp.sin(2*sp.pi*n*t) if i==j else 2*(n*sp.cos(2*sp.pi*n*t)-m*sp.cos(2*sp.pi*m*t))/sp.Integer(n-m)
       g+=u[i]*u[j]*h
     g=sp.simplify(g)
     out.append({'K':K,'omega':str(t),'u':[str(x) for x in u],'source_first_derivative_exact':str(g),'numerical_value':float(sp.N(g,30)),'moment0':str(sum(u)),'moment2':str(sum(int(n)**2*u[i] for i,n in enumerate(idx))),'moment4':str(sum(int(n)**4*u[i] for i,n in enumerate(idx)))})
     break
   break
 if out: break
p=Path('/mnt/data/rh_audit/results/source_weight_sign_search.json');p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
