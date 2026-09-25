"""Unconditional canonical finite matrices; FLOAT DISCOVERY ONLY, not certification."""
from pathlib import Path
import sys,json,time
import numpy as np
import sympy as sp
R=Path('/mnt/data/rh_audit/snapshot/zeta-23-lean-main')
sys.path.insert(0,str(R/'research/RHRC/routes/R003_ccm_bridge'))
from canonical_source_numeric import canonical_source_matrix_L
out=[]
for K in (2,3,4,6):
    ns=list(range(-K,K+1));q={}
    for parity in ('even','odd'):
        C=sp.zeros(2*K+1,K+1 if parity=='even' else K)
        if parity=='even':
            C[K,0]=1
            for n in range(1,K+1):C[K-n,n]=C[K+n,n]=1
            F=sp.Matrix([[sp.Integer(n)**r for n in ns] for r in (0,2)])
        else:
            for n in range(1,K+1):C[K-n,n-1]=-1;C[K+n,n-1]=1
            F=sp.Matrix([[sp.Integer(n) for n in ns]])
        B=C*sp.Matrix.hstack(*(F*C).nullspace())
        q[parity]=np.linalg.qr(np.array(B).astype(float))[0]
    ww=np.linspace(0.001,0.999,999)
    H=[]
    n=np.array(ns);nrow=n[:,None];ncol=n[None,:];dn=nrow-ncol
    for w in ww:
        c=np.cos(2*np.pi*n*w)
        mat=np.divide(2*((n*c)[:,None]-(n*c)[None,:]),dn,out=np.zeros_like(dn,dtype=float),where=dn!=0)
        np.fill_diagonal(mat,2*c-4*np.pi*n*w*np.sin(2*np.pi*n*w))
        H.append(mat)
    H=np.array(H)
    for L in (.5,1.,2.,3.,4.):
        M=canonical_source_matrix_L(L,K)
        row={'K':K,'L':L,'matrix_scale':float(np.linalg.norm(M,2)),'parities':{}}
        for p in q:
            A=q[p].T@M@q[p];a,z=np.linalg.eigh(A);u=q[p]@z[:,0]
            weights=np.einsum('i,wij,j->w',u,H,u)
            im=int(np.argmin(weights));ix=int(np.argmax(weights))
            row['parities'][p]={'bottom':float(a[0]),'gap':float(a[1]-a[0]) if len(a)>1 else None,
              'relative_eigen_residual':float(np.linalg.norm(A@z[:,0]-a[0]*z[:,0])/max(np.linalg.norm(A,2),1e-300)),
              'weight_min':float(weights[im]),'min_omega':float(ww[im]),'weight_max':float(weights[ix]),
              'ground_coefficients':[float(x) for x in u]}
        row['lower_parity']=min(row['parities'],key=lambda p:row['parities'][p]['bottom'])
        out.append(row)
        print(K,L,[(p,row['parities'][p]['bottom'],row['parities'][p]['weight_min']) for p in q],flush=True)
        Path('/mnt/data/rh_audit/results/ground_weight_scout.json').write_text(json.dumps({'claim_cap':'FLOAT_DISCOVERY_ONLY_NOT_CERTIFIED_GROUND_ENCLOSURES','rows':out},indent=2)+'\n')
