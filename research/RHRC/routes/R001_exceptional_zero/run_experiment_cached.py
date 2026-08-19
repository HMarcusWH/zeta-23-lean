from __future__ import annotations

import argparse, json, time, urllib.request
from pathlib import Path
import mpmath as mp
import numpy as np

OUTDIR = Path(__file__).resolve().parent / 'outputs'
ODLYZKO_ZEROS_URL = 'https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros1'


def first_zeros(n: int, cache: Path) -> tuple[np.ndarray, str]:
    if cache.exists():
        arr=np.load(cache)
        if len(arr)>=n: return arr[:n], 'local_cache'
    if n <= 100000:
        try:
            with urllib.request.urlopen(ODLYZKO_ZEROS_URL, timeout=20) as r:
                vals=[]
                for raw in r:
                    line=raw.decode('ascii').strip()
                    if not line: continue
                    vals.append(float(line))
                    if len(vals) >= n: break
            if len(vals) >= n:
                arr=np.asarray(vals[:n],dtype=float)
                cache.parent.mkdir(parents=True,exist_ok=True); np.save(cache,arr)
                return arr, 'Odlyzko_zeros1_first_100000_accuracy_3e-9'
        except Exception:
            pass
    mp.mp.dps=30
    arr=np.array([float(mp.im(mp.zetazero(k))) for k in range(1,n+1)], dtype=float)
    cache.parent.mkdir(parents=True, exist_ok=True); np.save(cache,arr); return arr, 'mpmath.zetazero_fallback'


def zero_terms(a: float, xi: np.ndarray, gammas: np.ndarray, *, chunk: int=64) -> np.ndarray:
    out=np.zeros_like(xi,dtype=np.complex128)
    for start in range(0,len(gammas),chunk):
        g=gammas[start:start+chunk,None]
        for sign in (1.0,-1.0):
            d=1j*(sign*g-xi[None,:])
            out += np.sum(np.exp(2*a*d)/d,axis=0)
    return out


def online_double(a,xi,gamma):
    out=np.zeros_like(xi,dtype=np.complex128)
    for g in (gamma,-gamma):
        d=1j*(g-xi); out += 2*np.exp(2*a*d)/d
    return out


def offline_pair(a,xi,gamma,delta):
    out=np.zeros_like(xi,dtype=np.complex128)
    for beta in (delta,-delta):
        for g in (gamma,-gamma):
            d=beta+1j*(g-xi); out += np.exp(2*a*d)/d
    return out


def rms(z,mask): return float(np.sqrt(np.mean(np.abs(z[mask])**2)))
def slope(ap,vals,min_a=30):
    ap=np.asarray(ap); vals=np.asarray(vals); m=(ap>=min_a)&np.isfinite(vals)&(vals>0)
    return float(np.polyfit(ap[m],np.log(vals[m]),1)[0])


def main():
    p=argparse.ArgumentParser(); p.add_argument('--zeros',type=int,default=100); p.add_argument('--grid',type=int,default=5400); p.add_argument('--aperture-max',type=float,default=300); p.add_argument('--output',type=Path,default=OUTDIR/'r001_cached.json'); args=p.parse_args()
    t=time.time(); cache=OUTDIR/f'zeta_zeros_{args.zeros}.npy'; gs,zero_source=first_zeros(args.zeros,cache); xmax=min(float(gs[-1])-5,390.0); xi=np.linspace(10,xmax,args.grid); gamma=float(gs[min(59,len(gs)-1)])
    base_ap=np.array([3,4,5,6,8,10,12,16,20,25,30,40,50,60,70,80,90,100],float)
    extra=np.arange(120,args.aperture_max+1,20,dtype=float) if args.aperture_max>100 else np.array([],float); aps=np.unique(np.concatenate([base_ap,extra]))
    pole=np.ones_like(xi,dtype=bool)
    for g in gs: pole &= np.abs(xi-g)>=0.15
    local=pole&(xi>=gamma-24)&(xi<gamma+24)
    bases={float(a):zero_terms(float(a),xi,gs) for a in aps}
    def curve(kind,delta=0.0,g=gamma,g2=None):
        vals=[]
        for a in aps:
            z=bases[float(a)].copy()
            if kind=='double': z+=online_double(float(a),xi,g)
            elif kind=='pair': z+=offline_pair(float(a),xi,g,delta)
            elif kind=='two': z+=offline_pair(float(a),xi,g,delta)+offline_pair(float(a),xi,float(g2),delta)
            vals.append(rms(z,local))
        return np.array(vals), slope(aps,vals), slope(aps,vals,min_a=max(60,args.aperture_max*0.4))
    dbl,dbl30,dbl_late=curve('double')
    ds={}
    for d in [0.005,0.01,0.02,0.05,0.1]:
        v,s30,sl=curve('pair',d); ds[f'{d:.3f}']={'slope_a30':s30,'slope_late':sl,'predicted_2delta':2*d,'rms':[float(x) for x in v]}
    spacings=np.concatenate([np.linspace(.005,.1,20),np.linspace(.12,1.0,12)])
    canc=[]
    for sp in spacings:
        v,s30,sl=curve('two',.05,gamma-sp/2,gamma+sp/2); canc.append({'spacing':float(sp),'slope_a30':s30,'slope_late':sl})
    worst=min(canc,key=lambda x:x['slope_late'])
    result={'run_id':'R001_CACHED_HEAVY_RUN','phase':'DISCOVERY','claim_cap':'FINITE_NUMERICAL_SYNTHETIC_DIAGNOSTIC_ONLY','configuration':{'zeros':args.zeros,'grid':args.grid,'apertures':[float(x) for x in aps],'anchor_gamma':gamma,'zero_source':zero_source},'online_double':{'slope_a30':dbl30,'slope_late':dbl_late},'offline_pairs':ds,'cancellation_scan':{'worst':worst,'records':canc},'bounded_claim':{'result':'PASS' if ds['0.050']['slope_late']>max(dbl_late,0)+0.02 and ds['0.100']['slope_late']>0.15 else 'FAIL','certificate_status':'VALID','authority':'EXPERIMENTAL_EVIDENCE'},'open_obligations':['R001_ZERO_GROWTH OPEN','R001_PRIME_UPPER OPEN','No RH theorem promotion'],'runtime_seconds':time.time()-t}
    args.output.parent.mkdir(parents=True,exist_ok=True); args.output.write_text(json.dumps(result,indent=2)); print(json.dumps({'bounded_result':result['bounded_claim']['result'],'delta_005':ds['0.005']['slope_late'],'delta_010':ds['0.010']['slope_late'],'delta_020':ds['0.020']['slope_late'],'delta_050':ds['0.050']['slope_late'],'delta_100':ds['0.100']['slope_late'],'worst_cancellation':worst,'runtime_seconds':result['runtime_seconds'],'output':str(args.output)},indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
