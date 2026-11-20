"""Exact disjoint-cut replay with the pinned generator and complete signed rows."""
from collections import Counter
from fractions import Fraction as Q
from functools import cache
from itertools import product
from math import isqrt

from check_stopping import density_bounds, HEAD
from finite_replay import native, replay, require

X=1656575
U=1<<20
LO,HI=1441792,1474560
Y=(X-1).bit_length()**2
MARK=(443,449,457)
FP=range(1<<len(MARK))
LOW,HIGH=2,4
ZERO=(0,)*len(FP)
ONE=(1,)+(0,)*(len(FP)-1)

def validate(intervals,complete=False):
    prev=LO
    for l,r in sorted(intervals):
        require(LO<=l<r<=HI and prev<=l,"overlapping or out-of-domain family")
        if complete:
            require(prev==l,"cut omitted integer sites")
        prev=r
    if complete:
        require(prev==HI,"partial terminal cover")

def interval(k,i):
    h=(HI-LO)>>k
    return LO+i*h,LO+(i+1)*h

def divisors(f):
    ds=[1]
    for p,e in f.items():
        old=ds.copy()
        for i in range(1,e+1):
            ds.extend(d*p**i for d in old)
    return ds

def solve():
    mod=native()
    rows={n:sgn for n,sgn,*_ in mod.vertex_rows(X,1) if LO<=n<HI}
    require(U**100<=X**99<LO**100 and HI-1<=X and LO%(HI-LO)==0,"scope mismatch")
    spf=list(range(HI))
    for p in range(2,isqrt(HI-1)+1):
        if spf[p]==p:
            for m in range(p*p,HI,p):
                if spf[m]==m:
                    spf[m]=p
    require(all(spf[p]==p and p>Y for p in MARK),"marked cutoff")
    def factors(n):
        f=Counter()
        while n>1:
            p=spf[n]
            f[p]+=1
            n//=p
        return f
    bits={p:1<<i for i,p in enumerate(MARK)}
    @cache
    def B(d):
        out=ONE
        for p,e in factors(d).items():
            if p<=Y:
                if e>1: return ZERO
                out=tuple(-a for a in out)
            elif p in bits:
                if e>2: return ZERO
                bit=bits[p]
                out=tuple((out[i^bit]-out[i]) if e==1 else -out[i^bit] for i in FP)
            else:
                if e!=2: return ZERO
                out=tuple(-a for a in out)
        return out
    yprime=2
    mark=MARK[0]
    require(B(yprime)==tuple(-a for a in ONE) and B(yprime**2)==ZERO,"small-prime power")
    require(B(mark)[0]==-1 and B(mark)[1]==1 and B(mark**2)[1]==-1,"marked local coefficients")
    require(B(461)==ZERO and B(461**2)[0]==-1,"unmarked rough square")
    ids=[(k,i) for k in range(HIGH+1) for i in range(1<<k)]
    hist={key:Counter() for key in ids}
    charge=Counter()
    actual_products=set()
    active={}
    for n in range(LO,HI):
        f=factors(n)
        fp=sum(bits[p] for p in f if p in bits)
        a=all(v==1 and p>Y for p,v in f.items())
        expected=tuple(int(a and i==fp) for i in FP)
        total=[0]*len(FP)
        for d in divisors(f):
            v=B(d)
            if v!=ZERO:
                active[d]=v
                for i in FP:
                    total[i]+=v[i]
        require(tuple(total)==expected,"complete signed Dirichlet convolution failed")
        require((n in rows)==a and (not a or rows[n]==(-1)**len(f)),"true signed source disagreement")
        if a:
            actual_products.add(fp)
            for k in range(HIGH+1):
                key=k,(n-LO)//((HI-LO)>>k)
                hist[key][fp]+=1
                charge[key]+=rows[n]

    # Only d dividing at least one actual integer in the base can enter a floor count.
    for key in ids:
        l,r=interval(*key)
        v=[0]*len(FP)
        for d,coeff in active.items():
            count=(r-1)//d-(l-1)//d
            if count:
                for i in FP:
                    v[i]+=count*coeff[i]
        require(v==[hist[key][i] for i in FP],"floor inversion on a node failed")

    low,high=density_bounds(Y)
    unit=2**50
    low=Q(low*unit//1,unit)
    high=Q(-(-high*unit//1),unit)
    probabilities=[]
    for i in FP:
        pr=Q(1)
        for j,p in enumerate(MARK):
            pr*=Q(1 if i>>j&1 else p,p+1)
        probabilities.append(pr)
    require(sum(probabilities)==1,"Euler marginal normalization")
    # On intervals of constant sign, TV minus its pushforward is an affine function of density.
    projections=0
    for key in ids:
        h=(HI-LO)>>key[0]
        for mask in FP:
            cells=[{i for i in FP if (i&mask)==t} for t in FP if t&~mask==0]
            forms=[(hist[key][i],h*probabilities[i]) for i in FP]
            proj=[(sum(hist[key][i] for i in fib),h*sum(probabilities[i] for i in fib)) for fib in cells]
            knots={low,high}|{Q(n)/v for n,v in forms+proj if v and low<Q(n)/v<high}
            for den in knots:
                require(sum(abs(n-v*den) for n,v in proj)<=sum(abs(n-v*den) for n,v in forms),"projection increased TV")
            projections+=1

    @cache
    def cuts(k,i):
        if k==HIGH:
            return (((k,i),),)
        joins=tuple(a+b for a,b in product(cuts(k+1,2*i),cuts(k+1,2*i+1)))
        return (((k,i),),)+joins if k>=LOW else joins
    covers=cuts(0,0)
    require(len(covers)==625,"enumeration of complete cuts")
    floor_covers=[covers[0],covers[22],covers[-1],tuple(covers[22][::2])]
    ds=set(active)|set(range(1,4097))|{U,2*U-1,2*U,2*U+1,3*U}
    for cut in floor_covers:
        js=[interval(k,i) for k,i in cut]
        validate(js)
        for d in ds:
            err=[d*((r-1)//d-(l-1)//d)-(r-l) for l,r in js]
            if d<=2*U:
                require(sum(e*e for e in err)<=3*U*d,"disjoint floor-square budget failed")
            else:
                require(all(e==l-r for e,(l,r) in zip(err,js)),"above-shell tail contained a multiple")
    overlap_tests=0
    for js in [[(LO,LO+2),(LO+1,LO+3)],[(LO,LO+1)]*2]:
        try: validate(js)
        except ValueError: overlap_tests+=1
    require(overlap_tests==2,"overlap accepted")
    for c in covers:
        validate([interval(k,i) for k,i in c],True)
        require(sum(charge[t] for t in c)==charge[0,0],"dropped signed rows")

    result={}
    for sign in (-1,1):
        costs={}
        for key in ids:
            h=(HI-LO)>>key[0]
            n=sum(hist[key].values())
            d0,d1=n-h*high,n-h*low
            lo_abs=0 if d0<=0<=d1 else min(abs(d0),abs(d1))
            sq=Q(max(sign*charge[key],0)**2)
            costs[key]=(max(Q(),sq-max(abs(d0),abs(d1))**2)/U,max(Q(),sq-lo_abs**2)/U)
        bounds=[]
        for edge in (0,1):
            def dp(k,i):
                v=costs[k,i][edge]
                if k==HIGH: return v
                children=dp(k+1,2*i)+dp(k+1,2*i+1)
                return children if k<LOW else min(children,v)
            exhaustive=min(sum(costs[t][edge] for t in c) for c in covers)
            require(dp(0,0)==exhaustive,"minimum sum failed")
            bounds.append(str(exhaustive))
        for c in covers:
            require(len(c)*sum(max(sign*charge[t],0)**2 for t in c)>=max(sign*charge[0,0],0)**2,"polarity dilution")
        result[str(sign)]=dict(certified_min_sum_interval=bounds)
    return dict(source_head=HEAD,source="PR303 complete signed source; no removals",horizon=X,shell_base=U,
                base=[LO,HI],scope="An intact native dyadic base in a clipped shell; finite checks do not estimate an asymptotic exponent.",
                rough_cutoff=Y,marked_primes=MARK,observed_fingerprints=sorted(actual_products),integer_sites=HI-LO,
                true_rows=len(rows),genuine_signed_charge=charge[0,0],nonzero_floor_coefficients=len(active),cut_depths=[LOW,HIGH],
                overlapping_tests=overlap_tests,complete_cuts=len(covers),nonuniform_cuts=sum(len({k for k,i in c})>1 for c in covers),
                disjoint_floor_families=len(floor_covers),disjoint_floor_divisors_each=len(ds),adaptive_projection_node_mask_checks=projections,
                density_bound="Integral-test interval for true zeta(2), rounded outwards at 50 binary places; complete Euler prime product.",
                true_density_enclosure=[str(low),str(high)],signed_stopping_sum=result)

if __name__ == "__main__":
    replay("DISJOINT_CHECK.json", solve)
