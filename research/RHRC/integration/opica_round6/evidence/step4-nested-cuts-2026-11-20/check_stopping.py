"""Exact signed-cell checks for the nested parity obstruction."""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from math import isqrt, prod
from finite_replay import native, replay, require

HEAD = "a6a001fd570cd7cf9b97fdad59e373760a3153ec"


def cut_value(cost, start, end):
    def recurse(k, i):
        if k == end:
            return cost[k,i]
        children = max(recurse(k+1,2*i),recurse(k+1,2*i+1))
        return children if k < start else min(cost[k,i],children)
    return recurse(0,0)

def path_value(cost, start, end):
    return max(min(cost[k,i>>(end-k)] for k in range(start,end+1)) for i in range(1<<end))

def exhaustive():
    checks = 0
    for values in product((-1,0,1),repeat=8):
        for sign in (-1,1):
            costs={}
            for k in range(4):
                w=8>>k
                for i in range(1<<k):
                    f=sum(values[i*w:(i+1)*w])
                    costs[k,i]=max(sign*f,0)**2
            z=cut_value(costs,1,3)
            require(z==path_value(costs,1,3),"complete cut")
            checks+=1
    bad={(0,0):0,(1,0):16,(1,1):0}
    require(cut_value(bad,1,1)==16 and min(bad[1,0],bad[1,1])==0,"incomplete cover control")
    return checks

def prime_factors(n):
    factors=[]
    d=2
    while d*d<=n:
        while n%d==0:
            factors.append(d)
            n//=d
        d+=1
    if n>1:
        factors.append(n)
    return factors

def sqrt_ceil(n):
    s=isqrt(n)
    return s+int(s*s<n)

def density_bounds(y):
    # The integral test encloses the exact reciprocal zeta(2) with rationals.
    m=64
    part=sum((Q(1,i*i) for i in range(1,m+1)),Q())
    weights=prod(Q(p,p+1) for p in range(2,y+1) if prime_factors(p)==[p])
    return weights/(part+Q(1,m)), weights/(part+Q(1,m+1))

def cell_calculation(mod):
    x=1656575
    lo,hi=1441792,1474560
    j=lo.bit_length()-1
    u=1<<j
    y=(x-1).bit_length()**2
    xs=sqrt_ceil(x.bit_length()-1)
    require(hi-lo==1<<(j-xs) and lo>=mod.first_terminal(x) and hi-1<=x,"full base")
    require(u**100<=x**99,"this shell is clipped")
    rows=[]
    for n,sign,*_ in mod.vertex_rows(x,1):
        if lo<=n<hi:
            fs=prime_factors(n)
            require(len(set(fs))==len(fs) and min(fs)>y and (-1)**len(fs)==sign,"source row")
            rows.append((n,sign,prod(p for p in fs if p<=2000)))
    targets=[n for n,s,f in rows if f>1450000]
    donors=[n for n,s,f in rows if s==-1][:len(targets)]
    removed=set(targets+donors)
    require(len(targets)==len(donors)==231 and len(removed)==462,"auxiliary matching")
    d_lo,d_hi=density_bounds(y)
    end=5
    raw=Counter()
    charge=Counter()
    deepest=[[] for _ in range(1<<end)]
    for row in rows:
        n,sgn,f=row
        for k in range(end+1):
            i=(n-lo)//((hi-lo)>>k)
            raw[k,i]+=1
            if n not in removed:
                charge[k,i]+=sgn
        if n not in removed:
            deepest[(n-lo)//((hi-lo)>>end)].append(row)
    def cancel(items):
        plus=sorted(r for r in items if r[1]==1)
        minus=sorted(r for r in items if r[1]==-1)
        small=min(len(plus),len(minus))
        return plus[small:]+minus[small:]
    residual=[cancel(bucket) for bucket in deepest]
    for depth in range(end,0,-1):
        residual=[cancel(residual[i]+residual[i+1]) for i in range(0,len(residual),2)]
    inherited=residual[0]
    require(len(inherited)==-charge[0,0] and all(s==-1 for _,s,_ in inherited),"root residual")
    fingerprint,count=Counter(f for _,_,f in inherited).most_common(1)[0]
    carried=[n for n,_,f in inherited if f==fingerprint]
    path=[]
    idx=0
    for k in range(end+1):
        width=(hi-lo)>>k
        require((1<<k)*len(carried)>=count and -charge[k,idx]>=len(carried),"sign carrier invariant")
        path.append([k,lo+idx*width,len(carried),charge[k,idx]])
        if k<end:
            mid=lo+idx*width+width//2
            left=[n for n in carried if n<mid]
            right=[n for n in carried if n>=mid]
            go_right=len(right)>len(left)
            carried=right if go_right else left
            idx=2*idx+int(go_right)
    out={}
    for sign in (-1,1):
        bounds=[{},{}]
        charged={}
        for k in range(end+1):
            width=(hi-lo)>>k
            for i in range(1<<k):
                f=charge[k,i]
                dl=raw[k,i]-width*d_hi
                dh=raw[k,i]-width*d_lo
                max_abs=max(abs(dl),abs(dh))
                min_abs=0 if dl<=0<=dh else min(abs(dl),abs(dh))
                sq=max(sign*f,0)**2
                charged[k,i]=Q(sq,u)
                for bound,d in zip(bounds,(max_abs,min_abs)):
                    bound[k,i]=max(Q(0),Q(sq)-d*d)/u
        for b in [*bounds,charged]:
            require(cut_value(b,2,end)==path_value(b,2,end),"observed cut vs path")
        out[str(sign)]={"normalized_charge_square":str(cut_value(charged,2,end)),
                        "opposed_product_lower":str(cut_value(bounds[0],2,end)),
                        "opposed_product_upper":str(cut_value(bounds[1],2,end))}
    return {"X":x,"y":y,"U":u,"cell":[lo,hi],"raw":len(rows),"removed_pairs":len(targets),
            "remaining":len(rows)-len(removed),"root_charge":charge[0,0],
            "path_depths":[2,end],"optimum":out,"root_residuals":len(inherited),
            "inherited_fingerprint":fingerprint,"count_with_fingerprint":count,"path":path,
            "actual_final_label":min(carried),"density_enclosure":list(map(str,(d_lo,d_hi))),
            "scope":"One intact native base cell inside a clipped shell. The auxiliary within-base matching is fixed by the published finite fingerprint fixture. The finite test does not sample a whole terminal shell."}

def grid(mod):
    x=65537
    s=sqrt_ceil(x.bit_length()-1)
    paper=sqrt_ceil((x-1).bit_length())
    require((s,paper)==(4,5),"rounding controls")
    rows=list(mod.vertex_rows(x,1))
    tests=[]
    for j in sorted({n.bit_length()-1 for n,*_ in rows}):
        u=1<<j
        d=j-s
        if d<2:
            continue
        def levels(base):
            depth=j-base
            e=[Q() for _ in range(depth+1)]
            for k in range(depth+1):
                buckets=Counter()
                for n,sgn,*_ in rows:
                    if u<=n<2*u:
                        buckets[n//(1<<(depth-k))]+=sgn
                e[k]=Q(sum(max(-f,0)**2 for f in buckets.values()),u*(1<<k))
            return e
        old,new=levels(s),levels(paper)
        require(all(new[k]==2*old[k+1] for k in range(len(new))),"level identity")
        v=sum(e for k,e in enumerate(old) if 2*k<d)
        v2=sum(e for k,e in enumerate(new) if 2*k<d-1)
        mid=old[d//2] if d%2==0 else 0
        require(mid<=1 and v2==2*(v-old[0]+mid) and v<=Q(5,2)*v2 and v2<=2*v+2,"coarse identity")
        tests.append({"j":j,"native":str(v),"shifted":str(v2),"extra_middle":str(mid)})
    return {"X":x,"native_s":s,"paper_s":paper,"true_y":(x-1).bit_length()**2,"negative_polarity":tests}

def calculate():
    mod = native()
    return {"source": HEAD, "exhaustive_ternary_8_leaf_cases_with_both_signs": exhaustive(),
            "finite_native_cell": cell_calculation(mod), "rounding_boundary": grid(mod)}


if __name__ == "__main__":
    replay("STOPPING_CHECK.json", calculate)
