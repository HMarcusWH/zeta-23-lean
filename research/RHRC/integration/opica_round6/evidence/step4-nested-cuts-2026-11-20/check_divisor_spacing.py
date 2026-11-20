"""Independent finite algebra checks for the two paper estimates, not an asymptotic test."""
from collections import Counter
from fractions import Fraction
from math import gcd,isqrt,prod
import itertools
from finite_replay import replay

def prime_factors(n):
    p=2
    out=[]
    while n>1 and p*p<=n:
        while n%p==0:
            out.append(p)
            n//=p
        p+=1
    if n>1:
        out.append(n)
    return out

def divisors(factors):
    parts=[1]
    for p in factors:
        parts += [p*k for k in parts]
    return sorted(set(parts))

def need(condition,reason):
    if not condition:
        raise ArithmeticError(reason)

def check_exponents():
    u=Fraction(5,14)
    lam=Fraction(4,5)
    table=[(0,Fraction(1,4),1,0),(Fraction(1,4),u,-Fraction(1,3),Fraction(1,3)),
           (u,Fraction(3,7),-1,Fraction(4,7)),(Fraction(3,7),Fraction(1,2),-2,1)]
    at=set()
    for lo,hi,slope,offset in table:
        for t in [lo,hi]:
            at.add((t,(lam+slope)*t+offset))
    need(max(exp for _,exp in at)==Fraction(1,2),"incorrect worst exponent")
    peaks=sorted(t for t,exp in at if exp==Fraction(1,2))
    need(peaks==[u],"incorrect maximizing divisor scale")
    return {"critical_pairs":[[str(a),str(b)] for a,b in sorted(at)],"worst_u":str(u)}

def check_floors():
    examples=0
    for U in (512,2048,8192):
        for offset in (0,1,13,71):
            x=U+offset
            for H in (1,7,32,128):
                for P in (2,4,8,16,32):
                    for h in (1,2,3,7):
                        direct=sum(1 for k in range(P+1,2*P+1)
                                   for m in range(1,2*U//(k*(k+h))+1)
                                   if x<m*k*(k+h)<=x+H)
                        forward=sum((x+H)//(k*(k+h))-x//(k*(k+h)) for k in range(P+1,2*P+1))
                        # Enlarging the m range further than in the proof makes a simple independent check.
                        def end(z,m):
                            return (isqrt(h*h+4*(z//m))-h)//2
                        dual=sum(end(x+H,m)-end(x,m) for m in range(1,(x+H)//((P+1)*(P+1+h))+1))
                        need(forward==direct and dual>=direct,"integer endpoint failed")
                        examples+=1
    return examples

def check_divisors_and_signed():
    U=4096
    factors={n:prime_factors(n) for n in range(U,2*U)}
    rows={n:f for n,f in factors.items() if len(f)==len(set(f)) and all(p>5 for p in f)}
    collision={}
    for n,ps in rows.items():
        ds=divisors(ps)
        violations=[(a,b) for a,b in itertools.combinations(ds,2) if (b-a)**4<=a**3]
        witnesses=[]
        for a,b in violations:
            k,l=a//gcd(a,b),b//gcd(a,b)
            need(k>5 and (l-k)**4<=k**3 and n%(k*l)==0,"failed reduced divisor witness")
            witnesses.append((k,l))
        if witnesses:collision[n]=witnesses
    # Thin undirected graph chosen in advance. Small threshold creates 3-way or 4-way overlaps.
    graph=lambda p,q: abs(p-q)<=12
    naive=Counter()
    ie=Counter()
    multiplicity=Counter()
    for n,ps in rows.items():
        edges=[(a,b) for a,b in itertools.combinations(ps,2) if graph(a,b)]
        mu=(-1)**len(ps)
        if edges:
            naive[n//64]+=mu
            multiplicity[len(edges)]+=1
        for r in range(1,len(edges)+1):
            for subset in itertools.combinations(edges,r):
                product=prod(set(itertools.chain.from_iterable(subset)))
                coprime_cofactor=n//product
                need(gcd(product,coprime_cofactor)==1,"cofactor not coprime")
                ie[n//64]+=(-1)**(r-1+len(prime_factors(product))+len(prime_factors(coprime_cofactor)))
    need(all(naive[k]==ie[k] for k in naive.keys()|ie.keys()),"overlapping prime graph IE failed")
    need(any(k>1 for k in multiplicity),"no overlap stress")
    return {"U":U,"roughness":5,"actual_squarefree_rows":len(rows),"bad_divisor_labels_at_fixed_lambda_3_over_4":len(collision),
            "signed_collision_sum":sum(ie.values()),"source_labels_by_number_of_flagged_edges":dict(sorted(multiplicity.items())),
            "all_64_cells_agree":True}

def calculate():
    return {"scope":"Finite integer counting on specified test shells and rational exponent audit. No execution of the asymptotic selector or evidence for the missing signed upper.",
            "exponents":check_exponents(),"floor_checks":check_floors(),"arithmetic":check_divisors_and_signed()}


if __name__ == "__main__":
    replay("DIVISOR_SPACING_CHECK.json", calculate)
