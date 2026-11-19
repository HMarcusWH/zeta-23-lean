"""Interval sample of the complete six-shell arithmetic at genuine apertures."""
import json
from pathlib import Path
from flint import arb, fmpq, ctx

ctx.prec=144
scale=arb(fmpq(1,4096))
sigma_sq=scale**2 * (arb.pi()**2/3-3)/3
sym=arb(0,1)
qrange=scale*sym
poly=[0, -864, 8136, -13384, 6704, -1184, 64]


def deriv_poly(coeff):
    out=[0]*(len(coeff)+1)
    for i,q in enumerate(coeff):
        out[i]+=(-fmpq(3,2)-2*i)*q
        out[i+1]+=2*q
    return out


def evaluate(c,a):
    v=arb(0)
    for x in reversed(c):
        v=v*a+arb(x)
    return v


p2=deriv_poly(deriv_poly(poly))
p4=deriv_poly(deriv_poly(p2))
facA=(2*qrange).exp()
facU=(3*qrange/2).exp()
bds=[(133,134),(817,818),(2387,2388),(5190,5191),(9971,9972)]
margin=(2*scale).exp()


def shell(a,val):
    count=0
    for l,r in bds:
        if a<arb(l)/1000/margin:
            return count
        if a>arb(r)/1000*margin:
            count+=1
            continue
        if val>0:
            return count if count%2 else count+1
        if val<0:
            return count+1 if count%2 else count
        raise ValueError("undecided sign in a transition shell")
    return count


def values(X):
    M=12*X
    logs=[arb(0)]+[arb(k).log() for k in range(1,M+1)]
    c=[arb(0) for _ in range(M+1)]
    sieve=bytearray([1])*(M+1)
    sieve[:2]=bytes(2)
    for p in range(2,M+1):
        if not sieve[p]:
            continue
        for m in range(p*p,M+1,p):
            sieve[m]=0
        k=p
        while k<=M:
            for d in range(1,M//k+1):
                c[k*d]+=logs[p]/d
            k*=p
    B=[arb(0) for _ in range(6)]
    I=arb(0)
    F=arb(0)
    for m in range(2,M+1):
        y=arb(m)/X
        a=arb.pi()*y*y
        v0=y*y.sqrt()*(-a).exp()
        aJ=a*facA
        fourth=abs(v0*facU*(a-aJ).exp()*evaluate(p4,aJ)).upper()
        W=v0*(evaluate(poly,a)+sigma_sq/2*evaluate(p2,a))+sym*scale**4*fourth/24
        h=shell(a,W)
        b=logs[m]-c[m] if not sieve[m] else arb(0)
        weight=W/arb(m).sqrt()
        I+=logs[m]*weight
        F+=c[m]*weight
        B[h]+=b*abs(weight)
    # For y=m/X>=12 and |v|<=s, a e^(2v) is in [3y²,4y²].
    # The sum of the absolute coefficients of P is <40,000 and its degree is six.
    # Each tail is at most 1e9 X^{-1/2} sum(log(m) y^13 exp(-3 y²)).
    # log(m)<=X y, y^14<=exp(y²/2), and exp(-3y²)<=exp(-288)exp(-y²).
    # Summing the remaining exp(-y²/2)<=exp(-y) costs at most X.
    tail=arb(10**9)*arb(X)*arb(X).sqrt()*arb(-288).exp()
    assert tail<arb(10)**(-100)
    I+=sym*tail
    F+=sym*tail
    B[5]+=sym*tail
    D=B[0]+B[2]+B[4]-B[1]-B[3]-B[5]
    assert (I+D-F).contains(0)
    def val(a):
        return a.str(16)
    return dict(X=X,last_index=M,complete_shell_mass=[val(x) for x in B],
                deficit=val(D),integer_observer=val(I),visible_observer=val(F),
                visible_sign=1 if F>0 else -1 if F<0 else 0,
                interval_method="Arb 144-bit balls, genuine even-seed variance, fourth derivative support bound, all remaining indices bounded")


if __name__=="__main__":
    out=[values(2**k) for k in range(4,12)]
    Path(__file__).with_name("SIX_SHELL_SAMPLES.json").write_text(json.dumps(out,indent=2)+"\n")
    for row in out:
        print(row["X"],row["deficit"],row["visible_observer"])
