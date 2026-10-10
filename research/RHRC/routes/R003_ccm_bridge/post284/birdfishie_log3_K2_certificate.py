"""Outward-rounded interval enclosure for the K=2 canonical source moment
at the natural seam L=log 3. This is a falsification of a proposed
negative-side sign; it is NOT an RH proof or a contact exclusion.
"""
from mpmath import iv
iv.dps=45
PI=iv.pi
L=iv.log(3)
log2=iv.log(2)
def I(a,b=None):
    if b is None:b=a
    return iv.mpf([str(a),str(b)])

def h(w):
    a=2*PI*w
    return 4/(7*PI)*(1-iv.cos(a))*(3*iv.sin(a)-a*(2+iv.cos(a)))

def P(t):
    return iv.exp(-t/2)+iv.exp(t/2)-iv.exp(t/2)/(iv.exp(t)-iv.exp(-t))

# Integrate x=t/L. Handle small x analytically.
# On x in (0,1): |h(1-x)| <= C*x^2 with C=(8*pi/7)*(3+6*pi).
# This follows from 1-cos(2*pi*x)<=2*pi^2*x^2 and
# |3 sin a - a(2+cos a)| <=3+6*pi.
# For t in (0,1/200 * log3), |P(t)| <=1/(2t)+3,
# which follows from the exponential-series bounds for t<0.006.
EPS=iv.mpf(1)/200
C=(8*PI/7)*(3+6*PI)
# |L ∫[0,EPS] P(L*x) h(1-x) dx| <=
# C*(EPS^2/4 + L*EPS^3)
small_bound=C*(EPS**2/4+L*EPS**3)
N=2048
step=(iv.mpf(1)-EPS)/N
summed=iv.mpf(0)
for j in range(N):
    xa=EPS+j*step
    xb=EPS+(j+1)*step
    x=iv.mpf([xa.a,xb.b])
    # interval rectangle for L P(Lx)h(1-x) dx
    summed+=step*L*P(L*x)*h(1-x)
primeweight=log2/iv.sqrt(2)
# q=2 term only, q=3 term is zero because h(0)=0 exactly.
prime=primeweight*h(1-log2/L)
value=summed-prime
upper=value.b+small_bound.b
lower=value.a-small_bound.b
print('N=',N,'eps=',EPS)
print('small interval abs error bound=',small_bound)
print('prime=',prime)
print('arch bulk=',summed)
print('source H(log3)=arch - prime bounded by:')
print('lower:',lower)
print('upper:',upper)
assert lower > 0, 'Unable to certify strict positivity at log3'
print('CERTIFIED H(log3)>0 for z=(1,-4,6,-4,1); M4=24 so source pairing positive')
