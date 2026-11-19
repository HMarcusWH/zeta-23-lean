"""Certificate for one fixed small-prime cutoff in the native covariance sign test."""
from fractions import Fraction as F
from hashlib import sha256
from math import factorial, isqrt
from pathlib import Path
import json
import flint
from flint import arb, acb, acb_series, ctx

Y=10_000_000
S=4096
ctx.prec=160
ctx.cap=3


def primes_table(top):
    flag=bytearray([1])*(top+1)
    flag[:2]=bytes(2)
    for p in range(2,isqrt(top)+1):
        if flag[p]:
            flag[p*p::p]=bytes((top-p*p)//p+1)
    return flag


def source_norm(order):
    def derivative(m):
        # L1 of q^(m), scaled from a support interval of length 2.
        return S**m*factorial(m)*factorial(m+1)*(m+1)*(m+2)
    return derivative(order+4)+F(1,2)*derivative(order+2)+F(1,16)*derivative(order)


def main():
    flag=primes_table(Y)
    low_penalty=2*sum((F(1,isqrt(p)-1) if p>=4 else F(3))
                      for p in range(2,3000) if flag[p])
    high_count=flag[1_000_000:].count(1)
    root_upper=isqrt(Y)+1
    gain=F(3*high_count,2*root_upper)-low_penalty
    assert high_count==586081
    assert arb(199)/1000*arb(3000).log()>arb.pi()/2
    assert arb(199)/1000*arb(1_000_000).log()>5*arb.pi()/6
    assert arb(1)/5*arb(Y).log()<7*arb.pi()/6
    assert arb(1)/5*arb(Y).log()<3*arb.pi()/2
    assert gain>200
    # Whole closed real-frequency interval [0.199,0.200] in a single ball.
    band=arb("0.1995 +/- 0.0005")
    derivative=acb_series([acb(arb("0.5"),band),1]).zeta()[1]
    assert abs(derivative)>1
    assert 1-F(1,2)*F(1,5*S)**2>F(1,2)
    upper=source_norm(2)+2*source_norm(0)
    assert upper<10**31
    # |Uhat|>1/32. Positive frequency bandwidth 1/1000, density >=1/(Y+1).
    lower=arb(200).exp()/(2*arb.pi()*1000*32**2*(Y+1))
    assert lower>10**73
    # Weighted tail norm for the finite native sign gate.
    cost=F(0)
    k=0
    while 2**(5*k)<=Y:
        count=flag[2**(5*k):min(Y+1,2**(5*k+5))].count(1)
        cost+=F(count,4**k)
        k+=1
    assert cost<4000
    assert 10**82*arb(-400).exp()<1
    m0=isqrt(3*10**12)
    assert F(15,m0+2)<F(1,32)-F(1,33)
    assert 3000*34<arb(12).exp() and 15*arb(m0+2).log()<216
    assert 12+216-F(m0,32)<-53890
    assert arb(5).exp()<150
    assert upper+1<10**31
    assert lower*(Y+1)>10**80
    # Elementary sampling-envelope bound for U. Scaled suprema of j, j' and j''.
    jsup=[source_norm(m)*S/2 for m in range(3)]
    assert max(jsup)<10**34
    assert jsup[0]<10**24
    assert F(4,5)*(10**80-1)/100000-24*10**62>10**74
    assert F(125506,1000000)*10/9<F(1,5)
    assert arb(10).log()<800 and arb(Y).log()+arb(10).log()<8000
    assert arb(144000).log()*2<24
    assert F(374,1000)*144000-53890==-34
    assert F(4,5)*(10**80-1)/144000-24*10**62>10**74
    assert flag.count(1)==664579
    end=1100000
    assert arb(4)*(arb(2)**664579+2)*end*arb(-(end-42000)//2).exp()<arb(-60000).exp()
    assert arb(4)*(10**80-1)/(5*end)>2*arb(end).log()*10**72
    assert (10**80-1)>2*(Y+1)*10**72
    assert arb(10**36-10**31).log()>82
    tracker_upper=F(9908119238306612133369374975000622988619121777878229799765263366946606045502455625911569003364955967645745531862430068266267717,
                    11345012023616779600791582323373494582287250283647959965785871011074347975117040113347744503437234376916434871293982689424818700)
    assert tracker_upper-F(1,2)<F(37335,100000)
    def slab_threshold(m):
        return arb(m)/32-17*arb(m+2).log()+(arb(10)**35/3000).log()
    assert slab_threshold(m0)>arb(m0+1)/33
    assert F(1,32)-F(1,33)>F(17,m0+2)
    assert slab_threshold(12*144000)>arb(37335)*144000/100000
    assert F(12,32)-F(37335,100000)>F(204,12*144000+2)
    result={"cutoff":Y,"source_scale":"1/4096","prime_flags_sha256":sha256(flag).hexdigest(),
            "high_prime_count":high_count,"threshold_prime_range":[1_000_000,Y],
            "negative_log_product_cost_upper":str(low_penalty),
            "squared_Euler_product_log_lower_above":200,
            "actual_zeta_derivative_modulus_enclosure":str(abs(derivative)),
            "frequency_band":["0.199","0.200"],"line_response_bound_strict":"1e31",
            "same_group_limiting_energy_lower_strict":"1e73",
            "numeric_lower_from_certificate":str(lower),"flint":flint.__version__,"bits":ctx.prec,
            "consecutive_integer_horizons":[50000,100000],"with_external_ceiling":[50000,144000],
            "signed_covariance_upper_strict":"-1e74",
            "upper_sum_p_minus_two_fifths":str(cost),
            "native_one_copy_spectral_tail_log_upper":-53890,
            "uniform_diagonal_mean_lower_after_50000":"1e72",
            "opposite_sign_forces_a_single_zero_in":"3e12 < abs(Im rho) < (12 n)^2 and n*(Re rho-1/2) > sqrt(abs(Im rho))/33",
            "qualification":"Finite prime sieve, exact rational constants and Arb ball bounds. Uses analytic identities specified in the paper. No finite check of the missing cofinal sign."}
    Path(__file__).with_name("FIXED_SIEVE_CONSTANTS.json").write_text(
        json.dumps(result,indent=2)+"\n",encoding="utf8")
    print("PASS",high_count,"primes in the positive range;",str(lower))


if __name__=="__main__":
    main()
