"""Explicit squarefree sampling and bounded-interval native sign certificate."""
from fractions import Fraction as F
from pathlib import Path
import sys, hashlib, json, importlib.util
from flint import arb, ctx

sys.dont_write_bytecode=True
base=Path(__file__).resolve().parent
provider=base.parent/"check_fixed_sieve.py"
spec=importlib.util.spec_from_file_location("original_fixed_sieve",provider)
prior=importlib.util.module_from_spec(spec)
spec.loader.exec_module(prior)


def main():
    ctx.prec=180
    K=1024
    Y=10**7
    flag=prior.primes_table(Y)
    nprimes=flag.count(1)
    assert nprimes==664579
    # Sum of |main coefficient| over the Bonferroni truncation tail.
    assert arb(Y).log() <17
    log_tail=arb(17) + K*(1+arb(17).log()-arb(K).log())
    assert log_tail < -3000
    # Error in the exact count of squarefree multiples, for all included subsets.
    log_error=arb(3*(K+1)).log() + K*(1+arb(F(2*nprimes,K).numerator).log()-arb(F(2*nprimes,K).denominator).log())
    assert log_error < 8500
    cost=F(0)
    k=0
    while 4**k<=Y:
        cost+=F(flag[4**k:4**(k+1)].count(1),2**k)
        k+=1
    assert cost==F(84063,128) and cost<657
    # Both U and U' can use the same coarse C^2 seminorm estimate.
    norms=[prior.source_norm(m)*prior.S/2 for m in range(4)]
    assert max(norms)<10**39
    # Common support lies in [1/2,2]. Chain/product-rule C^2 constants are below 120.
    profile_constant=120*max(norms)
    assert profile_constant < 10**42
    assert 2*10**84*F(17,27)<10**86
    assert 1314+86*arb(10).log()<1600
    assert 6*arb(-1400).exp()<1
    # Verify bound for tail of V at the earlier truncation.
    cost25=F(0)
    k=0
    while 2**(5*k)<=Y:
        cost25+=F(flag[2**(5*k):2**(5*k+5)].count(1),4**k)
        k+=1
    assert cost25<4000
    assert arb(-1000).exp()*10**82<1
    # Exact displacement of integration bounds in the Stieltjes sum.
    assert (70000-45000)//2-8500>=4000
    assert 71000-2*arb(100000).log()>70000
    assert 71000-2*arb(144550).log()>70000
    assert F(37335,100000)*144550-53890 < 78
    assert arb(78).exp()<10**34
    assert 11*10**72-2-(10**31+10**34)**2>10**73
    # The frequency band and zeta derivative are checked in the original fixed test.
    cI=arb(200).exp()/(2*arb.pi()*1000*32**2*(Y+1))
    assert cI>11*10**72
    assert 11*10**72-2-10**62>10**73
    rec={"cutoff":Y,"prime_count":nprimes,"sieve_sha256":hashlib.sha256(flag).hexdigest(),
         "original_check_sha256":hashlib.sha256(provider.read_bytes()).hexdigest(),
         "bonferroni_orders":[K-1,K],"density_tail_log_upper":str(log_tail),
         "count_error_factor_log_upper":str(log_error),
         "sum_prime_inverse_sqrt_upper":str(cost),"sum_prime_inverse_fifth_power_two_upper":str(cost25),
         "actual_density_times_energy_lower":str(cI),"signed_pointwise_interval":[70000,100000],
         "every_integer_native_terminal_window":[71000,100000],"windows":100000-71000+1,
         "with_external_upper_actual_displacement":"<0.37335",
         "extended_signed_pointwise_interval":[70000,144550],
         "extended_every_integer_native_terminal_window":[71000,144550],"extended_windows":144550-71000+1,
         "pointwise_distinct_core_covariance_strict_upper":"-10^73",
         "qualification":"Fresh finite sieve and Arb/rational constants for the paper comparison, using the original native band/verified zero-height inputs. No cofinal recurrence is asserted."}
    (base/"ROUGH_DENSITY_CONSTANTS.json").write_text(json.dumps(rec,indent=2)+"\n",encoding="utf-8")
    print("PASS",rec["windows"],"integer terminal windows; density bound",str(cI))


if __name__=="__main__":
    main()
