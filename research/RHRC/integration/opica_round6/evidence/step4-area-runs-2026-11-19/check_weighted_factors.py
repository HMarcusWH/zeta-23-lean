"""Check the weighted finite-sum identities on actual primes and prime powers."""
from pathlib import Path
import json
from flint import arb, ctx


def main():
    ctx.prec = 160
    bound = 2000
    atoms = [[] for _ in range(bound + 1)]
    squarefree = [True] * (bound + 1)
    powers = {}
    for p in range(2, bound + 1):
        if atoms[p]:
            continue
        for n in range(p, bound + 1, p):
            atoms[n].append(p)
        for n in range(p*p, bound + 1, p*p):
            squarefree[n] = False
        power = p
        while power <= bound:
            powers[power] = p
            power *= p
    result = []
    for numerator, denominator in [(1, 2), (3, 4), (873346, 1000000)]:
        a = arb(numerator) / denominator
        logs = {p: arb(p).log() for p in powers.values()}
        weight = {u: arb(u)**(-a) for u in range(2, bound + 1)}
        twopow = arb(2)**(1-a)
        theta, psi = arb(0), arb(0)
        prime_integral, power_integral = arb(0), arb(0)
        correction_const, correction_log = arb(0), arb(0)
        prime_const = arb(0)
        tested = 0
        for x in range(2, bound + 1):
            if x > 2:
                step = (weight[x-1] - weight[x]) / a
                continuum = (arb(x)**(1-a) - arb(x-1)**(1-a)) / (1-a)
                prime_integral += theta * step - continuum
                power_integral += psi * step - continuum
            if x in powers:
                p = powers[x]
                psi += logs[p]
                if p == x:
                    theta += logs[p]
                    prime_const += logs[p] * weight[p]
                else:
                    correction_const += logs[p] * weight[x]
                    correction_log += logs[p]
            correction = (correction_const - weight[x]*correction_log)/a
            true_sum = (prime_const - weight[x]*theta)/a - (arb(x)**(1-a)-twopow)/(1-a)
            assert (true_sum - prime_integral).contains(0)
            assert (power_integral - correction - prime_integral).contains(0)
            if x >= 4:
                assert prime_integral < arb("-0.32")
            if x >= 8 and squarefree[x]:
                z = arb(x).log()
                w = sum((logs[p]*weight[p] for p in atoms[x]), arb(0))
                target = z**(1-a) - a*twopow - (1-a)*w
                score = sum((logs[p]*(weight[p]-z**(-a))/a for p in atoms[x]),arb(0)) - (z**(1-a)-twopow)/(1-a)
                assert (target + a*(1-a)*score).contains(0)
                assert target > 0
                tested += 1
        result.append({"numerator":numerator,"denominator":denominator,"integer_horizons_from_2":bound-1,"squarefree_integers_from_8":tested,"true_prime_integral_at_last":str(prime_integral)})
    data = {"qualification":"Finite 160-bit interval checks only","maximum":bound,"runs":result}
    Path(__file__).with_name("WEIGHTED_FACTORS_CHECK.json").write_text(json.dumps(data,indent=2)+"\n",encoding="utf8")
    print(json.dumps(data))


if __name__ == "__main__":
    main()
