"""Exact common-row checks for the two prime sums and their PNT limit."""
from fractions import Fraction as F
import json
from pathlib import Path
from flint import fmpz


def first_primes(lo, hi, limit):
    n = fmpz(lo)
    answer = []
    while len(answer) < limit:
        n += 1
        if n > hi:
            break
        if n.is_prime():
            answer.append(int(n))
    return answer


def main():
    a,b,c,d = F(13,25),F(3,5),F(11,10),F(13,10)
    integral = ((b-a)*(d-c) - (b*b-a*a)*(d*d-c*c)/2
                + (b**3-a**3)*(d**3-c**3)/9)
    rows = []
    for x in [10**18,10**20,10**24,10**28]:
        L = int(fmpz(x**11).root(100))
        M = int(fmpz(x**37).root(100))
        assert L**100 <= x**11 < (L+1)**100 and M**100 <= x**37 < (M+1)**100
        ps = first_primes(int(a*x/L),int(b*x/L),6)
        qs = first_primes(int(c*L),int(d*L),6)
        assert ps and qs and all(p > 64*(2*M+1) for p in ps)
        assert all(L < q < 2*L+1 for q in qs)
        products = {p*q for p in ps for q in qs}
        assert len(products) == len(ps)*len(qs)
        assert all(x-n >= F(22,100)*x for n in products)
        assert all(p < F(x,L+1) and p**100 > x**64 for p in ps)
        assert all(q < F(x,M+1) and q**40 > x for q in qs)
        rows.append({'x':str(x),'first_cutoff':L,'second_cutoff':M,'p':ps,'q':qs,'distinct_products':len(products)})
    result = {'integral':str(integral),'minimum_positive_integrand':str((1-b*d)**2),'precision':'exact integers and fractions','rows':rows}
    Path(__file__).with_name('SHARED_SEMIPRIMES_CHECK.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(str(integral),sum(row['distinct_products'] for row in rows))


if __name__=='__main__':
    main()
