"""Evaluate the genuine finite prime-divisor graph at four arithmetic centers."""
from fractions import Fraction
from hashlib import sha256
from math import factorial, isqrt
from pathlib import Path
import json
import sys

import flint
from flint import arb, ctx

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from check_fixed_sieve import primes_table

ctx.prec = 160
S = arb(1) / 4096
PI = arb.pi()
Y = 10_000_000
HARMONICS = 511
BOXES = 1024


def exact_floor(value):
    return int(value.floor().unique_fmpz())


def kernel_coefficients():
    # s^5 j(s*x) on [-1,1]. Even nonzero Fourier indices vanish at the first box.
    coeffs = []
    error = arb(0)
    for k in range(1, HARMONICS + 1, 2):
        freq = PI * k
        partial = arb(1)
        for d in range(1, BOXES + 1):
            angle = freq / (d * (d + 1))
            partial *= angle.sin() / angle
        coeff = (freq**2 + S**2/4)**2 * partial
        coeffs.append((k, coeff))
        error += abs(coeff) * freq**2 / (18 * BOXES**3)
    # Use the first M boxes in each omitted coefficient, all remaining factors <=1.
    m = 18
    tail = ((PI**2 + S**2/4)**2 * factorial(m) * factorial(m + 1)
            / (PI**m * (m-5) * arb(HARMONICS)**(m-5)))
    return coeffs, error + tail


def kernel(x, coeffs, error):
    theta = PI*x
    val = S**4/32
    for k, coeff in coeffs:
        val += coeff*(k*theta).cos()
    return val + arb(0, error)


def prime_power_atoms(lo, hi, table):
    atoms = {m: m for m in range(lo, hi + 1) if table[m]}
    for p in range(2, isqrt(hi) + 1):
        if not table[p]:
            continue
        m = p*p
        while m <= hi:
            if m >= lo:
                assert m not in atoms
                atoms[m] = p
            m *= p
    return atoms


def observe(center, table, coeffs, error):
    lo = exact_floor(center * (-S).exp()) + 1
    hi = exact_floor(center * S.exp())
    assert 2*Y < lo < hi < 3*Y
    atoms = prime_power_atoms(lo, hi, table)
    doubles = [m for m in range(lo + lo%2, hi + 1, 2)
               if m//2 > Y and table[m//2]]
    assert doubles and atoms and set(atoms).isdisjoint(doubles)
    arg = lambda m: (arb(center)/m).log()/S
    prime = sum((arb(p).log() * kernel(arg(m), coeffs, error) / arb(m).sqrt()
                 for m, p in atoms.items()), arb(0))
    split_atoms = [arb(2).log()*kernel(arg(m), coeffs, error)/arb(m).sqrt() for m in doubles]
    split = sum(split_atoms, arb(0))
    cross = -2*prime*split - split**2 - sum((x*x for x in split_atoms), arb(0))
    assert cross > 0 or cross < 0, "covariance sign not resolved"
    # Direct genuine group expansion, independently ordered arithmetic operations.
    core = prime + split
    direct = prime**2 - core**2 - sum((x*x for x in split_atoms), arb(0))
    assert direct.overlaps(cross)
    r, v = len(doubles), len(atoms)
    return dict(center=center, inclusive_active_integer_bounds=[lo,hi],
                prime_atoms=sum(m==p for m,p in atoms.items()), proper_powers=v-sum(m==p for m,p in atoms.items()),
                distinct_double_prime_atoms=r, signed_matrix_nonzero_ordered_entries=r*r+2*r*v,
                inertia_on_active_integer_atoms=[1,r,v-1],
                native_field_times_s5=str(prime), cancelled_double_prime_field_times_s5=str(split),
                signed_covariance_times_s10=str(cross), sign=1 if cross>0 else -1)


def main():
    centers=[21_000_000,23_000_000,25_000_000,29_000_000]
    table=primes_table(exact_floor(max(centers)*S.exp()))
    coeffs, error=kernel_coefficients()
    observations=[observe(x,table,coeffs,error) for x in centers]
    data=dict(scope="Complete actual pointwise covariance at four selected early horizons, full one-copy source. No unbounded inference.",
              cutoff=Y, source_scale="1/4096", bits=ctx.prec, flint=flint.__version__,
              harmonics=HARMONICS, boxes=BOXES, uniform_scaled_kernel_error=str(error),
              prime_table_sha256=sha256(table).hexdigest(), observations=observations)
    (HERE/"OBSERVATIONS.json").write_text(json.dumps(data,indent=2)+"\n",encoding="utf8")
    print([(r["center"],r["sign"],r["signed_covariance_times_s10"]) for r in observations])


if __name__=="__main__":
    main()
