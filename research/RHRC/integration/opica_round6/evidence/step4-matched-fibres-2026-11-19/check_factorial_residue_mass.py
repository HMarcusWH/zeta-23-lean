"""Bounded controls for the factorial residue graph. Requires python-flint."""
import hashlib
import json
from array import array
from pathlib import Path

from flint import arb, arb_mat, ctx, fmpz
import flint


ctx.prec = 192
SCALE = 10**48
BASE = Path(__file__).resolve().parent


def mobius_sieve(n):
    mu = array("b", [0]) * (n+1)
    composite = bytearray(n+1)
    primes = []
    mu[1] = 1
    for d in range(2,n+1):
        if not composite[d]:
            primes.append(d)
            mu[d] = -1
        for p in primes:
            v = d*p
            if v > n:
                break
            composite[v] = 1
            if d % p == 0:
                break
            mu[v] = -mu[d]
    return mu


def display(v):
    return v.str(29)


def knot_integral(u0, u1, f0, f1):
    """Affine interpolant on reciprocal knots, endpoints with possible Arb error."""
    width = u1-u0
    a, b = f0.mid(), f1.mid()
    perturbation = width * (f0.rad()+f1.rad())/2
    if a*b < 0:
        val = width*(a*a+b*b)/(2*(abs(a)+abs(b)))
    else:
        val = width*(abs(a)+abs(b))/2
    return val + arb(0,perturbation.abs_upper())


def primitive_cell(n, e0, e1):
    """Independent original-y antiderivative, split at the exact linear zero."""
    slope = e1-e0
    const = e0 - n*slope
    def primitive(y):
        return -arb(slope)/y-arb(const)/(2*y*y)
    left, right = primitive(n), primitive(n+1)
    if e0*e1 >= 0:
        return abs(right-left)
    root = -arb(const)/slope
    middle = primitive(root)
    return abs(middle-left)+abs(right-middle)


def native_case(l, mu):
    cap = int(fmpz(l**101).root(100))
    assert cap**100 <= l**101 < (cap+1)**100 and cap+1 <= 2*l
    endpoint = arb(l) ** (arb(101)/100) if cap**100 != l**101 else arb(cap)
    assert endpoint >= cap and endpoint < cap+1
    e = slope = 0
    b = bpos = bneg = reciprocal = signed_integral = integral_y = trap = arb(0)
    signed_trap_pos = signed_trap_neg = arb(0)
    lo = hi = positive = negative = crossings = 0
    emin = emax = 0
    for n in range(l+1,cap+1):
        term = abs(e)
        contribution = arb(term)/(n**3)
        b += contribution
        if e>0:
            bpos += contribution
        elif e<0:
            bneg += contribution
        quo, rem = divmod(term*SCALE, n**3)
        lo += quo
        hi += quo + bool(rem)
        positive += e>0
        negative += e<0
        emin, emax = min(emin,e), max(emax,e)
        slope += mu[n]
        next_e = e+slope
        if n < cap:
            left, right = arb(1)/(n+1), arb(1)/n
            f0, f1 = left*next_e, right*e
            crossings += e*next_e<0
            reciprocal += knot_integral(left,right,f0,f1)
            signed_integral += (right-left)*(f0+f1)/2
            signed_trap_pos += (right-left)*(max(e,0)*right+max(next_e,0)*left)/2
            signed_trap_neg += (right-left)*(max(-e,0)*right+max(-next_e,0)*left)/2
            integral_y += primitive_cell(n,e,next_e)
            trap += (right-left)*(abs(f0)+abs(f1))/2
            e = next_e
    assert reciprocal.overlaps(integral_y) and (bpos+bneg).overlaps(b)
    fullpos, fullneg = (reciprocal+signed_integral)/2, (reciprocal-signed_integral)/2
    assert not(fullpos > signed_trap_pos or fullneg > signed_trap_neg)
    assert not(b < arb(lo)/SCALE or b > arb(hi)/SCALE)
    assert not (reciprocal > trap or 2*reciprocal < trap)
    assert not (4*reciprocal < b)
    if cap >= l+1:
        eu = e + (endpoint-cap)*slope
        right, left = arb(1)/cap, 1/endpoint
        collar = knot_integral(left,right,left*eu,right*e)
        signed_collar = (right-left)*(left*eu+right*e)/2
        if slope and (eu>0 or eu<0 or eu.is_zero()):
            linear_const = e-cap*slope
            def primitive(y):
                return -arb(slope)/y-arb(linear_const)/(2*y*y)
            lower_primitive, upper_primitive = primitive(cap),primitive(endpoint)
            if (e>0 and eu<0) or (e<0 and eu>0):
                middle = primitive(-arb(linear_const)/slope)
                independent = abs(middle-lower_primitive)+abs(upper_primitive-middle)
            else:
                independent = abs(upper_primitive-lower_primitive)
            assert independent.overlaps(collar)
    else:
        collar = arb(0)  # The native interval is empty.
        signed_collar = arb(0)
    full = reciprocal+collar
    return dict(L=l,integer_cap=cap,endpoint=display(endpoint),
                integer_terms=max(0,cap-l),integer_signs=dict(positive=positive,negative=negative,
                zero=max(0,cap-l)-positive-negative),integer_extrema=[emin,emax],
                sign_crossings_inside_complete_cells=crossings,
                B=display(b),B_scaled_integer_enclosure=[str(lo),str(hi)],
                B_positive=display(bpos),B_negative=display(bneg),
                reciprocal_complete_cells=display(reciprocal),original_y_complete_cells=display(integral_y),
                reciprocal_complete_positive=display(fullpos),reciprocal_complete_negative=display(fullneg),
                complete_positive_trapezoid=display(signed_trap_pos),complete_negative_trapezoid=display(signed_trap_neg),
                trapezoid_of_absolute_endpoints=display(trap),fractional_last_cell=display(collar),
                full_native_integral=display(full),
                full_native_positive_integral=display(fullpos+(collar+signed_collar)/2),
                full_native_negative_integral=display(fullneg+(collar-signed_collar)/2),
                full_integral_over_B=display(full/b) if b>0 else None)


def calibration(l, mu, centres):
    a = {m:-arb(mu[m])/m for m in range(2,l+1) if mu[m]}
    def col(m):
        v = arb(m)
        return [arb(1),v.log(),1-v.sqrt(),v-1]
    targets = [arb(1),arb(1),1/arb("0.5").zeta(), arb(2)]
    rhs = [t-sum((v*col(m)[i] for m,v in a.items()),arb(0))
           for i,t in enumerate(targets)]
    extras = {}
    for r in centres:
        nodes = [r*4**i for i in range(4)]
        mat = arb_mat([[col(m)[i] for m in nodes] for i in range(4)])
        sol = mat.solve(arb_mat([[v] for v in rhs]))
        for k,m in enumerate(nodes):
            extras[m] = extras.get(m,arb(0)) + sol[k,0]/len(centres)
    a.update(extras)
    for i,t in enumerate(targets):
        assert sum((v*col(m)[i] for m,v in a.items()),arb(0)).overlaps(t)
    return a, sorted(extras)


def actual_wide(l, centres, mu):
    a, nodes = calibration(l,mu,centres)
    limit = max(nodes)+3*l+1
    # Independent divisor ramps. For j>=2, r(j)=-1+sum_{m|j}m*a_m;
    # the unit residual is exactly zero by the mass equation.
    r = [arb(-1) for _ in range(limit+1)]
    r[1] = arb(0)
    for m,v in a.items():
        coefficient = m*v
        for j in range(m,limit+1,m):
            r[j] += coefficient
    e = slope = arb(0)
    mu_e = mu_slope = 0
    b = area = trap = arb(0)
    near_l = int(fmpz(l**101).root(100))
    native_b = arb(0)
    witnesses = {}
    targets = {l+1,2*l,2*l+1,limit} | set(nodes) | {m+1 for m in nodes}
    old = arb(0)
    for n in range(1,limit+1):
        modular = arb(-1)+sum((v*((n%m)*(m-n%m)) for m,v in a.items()),arb(0))/2
        assert modular.overlaps(e)
        if n<=2*l:
            assert modular.contains(mu_e) and e.contains(mu_e)
        if n in targets:
            # Direct definition of J_m, summed using integer triangular sums.
            j_val = arb(0)
            for m,v in a.items():
                k = n//m
                integral_j = n*(n-1)//2 - m*(n*k-m*(k*(k+1)//2))
                j_val += v*integral_j
            direct = n-1-j_val
            assert direct.overlaps(modular) and direct.overlaps(e)
            witnesses[str(n)] = dict(modular=display(modular),direct=display(direct))
        if n>=l+1:
            b += abs(modular)/(n**3)
            if n<=near_l:
                native_b += abs(modular)/(n**3)
            if n>l+1:
                left, right = arb(1)/n,arb(1)/(n-1)
                f0, f1 = left*modular,right*old
                area += knot_integral(left,right,f0,f1)
                trap += (right-left)*(abs(f0)+abs(f1))/2
        old = modular
        slope += r[n]
        e += slope
        if n>l and n<2*l:
            mu_slope += mu[n]
            mu_e += mu_slope
    assert not (area > trap or 2*area < trap or 4*area < b)
    return dict(L=l,centres=centres,exceptional_nodes=nodes,
                native_cap=near_l,diagnostic_cap=limit,all_integer_knot_comparisons=limit,
                integer_mu_identity_checked_through=2*l,
                native_B_from_modular=display(native_b),wider_B_from_modular=display(b),
                wider_integral=display(area),wider_trapezoid=display(trap),
                wider_integral_over_B=display(area/b),selected_direct_ramp_witnesses=witnesses)


def main():
    ls = [9,32,100,257,1000,4096,10000,65536,100000,262144,1000000]
    mu = mobius_sieve(int(fmpz(max(ls)**101).root(100))+1)
    native = [native_case(l,mu) for l in ls]
    # At L=100 the native interval already has a nonzero integer knot.
    single = actual_wide(100,[201],mu)
    distributed = actual_wide(100,list(range(207,301,9)),mu)
    for sample in (single,distributed):
        n = next(r for r in native if r["L"]==sample["L"])
        assert arb(sample["native_B_from_modular"]).overlaps(arb(n["B"]))
    receipt = dict(scope="Finite calculation with fixed native delta=1/100. Wide controls cross calibration nodes and are separately labeled. No fitted exponent.",
                   source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   flint_version=flint.__version__,precision_bits=ctx.prec,
                   integer_weight_scale=str(SCALE),
                   native_convention="knot L+1 through floor(L^(101/100)) inclusive, empty if floor < L+1",
                   integral_convention="Integral from L+1 to L^(101/100) of |E(y)|/y^3 dy via affine reciprocal knots, empty if upper < lower",
                   native=native,wide=[single,distributed])
    out = BASE/"FACTORIAL_RESIDUE_MASS_CHECK.json"
    out.write_text(json.dumps(receipt,indent=2)+"\n",encoding="utf8")
    print("native:",[(r["L"],r["integer_terms"],r["sign_crossings_inside_complete_cells"]) for r in native])
    print("wide:",[(r["L"],r["all_integer_knot_comparisons"],len(r["exceptional_nodes"])) for r in receipt["wide"]])


if __name__=="__main__":
    main()
