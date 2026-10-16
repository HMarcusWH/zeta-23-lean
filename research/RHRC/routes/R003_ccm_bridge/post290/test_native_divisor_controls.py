"""Exact native versus changed-prime compatibility through n=64."""
import json
from pathlib import Path
import sympy as s

def mangoldt(n):
    factors = s.factorint(n)
    return s.log(next(iter(factors))) if len(factors) == 1 else s.Integer(0)

def check_coefficients(coefficients, maximum=64):
    residuals = {n: s.simplify(sum(coefficients(d) for d in s.divisors(n)) - s.log(n))
                 for n in range(1, maximum + 1)}
    broken = [n for n, residual in residuals.items() if residual != 0]
    return residuals, min(broken) if broken else None

def run():
    native, first = check_coefficients(mangoldt)
    assert first is None
    altered = lambda n: mangoldt(n) + (s.Integer(1) if n == 2 else s.Integer(0))
    changed, first = check_coefficients(altered)
    assert first == 2 and changed[2] == 1
    assert all(changed[n] == (1 if n % 2 == 0 else 0) for n in range(1, 65))
    # Exercise a mathematical mutation: falsely presenting altered coefficients
    # as native fails the unchanged complete divisor equation, not a label test.
    assert any(changed.values())
    return {'execution_status':'SUCCESS', 'integrity_status':'PASS',
            'scientific_disposition':'ALTERED_PRIME_REJECTED_BY_NATIVE_DIVISOR_LAW',
            'authority':'RATIONAL_EXACT_WITH_SYMBOLIC_LOG_IDENTITIES', 'claim_cap':'RH_OPEN',
            'native_source_id':'UNCHANGED_VON_MANGOLDT_INTEGER_LATTICE',
            'synthetic_source_id':'MODIFIED_LAMBDA_2_PLUS_ONE',
            'first_broken_coefficient':first, 'matched_domain':'n=1,...,64',
            'residual_at_2':'1', 'weighted_residual_at_2':'1/sqrt(2)',
            'scope':'Coefficient-level control; no negative ground, X bound, or RH exclusion is asserted.'}

if __name__ == '__main__':
    result = run()
    out = Path(__file__).parent / 'evidence/native_divisor_controls.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))
