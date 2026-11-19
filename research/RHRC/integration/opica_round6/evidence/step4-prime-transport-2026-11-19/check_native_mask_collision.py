"""Two genuine same-node positive rough targets rejected by the exact GCD cutoff."""
from hashlib import sha256
from math import gcd, isqrt
from pathlib import Path
import json

import flint
from flint import fmpz


def check():
    # The independently verified large Mersenne prime is an explicit external input.
    large_exponent = 1_398_269
    cofactor_exponent = 1_279
    common_prime = (1 << large_exponent) - 1
    cofactors = [(1 << cofactor_exponent) - offset for offset in (157, 1)]
    assert all(fmpz(m).is_prime() == 1 for m in cofactors)
    labels = [common_prime * m for m in cofactors]
    assert common_prime > max(cofactors) and labels[0] < labels[1]
    assert gcd(*labels) == common_prime

    cutoff_exponent = 100 * ((large_exponent + cofactor_exponent + 99) // 100)
    shell_exponent = labels[0].bit_length() - 1
    assert (labels[1].bit_length() - 1) == shell_exponent
    assert 99 * cutoff_exponent // 100 <= shell_exponent < cutoff_exponent
    assert labels[0] > (1 << (99 * cutoff_exponent // 100))
    assert max(m ** 1000 for m in cofactors) <= (1 << cutoff_exponent)
    assert min(cofactors) > cutoff_exponent**2
    assert common_prime >= 1 << (cutoff_exponent // 100)

    s = 1 + isqrt(cutoff_exponent - 1)
    base_exponent = shell_exponent - s
    base_indices = [(n - (1 << shell_exponent)) >> base_exponent for n in labels]
    assert base_indices[0] == base_indices[1] == (1 << s) - 1
    # Exactly which successive dyadic ancestors the edge activates, including base.
    last_shared_depth = 0
    while (labels[0] >> (base_exponent - last_shared_depth - 1)
           == labels[1] >> (base_exponent - last_shared_depth - 1)):
        last_shared_depth += 1
    return {
        "qualification": "Exact two-label arithmetic and original tree/mask geometry; unmasked covariance and the full matching were not evaluated.",
        "cutoff_X": f"2^{cutoff_exponent}",
        "kappa": "1/1000",
        "alpha_fixture": "1/125 (only kappa is used by these two mandatory targets)",
        "rough_cutoff": cutoff_exponent**2,
        "common_prime": f"2^{large_exponent}-1",
        "common_prime_authority": "https://www.mersenne.org/primes/?press=M1398269",
        "cofactors": ["2^1279-157", "2^1279-1"],
        "cofactor_primality": f"python-flint {flint.__version__} fmpz.is_prime() returned 1 for both",
        "labels": ["(2^1398269-1)(2^1279-157)", "(2^1398269-1)(2^1279-1)"],
        "mobius_signs": [1, 1],
        "gcd_equals_common_prime": True,
        "mask_rejects": True,
        "s": s,
        "shell": f"[2^{shell_exponent}, 2^{shell_exponent + 1})",
        "common_base_cell": f"last of 2^{s}; length 2^{base_exponent}",
        "last_shared_dyadic_depth_relative_to_base": last_shared_depth,
        "ordered_signed_removed_weight_at_base": f"2/2^{shell_exponent}",
        "ordered_signed_removed_weight_all_levels": f"(4-2^(1-{last_shared_depth}))/2^{shell_exponent}",
        "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
    }


if __name__ == "__main__":
    output = Path(__file__).with_name("NATIVE_MASK_COLLISION.json")
    output.write_text(json.dumps(check(), indent=2) + "\n", encoding="utf-8")
