from __future__ import annotations

from fractions import Fraction


def cubic_contact(t: Fraction) -> tuple[Fraction, Fraction, Fraction]:
    """Hermitian diagonal family diag(1, -t^3)."""
    a = Fraction(1)
    b = Fraction(0)
    d = -(t ** 3)
    return a, b, d


def singular_coupling_contact(t: Fraction) -> tuple[Fraction, Fraction, Fraction]:
    """Hermitian family [[t^2, t], [t, 1/2]]."""
    a = t * t
    b = t
    d = Fraction(1, 2)
    return a, b, d


def determinant(a: Fraction, b: Fraction, d: Fraction) -> Fraction:
    return a * d - b * b


def harvest() -> dict:
    # Falsifier A: zero contact + zero first derivative does not block crossing.
    a0, b0, d0 = cubic_contact(Fraction(0))
    a1, b1, d1 = cubic_contact(Fraction(1, 10))
    cubic = {
        "contact_det": str(determinant(a0, b0, d0)),
        "contact_predecessor": str(a0),
        "contact_coupling": str(b0),
        "right_det": str(determinant(a1, b1, d1)),
        "contact_ground_derivative": "0",
        "disposition": "GENERIC_ZERO_DERIVATIVE_CROSSING_COUNTERMODEL",
    }
    assert determinant(a0, b0, d0) == 0
    assert a0 > 0 and b0 == 0
    assert determinant(a1, b1, d1) < 0

    # Falsifier B: predecessor >= 0 and coupling=0 at contact do not block
    # a negative full determinant immediately away from contact.
    c0 = singular_coupling_contact(Fraction(0))
    cp = singular_coupling_contact(Fraction(1, 10))
    cm = singular_coupling_contact(Fraction(-1, 10))
    singular = {
        "contact_det": str(determinant(*c0)),
        "contact_predecessor": str(c0[0]),
        "contact_coupling": str(c0[1]),
        "right_det": str(determinant(*cp)),
        "left_det": str(determinant(*cm)),
        "disposition": "GENERIC_CONTACT_DECOUPLING_NOT_A_BARRIER",
    }
    assert c0[0] == 0 and c0[1] == 0 and c0[2] > 0
    assert cp[0] >= 0 and cm[0] >= 0
    assert determinant(*cp) < 0 and determinant(*cm) < 0

    return {
        "schema_version": "RHRC-FIRST-CROSSING-FALSIFIERS-1.0",
        "claim_cap": "SYNTHETIC_GENERIC_COUNTERMODEL_ONLY",
        "cubic_contact": cubic,
        "singular_coupling_contact": singular,
        "terminal_claim": "RH_OPEN",
    }


if __name__ == "__main__":
    import json
    print(json.dumps(harvest(), indent=2, sort_keys=True))
