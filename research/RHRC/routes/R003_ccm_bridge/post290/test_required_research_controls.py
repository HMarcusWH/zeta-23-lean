#!/usr/bin/env python3
"""Replay two supplied fixed exact controls and separate synthetic models.

Pinned ZIP/member bytes are read-only. Their algorithms run in memory with
assertions converted to explicit exceptions, including under python -O.
Only each original main's trailing file/print operations are replaced by a
return. No search, D2 continuation, source alteration or Lean claim occurs.
"""
from __future__ import annotations

import argparse
import ast
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys
import types
import zipfile

import sympy as s

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
INPUTS = REPO / "research/RHRC/integration/post290/spec/inputs"
PN_ZIP = "RH_Post290_PoleNeutral_Research_2026-10-13.zip"
NATIVE_ZIP = "RH_Constructive_Continuation_2026-10-13(2).zip"
ARCHIVES = {
    PN_ZIP: "9c2964a7731b583a95d220c6d54aa4214089336c249aedec2f9fb182b0b1ef82",
    NATIVE_ZIP: "0c3767e427fa003a34db90cfc40c4c4f60c8be8603d60f54fe3686a2ab248f85",
}
PN_PREFIX = "RH_Post290_PoleNeutral_Research/"
NATIVE_PREFIX = "RH_Constructive_Continuation_2026-10-13/"
MEMBERS = {
    "geometry": (PN_ZIP, PN_PREFIX + "checks/verify_pole_neutral_geometry.py", "d62310f68d005631acfd80dd579a224f0b2d033ca3cfc5984c9c88ab092ca953"),
    "modified_prime": (PN_ZIP, PN_PREFIX + "checks/verify_modified_prime_control.py", "ad79e6453ee27094c2ba056748f563439af5c68d72ac04c4f601e8d9accff9f8"),
    "modified_prime_evidence": (PN_ZIP, PN_PREFIX + "evidence/modified_prime_control.json", "1bd6037284787be8e25385940f9b7591b0f3cca6bb19232facc2c22ef3fb5484"),
    "native_completion": (NATIVE_ZIP, NATIVE_PREFIX + "checks/native_completion_certificate.py", "85d0b525be4d3d4eb0f54ff7f7778a097a95748845e6fe39b4e062428916c496"),
    "native_completion_evidence": (NATIVE_ZIP, NATIVE_PREFIX + "evidence/native_completion_certificate.json", "502d53d4a8adae8e2f4a93cb5a630a9802fcea923015be5d17799d84f02e2ddb"),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rational(value):
    value = F(value)
    return [value.numerator, value.denominator]


def matrix_record(matrix):
    return [[rational(matrix[i, j]) for j in range(matrix.cols)] for i in range(matrix.rows)]


def zero(matrix):
    return all(s.cancel(value) == 0 for value in matrix)


def read_member(key):
    archive, member, expected = MEMBERS[key]
    path = INPUTS / archive
    raw_archive = path.read_bytes()
    require(hashlib.sha256(raw_archive).hexdigest() == ARCHIVES[archive], "immutable control archive changed")
    with zipfile.ZipFile(path) as z:
        raw = z.read(member)
    require(hashlib.sha256(raw).hexdigest() == expected, "immutable control member changed")
    return raw, {"archive": str(path.relative_to(REPO)).replace("\\", "/"),
                 "archive_sha256": ARCHIVES[archive], "member": member,
                 "member_sha256": expected, "member_bytes": len(raw)}


class ExplicitAssertions(ast.NodeTransformer):
    def visit_Assert(self, node):
        # Preserve the test and original diagnostic, independent of -O.
        return ast.copy_location(ast.If(test=ast.UnaryOp(op=ast.Not(), operand=node.test),
            body=[ast.Raise(exc=ast.Call(func=ast.Name(id="ValueError", ctx=ast.Load()),
                                        args=[node.msg or ast.Constant("archived exact-control guard failed")], keywords=[]), cause=None)],
            orelse=[]), node)


def source_module(key, report_name=None, geometry=None):
    raw, provenance = read_member(key)
    tree = ast.parse(raw, filename=provenance["member"])
    body = []
    for node in tree.body:
        if isinstance(node, ast.If):
            # These pinned modules have only the final __name__ main guard.
            require(ast.unparse(node.test) == "__name__ == '__main__'", "unexpected archived top-level conditional")
            continue
        if isinstance(node, ast.ImportFrom) and node.module == "verify_pole_neutral_geometry":
            require(geometry is not None, "missing pinned geometry dependency")
            continue
        if isinstance(node, ast.FunctionDef) and node.name == "main":
            if report_name is None:
                continue
            outputs = [i for i, child in enumerate(node.body)
                       if isinstance(child, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "path" for t in child.targets)]
            require(len(outputs) == 1 and outputs[0] == len(node.body) - 3,
                    "archived output boundary changed")
            node.body = node.body[:outputs[0]] + [ast.Return(value=ast.Tuple(elts=[
                ast.Name(id=report_name, ctx=ast.Load()),
                ast.Call(func=ast.Name(id="locals", ctx=ast.Load()), args=[], keywords=[])
            ], ctx=ast.Load()))]
        body.append(node)
    tree.body = body
    tree = ast.fix_missing_locations(ExplicitAssertions().visit(tree))
    name = "_post290_required_control_" + key
    module = types.ModuleType(name)
    module.__file__ = provenance["member"]
    if geometry is not None:
        module.geometry = geometry
    sys.modules[name] = module  # dataclass inspects its defining module.
    exec(compile(tree, provenance["member"], "exec"), module.__dict__)
    return module, provenance


def modified_prime_control(geometry):
    module, provenance = source_module("modified_prime", "report", geometry)
    archived, state = module.main()
    old_bytes, old_provenance = read_member("modified_prime_evidence")
    require(archived == json.loads(old_bytes), "supplied modified-prime replay differs from archived result")
    require(archived["assertion_count"] == 15 and all(archived["checks"].values()), "supplied checks incomplete")
    a, p, u, du, Q = (state[name] for name in ("a", "p", "u", "du", "Q"))
    # K3 has one actual pole-neutral dimension in each parity. Verify the
    # actual geometric projectors rather than choosing unrelated vectors.
    d = geometry(3, a)
    # Normalize the rational normal profiles before forming their outer
    # products; the raw expanded shared formula is needlessly expensive.
    ve, vo = d["ve"].applyfunc(s.cancel), d["vo"].applyfunc(s.cancel)
    Qe = (d["E"]-ve*ve.T/s.cancel(ve.dot(ve))).applyfunc(s.cancel)
    Qo = (d["O"]-vo*vo.T/s.cancel(vo.dot(vo))).applyfunc(s.cancel)
    require(zero(Qe - u*u.T/u.dot(u)) and zero(Qo - du*du.T/du.dot(du)), "actual K3 pole-neutral projectors differ")
    even_q = s.factor((u.T*Q*u)[0]/u.dot(u))
    odd_q = s.factor((du.T*Q*du)[0]/du.dot(du))
    require(zero(Qe*u-u) and zero(Qo*du-du)
            and zero(Qe*Q*u-even_q*u) and zero(Qo*Q*du-odd_q*du),
            "actual one-dimensional atom eigenvectors failed")
    # Uniform coefficient-by-coefficient bounds from the supplied paper,
    # with 0<a<=1 and 3<pi<22/7. No decimal sign or native pi substitution.
    even_coefficients = [205*p-644, 1128-360*p, 2316-720*p]
    odd_coefficients = [15*p-47, 120*p-386, 240*p-667]
    def minima(expressions):
        return [min(expr.subs(p, 3), expr.subs(p, s.Rational(22, 7))) for expr in expressions]
    eb, ob = minima(even_coefficients), minima(odd_coefficients)
    require(eb == [-29, -s.Rational(24, 7), s.Rational(372, 7)] and ob == [-2, -26, 53], "supplied uniform coefficient bounds changed")
    require(sum(eb) == s.Rational(145, 7) and sum(ob) == 25 and 8 < 16 < 27, "supplied margins/window failed")
    from test_native_divisor_controls import check_coefficients, mangoldt
    native, native_first = check_coefficients(mangoldt)
    altered, altered_first = check_coefficients(lambda n: mangoldt(n) + (1 if n == 2 else 0))
    require(native_first is None and all(value == 0 for value in native.values())
            and altered_first == 2 and altered[2] == 1
            and all(altered[n] == (1 if n % 2 == 0 else 0) for n in range(1, 65)),
            "modified prime did not first break the actual divisor law at n=2")
    return {"id": "MODIFIED_PRIME_K3", "origin": "SYNTHETIC_CONTROL",
            "source_model_tag": "POSITIVE_FIRST_PRIME_COEFFICIENT_MODIFIED_NOT_ACTUAL_ZETA",
            "control_is_actual_zeta": False, "resolution": "RATIONAL_EXACT",
            "scientific_disposition": "SUPPLIED_POLE_NEUTRAL_ATOM_CONTROL_REPLAYED_NATIVE_DIVISOR_LAW_REJECTS_MODIFIED_COEFFICIENT",
            "source_provenance": [provenance, old_provenance], "supplied_checks": archived["checks"],
            "domain": "K=3, 0<a<=1, 3<pi<22/7; L=(4/3)log2 gives 2<exp(L)<3",
            "M4": [-720, 1], "even_numerator_lower_bound": [145, 7], "odd_numerator_lower_bound": [25, 1],
            "coefficient_lower_bounds": {"even": [rational(x) for x in eb], "odd": [rational(x) for x in ob]},
            "actual_PN_dimensions": {"even": 1, "odd": 1},
            "symbolic_eigenvectors": {"even": [str(x) for x in u], "odd": [str(x) for x in du]},
            "actual_compressed_atom_eigenvalues": {"even": str(even_q), "odd": str(odd_q)},
            "prime_atom_signs": {"even": "STRICTLY_POSITIVE", "odd": "STRICTLY_NEGATIVE"},
            "first_broken_divisor_coefficient": 2, "divisor_residual_at_2": [1, 1],
            "scope": "Exact supplied atom formulas, actual one-dimensional PN eigendirections, rational sign margins and modified-coefficient native-identity failure. A sufficiently large positive atom increment is the paper mechanism for negative-even/positive-odd grounds; no actual-zeta negative ground or full native upper law is inferred."}


def exact_interval(record):
    denominator = int(record["denominator"])
    lo, hi = int(record["lower_numerator"]), int(record["upper_numerator"])
    require(denominator > 0 and lo <= hi, "invalid exact interval")
    return {"lower": [lo, denominator], "upper": [hi, denominator], "resolution": "RATIONAL_EXACT"}


def native_frequency_control():
    module, provenance = source_module("native_completion", "out")
    archived, _ = module.main()
    old_bytes, old_provenance = read_member("native_completion_evidence")
    require(archived == json.loads(old_bytes), "native fixed-frequency replay differs from original exact receipt")
    require(F(archived["operator_norm_rational_upper_bound"]) == F(605, 621) < 1,
            "native mass comparison constant failed")
    require(archived["zero_denominator_rejected"] is True, "native zero denominator not rejected")
    rows = []
    for row in archived["native_inverse_iteration_falsifiers"]:
        eps, frequency = F(row["epsilon"]), F(row["frequency"])
        real, bad = row["A_triangle"]["real"], row["abs2_I_minus_A"]
        require(frequency == 12 and eps in (F(0), F(1, 100)), "wrong fixed native frequency/domain")
        require(F(int(real["upper_numerator"]), int(real["denominator"])) < -F(4, 100)
                and F(int(bad["lower_numerator"]), int(bad["denominator"])) > F(109, 100),
                "native naive inverse-iteration margins failed")
        rows.append({"epsilon": rational(eps), "frequency": [12, 1],
                     "domain_status": "BOUNDARY_FREQUENCY_ONLY" if eps == 0 else "POSITIVE_DAMPING_FREQUENCY",
                     "zeta": {k: exact_interval(v) for k, v in row["zeta"].items()},
                     "A_triangle": {k: exact_interval(v) for k, v in row["A_triangle"].items()},
                     "abs2_I_minus_A": exact_interval(bad),
                     "em_absolute_error_bound": rational(row["em_absolute_error_bound"])})
    require([r["epsilon"] for r in rows] == [[0, 1], [1, 100]], "fixed damping rows omitted")
    return {"id": "NATIVE_FREQUENCY_NAIVE_ITERATION", "origin": "NATIVE_PARAMETER_EVALUATION",
            "source_model_tag": "UNCHANGED_NATIVE_MULTIPLIER_NAIVE_FIXED_POINT_ITERATION",
            "is_actual_zeta_countermodel": False, "native_coefficients_modified": False,
            "resolution": "RATIONAL_EXACT", "source_provenance": [provenance, old_provenance],
            "scientific_disposition": "NAIVE_I_MINUS_A_ITERATION_NONCONTRACTIVE_AT_TWO_FIXED_FREQUENCIES",
            "operator_norm_rational_upper_bound": [605, 621],
            "eta_half_enclosure": exact_interval(archived["eta_half_enclosure"]),
            "rows": rows, "real_A_strict_upper_margin": [-4, 100],
            "abs2_I_minus_A_strict_lower_margin": [109, 100], "zero_denominator_rejected": True,
            "scope": "Only the naive unpreconditioned (I-A) fixed-point inverse iteration is falsified. This does not falsify the proved (I-AA*) adjoint-residual scheme and proves no actual native-input range failure, noninvertibility or RH statement. Epsilon=0 is a boundary evaluation; epsilon=1/100 is the separate legitimate positive-damping case."}


def primitive_integer(vector):
    denominator = s.ilcm(*[x.q for x in vector])
    integers = [int(x*denominator) for x in vector]
    divisor = s.igcd(*integers)
    integers = [x//int(divisor) for x in integers]
    if next(x for x in integers if x) < 0:
        integers = [-x for x in integers]
    return s.Matrix(integers)


def moment_null_control(geometry):
    d = geometry(4, s.Rational(1))
    Qe, n = d["Qe"], d["n"]
    basis = s.Matrix.hstack(*Qe.columnspace())
    M4 = n.applyfunc(lambda x: x**4).T
    u = primitive_integer(basis*(M4*basis).nullspace()[0])
    v = primitive_integer(basis*(u.T*basis).nullspace()[0])
    u2, v2 = u.dot(u), v.dot(v)
    A = -Qe + (v*u.T+u*v.T)/u2
    require(u2 > 0 and v2 > 0 and u.dot(v) == 0 and (M4*u)[0] == 0,
            "moment-null PN construction degenerated")
    require(zero(Qe*u-u) and zero(Qe*v-v) and zero(A-A.T) and zero(Qe*A-A)
            and zero(A*Qe-A) and zero(A*u+u-v), "actual PN carrier/residual failed")
    rayleigh = (u.T*A*u)[0]/u2
    residual = A*u-rayleigh*u
    w = u-v
    competitor = s.factor((w.T*A*w)[0]/w.dot(w))
    require(rayleigh == -1 and residual == v and residual.dot(residual) > 0
            and competitor == -1-2*v2/(u2+v2) and competitor < rayleigh,
            "negative moment-null trial unexpectedly became a ground")
    return {"id": "MOMENT_NULL_NOT_GROUND", "origin": "SYNTHETIC_CONTROL",
            "source_model_tag": "SYNTHETIC_PN_OPERATOR_NOT_NATIVE_COEFFICIENTS",
            "is_supplied_historical_replay": False, "control_is_actual_zeta": False,
            "resolution": "RATIONAL_EXACT", "K": 4, "a": [1, 1],
            "scientific_disposition": "NEW_EXACT_NEGATIVE_MOMENT_NULL_TRIAL_HAS_NONZERO_RESIDUAL_AND_LOWER_COMPETITOR",
            "u": matrix_record(u), "v": matrix_record(v), "operator": matrix_record(A),
            "actual_PN_projector": matrix_record(Qe), "M4_u": [0, 1],
            "rayleigh_u": [-1, 1], "residual_norm_squared": rational(v2),
            "rayleigh_u_minus_v": rational(competitor),
            "scope": "NEW deterministic rational K4 pole-neutral operator control, not a rediscovered supplied instance and not native prime coefficients. It refutes trial-equals-ground inference: the negative M4-null trial has nonzero residual and an explicit lower Rayleigh competitor."}


def generic_range_control():
    A = s.diag(s.Rational(1, 2), 0)
    y = s.Matrix([0, 1])
    adjoint_residual_step = s.eye(2)-A*A.T
    require(A == A.T and all(x >= 0 for x in A.diagonal())
            and s.Rational(1, 2) < 1 and A.T*y == s.zeros(2, 1)
            and y.dot(y) == 1 and adjoint_residual_step*y == y,
            "generic contractive range obstruction failed")
    return {"id": "GENERIC_CONTRACTIVE_RANGE_OBSTRUCTION", "origin": "SYNTHETIC_CONTROL",
            "source_model_tag": "DIAGONAL_HALF_ZERO_NOT_NATIVE_COMPLETION_OPERATOR",
            "control_is_actual_zeta": False, "resolution": "RATIONAL_EXACT",
            "scientific_disposition": "POSITIVE_STRICT_CONTRACTION_HAS_NONTRIVIAL_ADJOINT_KERNEL_AND_RANGE_OBSTRUCTION",
            "operator": matrix_record(A), "input_y": matrix_record(y),
            "operator_norm": [1, 2], "adjoint_kernel_pairing": [1, 1],
            "adjoint_residual_step": matrix_record(adjoint_residual_step),
            "scope": "Explicit separate generic model: every range vector has zero second coordinate while y has second coordinate one. The (I-AA*) residual retains y, consistently with its kernel-projection invariant. This is not the native completion operator or an actual native-input range failure."}


def validate_report(report):
    require(report.get("claim_cap") == "RH_OPEN" and report.get("Lean_authority") is False,
            "required-control report claim firewall failed")
    rows = {r["id"]: r for r in report["controls"]}
    require(set(rows) == {"MODIFIED_PRIME_K3", "NATIVE_FREQUENCY_NAIVE_ITERATION", "MOMENT_NULL_NOT_GROUND", "GENERIC_CONTRACTIVE_RANGE_OBSTRUCTION"},
            "mandatory exact-control row missing")
    modified = rows["MODIFIED_PRIME_K3"]
    require(modified["origin"] == "SYNTHETIC_CONTROL" and modified["control_is_actual_zeta"] is False
            and modified["M4"] == [-720, 1]
            and modified["even_numerator_lower_bound"] == [145, 7]
            and modified["odd_numerator_lower_bound"] == [25, 1]
            and modified["first_broken_divisor_coefficient"] == 2,
            "modified-prime model/margins were dropped or mislabelled")
    native = rows["NATIVE_FREQUENCY_NAIVE_ITERATION"]
    require(native["origin"] == "NATIVE_PARAMETER_EVALUATION"
            and native["native_coefficients_modified"] is False
            and [r["frequency"] for r in native["rows"]] == [[12, 1], [12, 1]]
            and [r["epsilon"] for r in native["rows"]] == [[0, 1], [1, 100]],
            "native frequency/source scope changed")
    for row in native["rows"]:
        require(F(*row["A_triangle"]["real"]["upper"]) < -F(4, 100)
                and F(*row["abs2_I_minus_A"]["lower"]) > F(109, 100), "native exact margins dropped")
    moment = rows["MOMENT_NULL_NOT_GROUND"]
    require(moment["origin"] == "SYNTHETIC_CONTROL" and moment["is_supplied_historical_replay"] is False
            and moment["source_model_tag"] == "SYNTHETIC_PN_OPERATOR_NOT_NATIVE_COEFFICIENTS"
            and moment["M4_u"] == [0, 1] and F(*moment["residual_norm_squared"]) > 0
            and F(*moment["rayleigh_u_minus_v"]) < -1, "new synthetic control scope changed")


def run():
    geometry_module, geometry_provenance = source_module("geometry")
    controls = [modified_prime_control(geometry_module.geometry), native_frequency_control(),
                moment_null_control(geometry_module.geometry), generic_range_control()]
    report = {"schema": "post290.required-research-controls.v1", "execution_status": "SUCCESS",
              "integrity_status": "PASS", "claim_cap": "RH_OPEN", "Lean_authority": False,
              "scientific_disposition": "EXACT_SCOPED_FALSIFICATIONS_REPLAYED_RH_OPEN",
              "algorithm_execution": "PINNED_ARCHIVE_ALGORITHMS_IN_MEMORY_OUTPUTS_RETURNED_ASSERT_GUARDS_EXPLICIT_UNDER_O",
              "geometry_source_provenance": geometry_provenance, "controls": controls}
    validate_report(report)
    from copy import deepcopy
    mutations = (
        lambda x: x["controls"][0].pop("even_numerator_lower_bound"),
        lambda x: x["controls"][1]["rows"][0].update(frequency=[11, 1]),
        lambda x: x["controls"][0].update(control_is_actual_zeta=True),
        lambda x: x["controls"][2].update(is_supplied_historical_replay=True),
    )
    for mutate in mutations:
        altered = deepcopy(report)
        mutate(altered)
        try:
            validate_report(altered)
        except (ValueError, KeyError):
            continue
        raise ValueError("required-control evidence mutation escaped rejection")
    report["adversarial_mutations_rejected"] = len(mutations)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    report = run()
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({"status": "PASS", "controls": len(report["controls"]),
                      "adversarial_mutations_rejected": report["adversarial_mutations_rejected"],
                      "scope": "two supplied fixed exact controls plus separate synthetic PN trial/range controls",
                      "RH": "OPEN", "Lean_authority": False}))


if __name__ == "__main__":
    main()
