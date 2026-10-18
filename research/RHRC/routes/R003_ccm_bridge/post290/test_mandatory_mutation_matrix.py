"""Replay the twenty frozen PR292 mathematical/evidence mutation rows.

Every row first accepts a correct exact model, then rejects its mutants.
Synthetic polynomial/matrix/receipt fixtures are not actual generated zeta
states, compiler receipts, D2 certificates, or independent review approvals.
The only output is JSON on stdout; importing/running this file writes nothing.
All checks remain active with Python optimization enabled.
"""
from __future__ import annotations

from copy import deepcopy
from fractions import Fraction as F
import hashlib
import json
from typing import Callable

import sympy as s

from build_formal_receipt import (
    KIND_BLOB_SHA1, KIND_CROSSWALK, TYPED_CONTRACT_ROOTS,
    compiler_records, independent_complete_review, load_frozen_json,
)
from pole_neutral_exact import geometry, is_zero
from test_argon_continuum_and_roots_exact import continuum_blocks
from test_forcing_history import causal, four
from test_output_mutations import fixture, synthetic_release_gaps
from test_reviewed_workflow_harvest import fixture as harvest_fixture
from verify_semantic_review_provenance import (
    REQUIRED, field_digest, validate as validate_semantic_review,
)
from verify_workflow_harvest import validate_jobs


LABELS = (
    "SOURCE_MISMATCH", "WRONG_TRANSFORM_POINT", "WRONG_ZERO_JET_ORDER",
    "WRONG_JET_COEFFICIENT", "EXCEPTIONAL_POINT_MISMATCH",
    "WRONG_SHIFT_BUDGET", "UNSUPPORTED_SPECTRAL_IDENTIFICATION",
    "WRONG_CARRIER_MAP", "WRONG_ADJOINT_IDENTITY", "INAPPLICABLE_BRANCH",
    "OMITTED_NORMAL_TERM", "WRONG_SCHUR_SPACE", "INCOMPLETE_FORCING",
    "WRONG_COMPRESSION", "UNPROVED_PROPERTY_TRANSPORT",
    "MISSING_DOMAIN_LIMIT_THEOREM", "INCOMPLETE_NUMERICAL_COVERAGE",
    "EVIDENCE_INTEGRITY_FAILURE", "INCOMPLETE_PRODUCER",
    "SCIENTIFIC_DISPOSITION_MISMATCH",
)


def require(condition: object, reason: str) -> None:
    if not bool(condition):
        raise RuntimeError(reason)


def equal(left: object, right: object) -> bool:
    if isinstance(left, s.MatrixBase) or isinstance(right, s.MatrixBase):
        return is_zero(left - right)
    return s.simplify(left - right) == 0


def exact_row(number: int, baseline: object, mutants: dict,
              valid: Callable[[object], bool], reason: str) -> dict:
    require(valid(baseline), f"row {number}: correct exact model rejected")
    rejected = []
    for name, candidate in mutants.items():
        require(not valid(candidate), f"row {number}: mutant accepted: {name}")
        rejected.append(name)
    require(rejected, f"row {number}: no adversarial mutation was exercised")
    return row(number, reason, rejected, "EXACT_FINITE_CONTROL")


def row(number: int, reason: str, rejected: list,
        authority: str = "VALIDATOR_CONTROL") -> dict:
    return {"row": number, "status": "PASS", "label": LABELS[number - 1],
            "reason": reason, "rejected_mutations": rejected,
            "authority": authority, "Lean_authority": False}


def reject_value_error(action: Callable[[], object], message: str) -> None:
    try:
        action()
    except ValueError as exc:
        require(message in str(exc),
                f"validator rejected for the wrong reason: {exc!s}; wanted {message!r}")
    else:
        raise RuntimeError(f"validator incorrectly accepted mutant: {message}")


def release_mutation(control: list, name: str, mutate: Callable[[list], None],
                     expected_gap: str) -> str:
    args = deepcopy(control)
    mutate(args)
    gaps = synthetic_release_gaps(*args)
    require(any(expected_gap in gap for gap in gaps),
            f"release mutant {name!r} lacks its expected rejection: {gaps!r}")
    return name


def jet_model() -> tuple:
    z, t = s.symbols("z t")
    p = s.Rational(3, 4) + s.I * s.Rational(2, 3)
    epsilon = s.Rational(1, 8)
    w = p - epsilon
    m, R, J = 3, s.Rational(2, 7), s.Rational(5, 3)
    Y = (-R * J * s.diff((t - p)**m, t)).subs(t, z + epsilon)
    return z, t, p, epsilon, w, m, R, J, Y


def mathematical_rows() -> list:
    rows = []
    z = s.symbols("z")
    Q = 1 + z**2
    pole_killer = (z**2 - s.Rational(1, 4))**2
    J = pole_killer * Q
    rows.append(exact_row(1, J, {"replace single Q by Q squared": pole_killer * Q**2},
                          lambda candidate: equal(candidate, J),
                          "The P-squared source has one Q factor; correlation has Q squared."))

    z, t, p, epsilon, w, m, R, J, Y = jet_model()
    rows.append(exact_row(2, Y.subs(z, w), {
        "pair at conjugate w": Y.subs(z, s.conjugate(w)),
        "omit positive damping shift": (-R * J * s.diff((t-p)**m, t)).subs(t, w),
    }, lambda candidate: equal(candidate, 0),
        "The correct shifted physical-Y zero is p=w+epsilon, with no conjugation."))

    def correct_order(order: int) -> bool:
        return (all(equal(s.diff(Y, z, n).subs(z, w), 0) for n in range(order))
                and not equal(s.diff(Y, z, order).subs(z, w), 0))

    rows.append(exact_row(3, m-1, {"use zero multiplicity m as Y order": m},
                          correct_order,
                          "Differentiating a multiplicity-m zero makes Y have order m-1."))
    jet = s.diff(Y, z, m-1).subs(z, w)
    pairing = (-1)**(m-1) * jet
    expected = (-1)**m * R * J * s.factorial(m)
    require(equal(pairing, expected) and expected != 0, "physical-Y coefficient model failed")
    rows.append(exact_row(4, expected, {
        "extra factorial": expected * s.factorial(m),
        "omit parity sign": R * J * s.factorial(m),
    }, lambda candidate: equal(candidate, pairing),
        "The exact derivative and Laplace parity give (-1)^m R J m! once."))

    pole_expression = (z-1) / (z-1)
    continued_value = s.limit(pole_expression, z, 1)
    rows.append(exact_row(5, continued_value,
                          {"totalized zero times pole at exceptional point": s.Integer(0)},
                          lambda candidate: equal(candidate, continued_value),
                          "A removable pole product is evaluated by its limit, not 0 times 0."))

    depth, Kd, eta = F(12), 5, F(5)
    gap = depth / (12*(Kd-1))
    lam = -eta-gap
    predecessors = (F(-19, 4), F(-9, 2))
    ground_inverse = max(1/(value-lam) for value in predecessors)
    detector_inverse = max(1/(value+eta) for value in predecessors)
    budgets = (6*(Kd-1)/depth, 12*(Kd-1)/depth)
    rows.append(exact_row(6, budgets,
                          {"swap lambda and minus-eta inverse budgets": budgets[::-1]},
                          lambda candidate: (ground_inverse == candidate[0]
                                             and detector_inverse == candidate[1]),
                          "The exact predecessor inverses attain distinct 6 and 12 budgets."))
    actual_delta = F(1, 100)
    even_bottom, odd_bottom = -depth, -depth+actual_delta
    require(even_bottom < odd_bottom < 0 and actual_delta < depth/3,
            "small strict-even gap model failed")
    rows.append(exact_row(7, (lam, actual_delta), {
        "identify lambda with minus eta": (-eta, actual_delta),
        "replace actual parity gap by depth third": (lam, depth/3),
    }, lambda candidate: candidate == (lam, odd_bottom-even_bottom),
        "A separated selector lambda and arbitrarily small strict parity gap remain distinct."))

    A, B, D = s.diag(-2, 3), s.diag(1, 3), s.diag(2, 3)
    g, source, u = s.Matrix([1, 0]), s.Matrix([[6, 0]]), s.Matrix([1, 0])
    lam_even = -2
    require(equal(B*D-D*A, g*source), "even intertwining model failed")
    ray = D.inv() * (B-lam_even*s.eye(2)).inv() * g
    rows.append(exact_row(8, ray,
                          {"drop D0 inverse": (B-lam_even*s.eye(2)).inv()*g},
                          lambda candidate: equal((source*u)[0]*candidate, u),
                          "A nonunitary D0 needs its inverse in the even reconstruction."))

    A, B, D = s.diag(1, 3), s.diag(-2, 3), s.diag(2, 3)
    g, source, v = s.Matrix([s.I, 0]), s.Matrix([[6*s.I, 0]]), s.Matrix([1, 0])
    lam_odd = -2
    ray = -D.H.inv() * (A-lam_odd*s.eye(2)).inv() * source.H
    overlap = (g.H*v)[0]
    require(equal(D.H*B-A*D.H, source.H*g.H), "complex adjoint model failed")
    rows.append(exact_row(9, (ray, D.H), {
        "drop strict-odd minus sign": (-ray, D.H),
        "substitute D0 inverse for D0 adjoint": (ray, D.inv()),
        "treat D0 as unitary in the odd ray":
            (-D.H*(A-lam_odd*s.eye(2)).inv()*source.H, D.H),
    }, lambda candidate: (equal(overlap*candidate[0], v)
                           and equal(candidate[1]*B-A*candidate[1], source.H*g.H)),
        "The complex odd identity requires the adjoint and its reconstruction minus sign."))

    reversal = s.diag(1, -1)
    even, odd = s.Matrix([1, 0]), s.Matrix([0, 1])
    rows.append(exact_row(10, even, {"apply even residual premise to odd vector": odd},
                          lambda candidate: equal(reversal*candidate, candidate),
                          "The even carrier guard rejects a nonzero odd vector before using M4."))

    blocks = continuum_blocks(3, s.Rational(1))
    Qe, Qo, D, A0, B0, g0, S0 = (
        blocks[key] for key in ("Qe", "Qo", "D", "A0", "B0", "g0", "source_P0"))
    defect = B0*D*Qe-D*A0
    require(not is_zero(defect), "continuum defect must be nonzero in exact control")
    rows.append(exact_row(11, g0*S0,
                          {"set neutral continuum defect to zero": s.zeros(defect.rows)},
                          lambda candidate: equal(candidate, defect),
                          "The retained K3 continuum defect is the nonzero corrected normal term."))

    P = s.diag(4, 5)
    cross = s.Matrix([[1+s.I, 2], [0, 1-s.I]])
    C = s.diag(-8, -10)
    T = P.row_join(cross).col_join(cross.H.row_join(C))
    pvec = s.Matrix([s.Rational(3, 5), 0, 0, s.Rational(4, 5)])
    x, y = pvec[:2, 0], pvec[2:, 0]
    shifted = P+s.eye(2)
    schur = C+s.eye(2)-cross.H*shifted.inv()*cross
    completed = x+shifted.inv()*cross*y
    total = (pvec.H*(T+s.eye(4))*pvec)[0]
    square = (completed.H*shifted*completed)[0]
    rows.append(exact_row(12, (y.H*schur*y)[0], {
        "replace two-dimensional detector complement by first shell":
            s.conjugate(y[0])*schur[0, 0]*y[0],
    }, lambda candidate: equal(square+candidate, total),
        "The full detector Schur completion fails after a nonzero complement component is lost."))

    L, c, kappa, sigma = 10, 2, F(2, 7), -1
    original_history = four(9, L, c, sigma, kappa)
    kernel = lambda value: F(1, 1+abs(value))
    response = lambda value: F(value)+F(1, 2)
    interior = lambda value: response(value) if 0 <= value <= L else F(0)
    exterior = lambda value: response(value) if value > L else F(0)
    coordinates = [L-2+1-value for value in range(-2, 3)]
    whole = sum(kernel(value)*response(point)
                for value, point in zip(range(-2, 3), coordinates))
    middle = sum(kernel(value)*interior(point)
                 for value, point in zip(range(-2, 3), coordinates))
    tail = sum(kernel(value)*exterior(point)
               for value, point in zip(range(-2, 3), coordinates))
    require(middle != 0 and whole == middle+tail, "boundary history partition model failed")
    rows.append(exact_row(13, (original_history, whole), {
        "delete reflected fourth prime history":
            (original_history-kappa*sigma*causal(9+c-L), whole),
        "discard original interior history": (original_history, tail),
    }, lambda candidate: candidate == (original_history, middle+tail),
        "All four signed prime arguments and the nonzero interior contribution are retained."))

    neutral_u = s.Matrix([-10, 30, -30, 20, -30, 30, -10])
    legal_response = blocks["E"]*blocks["continuum_diagonal"]*neutral_u
    neutral_response = Qe*legal_response
    require(equal(Qe*neutral_u, neutral_u), "compression input is not neutral")
    require(not equal(legal_response, neutral_response), "legal/neutral control is vacuous")
    rows.append(exact_row(14, neutral_response,
                          {"replace neutral response by legal response": legal_response},
                          lambda candidate: equal(Qe*candidate, candidate),
                          "The legal K3 response has a nonzero pole-normal component removed by Qe."))

    positive_source, finite_ground = s.Matrix([1, 1]), s.Matrix([1, -1])
    ground_matrix = -finite_ground*finite_ground.T/finite_ground.dot(finite_ground)
    require(equal(ground_matrix*finite_ground, -finite_ground), "finite ground control failed")
    rows.append(exact_row(15, positive_source,
                          {"transfer source positivity to sign-changing finite ground": finite_ground},
                          lambda candidate: all(value >= 0 for value in candidate),
                          "A positive source does not make a distinct negative-eigenvalue ground positive."))

    forward = s.diag(s.Rational(1, 2), 0)
    full_input, attainable = s.Matrix([1, 1]), s.Matrix([1, 0])
    invisible = s.Matrix([0, 1])
    residual = (s.eye(2)-forward*forward.H)**8*full_input
    require(equal((invisible.H*residual)[0], 1), "adjoint-kernel projection was lost")
    require(0 < residual[0] < full_input[0], "observed finite coordinate must decay")
    rows.append(exact_row(16, attainable,
                          {"promote observed finite decay to full range membership": full_input},
                          lambda candidate: equal((invisible.H*candidate)[0], 0),
                          "An invisible adjoint-kernel component persists despite finite observed decay."))
    return rows


def compiler_fixture() -> tuple:
    head, tree = "a"*40, "b"*40
    roots = {"Mock.first": "Mock.Module", "Mock.second": "Mock.Module"}
    lines = [f"POST290_COMPILER_CONTEXT\t{head}\t{tree}"]
    for name in roots:
        lines.extend([
            f"RHRC_CANDIDATE_RESULT\t{name}\tRESOLVED_UNIQUE\t1\t{name}"
            "\tMock.Module\tTHEOREM\t0\tSYNTHETIC_CONTROL_TYPE\tcontrol",
            f"POST290_AXIOMS\t{name}\tpropext,Classical.choice,Quot.sound",
        ])
    return "\n".join(lines), roots, head, tree


class ReviewBytes:
    """In-memory test input for the real independent receipt review parser."""
    def __init__(self, data: dict):
        self.data = data

    def read_bytes(self) -> bytes:
        return json.dumps(self.data, sort_keys=True).encode("utf-8")


def semantic_fixture() -> tuple:
    head, tree = "c"*40, "a"*40
    api = load_frozen_json(KIND_CROSSWALK, KIND_BLOB_SHA1)
    kind_names = {"THEOREM": "THEOREM", "DEFINITION": "DEFINITION",
                  "STRUCTURE": "INDUCTIVE", "INDUCTIVE": "INDUCTIVE"}
    roots = {entry["requested_name"]: "Synthetic.Source" for entry in api["rows"]}
    kinds = {entry["requested_name"]: kind_names[entry["required_kind"]]
             for entry in api["rows"]}
    roots.update({name: "Zeta23.RHRC.Step123OutputContractCheck" for name in TYPED_CONTRACT_ROOTS})
    kinds.update(TYPED_CONTRACT_ROOTS)
    declaration = next(iter(roots))
    review_url = "https://github.com/mock/review/17"
    review = {"schema_version": "POST290_INDEPENDENT_SEMANTIC_REVIEW_1.0",
              "reviewed_head": head, "reviewed_tree": tree, "claim_cap": "RH_OPEN",
              "reviewer_identity": "synthetic-reviewer",
              "reviewer_is_source_author": False,
              "independent_assumption_review_pass": True,
              "external_review_reference": review_url,
              "field_reviews": [{"id": field, "semantic_proof_review": "PASS",
                                  "evidence_verified": True, "declaration_ref": declaration,
                                  "reason": "Synthetic validator fixture; no mathematical review."}
                                 for field in sorted(REQUIRED)]}
    pr = {"number": 292, "head": {"sha": head}, "user": {"login": "synthetic-author"}}
    github = [{"id": 17, "user": {"login": "synthetic-reviewer", "type": "User"},
               "author_association": "COLLABORATOR", "state": "APPROVED",
               "commit_id": head, "html_url": review_url,
               "submitted_at": "2026-10-17T00:00:00Z",
               "body": "PR292-44-FIELD-SHA256="+field_digest(review["field_reviews"])}]
    commits = [{"author": {"login": "synthetic-author"}, "committer": None}]
    return review, pr, github, commits, head, tree, roots, kinds


def validator_rows() -> list:
    controls = fixture()
    require(not synthetic_release_gaps(*controls), "synthetic release baseline was rejected")
    rows = []
    rejected = []
    for key in ("unrun_tiles", "unresolved_tiles", "unverified_tiles"):
        rejected.append(release_mutation(controls, f"mark {key} complete",
                        lambda args, key=key: args[2].update({key: 1}),
                        "D2 continuous full-domain gate incomplete"))
    rejected.append(release_mutation(controls, "required skipped checker reported passed",
                    lambda args: args[3][0].update(conclusion="skipped"),
                    "required job unestablished"))
    raw, reviewed = harvest_fixture()
    require(validate_jobs(raw, reviewed), "reviewed harvest baseline rejected")
    for status, conclusion in (("completed", "skipped"), ("in_progress", None)):
        actual, proposed = deepcopy(raw), deepcopy(reviewed)
        actual["jobs"][0].update(status=status, conclusion=conclusion)
        proposed["jobs"][0].update(status=status, conclusion=conclusion,
                                    scientific_acceptance=True)
        reject_value_error(lambda: validate_jobs(actual, proposed), "skipped/failed/unrun")
        rejected.append(f"harvest accepts {status}/{conclusion} as scientific completion")
    rows.append(row(17, "Real release and harvest guards reject missing coverage and skipped/unrun work.",
                    rejected))

    log, roots, head, tree = compiler_fixture()
    types, axioms = compiler_records(log, roots, head, tree)
    require(set(types) == set(roots) and set(axioms) == set(roots),
            "exact compiler fixture baseline incomplete")
    rejected = []
    bad_logs = {
        "stale source tree": (log.replace(tree, "d"*40), "compiler head/tree context"),
        "duplicate compiler root": (log+"\n"+log.splitlines()[1], "duplicate or empty compiler type"),
        "missing public API": ("\n".join(log.splitlines()[:-2]), "incomplete type or axiom receipt"),
        "wrong declaration kind": (log.replace("THEOREM\t0", "DEFINITION\t0"),
                                   "binding identity/kind mismatch"),
    }
    for name, (candidate, message) in bad_logs.items():
        reject_value_error(lambda: compiler_records(candidate, roots, head, tree), message)
        rejected.append(name)
    rejected.append(release_mutation(controls, "stale normalized theorem type hash",
                    lambda args: args[1]["declarations"][0].update(normalized_type="CHANGED_TYPE"),
                    "unverified, wrong-kind or stale producer"))
    rejected.append(release_mutation(controls, "missing requested public API receipt",
                    lambda args: args[1]["declarations"].pop(0), "missing producer"))
    rows.append(row(18, "Real compiler/receipt validators reject tree/type drift, duplicate roots, APIs and kinds.",
                    rejected))

    review, pr, github, commits, head, tree, roots, kinds = semantic_fixture()
    digest = independent_complete_review(ReviewBytes(review), roots, kinds, head, tree)
    require(digest == hashlib.sha256(ReviewBytes(review).read_bytes()).hexdigest(),
            "independent complete-review parser baseline failed")
    provenance = validate_semantic_review(review, pr, github, commits, head, tree)
    require(provenance["reviewed_field_count"] == 44, "semantic provenance baseline incomplete")
    rejected = []
    reject_value_error(lambda: independent_complete_review(None, roots, kinds, head, tree),
                       "requires a separately supplied independent semantic review")
    rejected.append("completion without separately supplied semantic review")
    wrong_roots = dict(roots)
    wrong_roots[next(iter(TYPED_CONTRACT_ROOTS))] = "Synthetic.WrongModule"
    reject_value_error(lambda: independent_complete_review(ReviewBytes(review), wrong_roots,
                                                           kinds, head, tree),
                       "incorrect declaration kind or source module")
    rejected.append("typed contract root comes from an unrelated module")
    reject_value_error(lambda: validate_semantic_review(review, pr, [], commits, head, tree),
                       "no independent GitHub APPROVED review")
    rejected.append("claimed approval with no signed GitHub review")
    bad_review = deepcopy(review)
    bad_review["field_reviews"][0]["semantic_proof_review"] = "UNRESOLVED"
    reject_value_error(lambda: validate_semantic_review(bad_review, pr, github, commits, head, tree),
                       "incomplete or malformed 44-field independent review")
    rejected.append("completion with an unresolved field review")
    self_review = deepcopy(review)
    self_review["reviewer_identity"] = "synthetic-author"
    reject_value_error(lambda: validate_semantic_review(self_review, pr, github, commits, head, tree),
                       "reviewer participated as source author")
    rejected.append("source author labelled independent reviewer")
    rejected.append(release_mutation(controls, "completion flag with absent typed contract",
                    lambda args: args[1].update(declarations=[
                        entry for entry in args[1]["declarations"]
                        if entry.get("declaration") not in TYPED_CONTRACT_ROOTS]),
                    "missing or wrong typed MC contract"))
    rejected.append(release_mutation(controls, "producer completion flag alone",
                    lambda args: args[1].update(independent_assumption_review_pass=False),
                    "independent producer assumption review missing"))
    rows.append(row(19, "Real complete-output, provenance and release validators require review and typed consumers.",
                    rejected))

    raw, reviewed = harvest_fixture()
    reviewed["jobs"][0].update(scientific_disposition="UNRESOLVED",
                                scientific_acceptance=False,
                                review_reason="Diagnostic ran successfully; positivity remains unresolved.")
    require(validate_jobs(raw, reviewed), "honest successful UNRESOLVED diagnostic rejected")
    rejected = [release_mutation(controls, "diagnostic unresolved rows promoted to positivity",
                lambda args: args[3][-1]["native_output_review"].update(unresolved_rows=1),
                "native finite observation output not independently reviewed")]
    changed = deepcopy(reviewed)
    changed["jobs"][0]["conclusion"] = "POSITIVE"
    changed["jobs"][0]["scientific_acceptance"] = True
    reject_value_error(lambda: validate_jobs(raw, changed), "immutable GitHub job result changed")
    rejected.append("rewrite a successful diagnostic job result as POSITIVE")
    rows.append(row(20, "An honest UNRESOLVED diagnostic is preserved and cannot satisfy the finite positivity gate.",
                    rejected))
    return rows


def run() -> dict:
    rows = mathematical_rows()+validator_rows()
    require([entry["row"] for entry in rows] == list(range(1, 21)),
            "mandatory mutation rows missing, duplicated or reordered")
    require(tuple(entry["label"] for entry in rows) == LABELS,
            "mandatory mutation label map changed")
    return {"status": "PASS", "claim_cap": "RH_OPEN", "row_count": len(rows),
            "rejected_mutation_count": sum(len(entry["rejected_mutations"]) for entry in rows),
            "Lean_authority": False,
            "scope": "Exact finite mathematical and synthetic real-validator controls; no release authority.",
            "rows": rows}


if __name__ == "__main__":
    print(json.dumps(run(), sort_keys=True))
