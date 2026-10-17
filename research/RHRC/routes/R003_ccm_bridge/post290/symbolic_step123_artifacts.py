"""Add source-bound symbolic indexes without performing semantic approval.

Exact compiler statements are copied, not reconstructed from prose.  All
descriptive maps below remain source-author review questions.  Conditional
objects have no invented coordinates; finite observations retain their full
original rows and never acquire the conditional object's properties.
"""
from __future__ import annotations

from copy import deepcopy
import hashlib
import json
from pathlib import Path

from build_step4_handoff import validated_formal_roots

SOURCE_ID = "frozen-universal-sinc-product-s0-1/4096"
FIELD_IDS = tuple(f"N{i:02d}" for i in range(1, 41)) + tuple(f"G{i:02d}" for i in range(1, 5))
DESCRIPTION = "SOURCE_AUTHOR_DESCRIPTION_REVIEW_PENDING"
SYMBOLIC_KIND = "SYMBOLIC_COMPILER_BOUND_DESCRIPTION"

# Descriptions point to the complete typed consumer statements, including
# their hypotheses. They are not an alternative theorem/type parser.
OBJECTS = (
    ("q_k_j", "fixed physical q; k=Pq; j=P^2q", "N01 N02 N03 N04", "fixed scale 1/4096; mass-one q"),
    ("original_trial", "original two-lobe phase trial f_sigma,a", "N05 N06 N07", "fixed positive original-trial normalization"),
    ("finite_precursor", "literal padded finite precursor and P-image at Kd=ceil(L^4)", "N08 N09 N10", "literal common DC padding; fixed endpoint order"),
    ("original_finite_p", "nativeOriginalDetectorPaddedUnit on its own original parity at Kd", "N11 N12 N13 N14 N15 N16", "true physical L2 norm one"),
    ("selected_ground_u", "the separately stored selected unit eigenvector at K_eta", "N17 N18 N19 N20 N21 N22 N23", "selected unit; original-trial properties are not transferred"),
    ("detector_schur", "original p split into predecessor at K_eta-1 and its FULL complement", "N24 N25", "original complement coordinate y is not renormalized"),
    ("ground_schur", "selected ground split at its one-dimensional successor shell", "N26", "actual eigenvalue lambda; distinct from detector shift -eta"),
    ("own_parity_residual", "actual own-parity neutral compressed residual of original p", "N27 N28", "own Rayleigh value; full complex channel Gram"),
    ("X_U", "literal von Mangoldt X=Pi*j and integer drive U=(tN)*j", "N29 N30", "unchanged coefficients and full initial history"),
    ("a_Y_A", "actual native floor kernel a, Y=c*U and damped causal L2 operator A_epsilon", "N31 N32 N33 N34", "actual damping/domain; no inverse assumed"),
    ("physical_response", "actual original finite-image physical response and predecessor forcing", "N35 N36 N37 N38", "own Kd; local physical L2 restriction only"),
    ("smooth_exterior", "original smooth response interior, left/right causal exterior and boundary history", "N39 N40", "original smooth trial; interior is retained"),
    ("generated_packet", "zero-indexed cofinal extension of the one retained native packet", "G01 G02 G03 G04", "hypothetical off-line zero remains a symbolic hypothesis"),
)
MAPS = (
    ("source_to_original_trial", "q_k_j", "original_trial", "N05 N06 N07", "definition and exact physical phase identities"),
    ("quantitative_finite_transport", "original_trial", "original_finite_p", "N08 N09 N10 N11 N12 N13 N14 N15 N16", "constructed image with errors; not exact equality to the original smooth trial"),
    ("retained_selection", "original_finite_p", "selected_ground_u", "N17 N18 N19 N20 N21 N23 N24", "threshold/least-crossing selection; not a linear map p to u"),
    ("original_detector_split", "original_finite_p", "detector_schur", "N25", "exact embeddings and completion of squares at -eta"),
    ("selected_shell_split", "selected_ground_u", "ground_schur", "N26", "one-shell eigen-equation at lambda"),
    ("native_convolution_and_forward", "X_U", "a_Y_A", "N29 N30 N31 N32 N33 N34", "N*X=U; a*X=Y on the legitimate initial domain"),
    ("original_forcing_bridge", "X_U", "physical_response", "N35 N36 N37 N38", "compact-test duality and finite error, all four signed histories"),
    ("original_exterior_reconstruction", "original_trial", "smooth_exterior", "N39 N40", "interior and full boundary histories retained; no contact asserted"),
)
LOST_PROPERTIES = (
    "No exact preservation of the original entire transform's zero divisor is supplied by finite transport.",
    "Trial phase, precursor positivity and higher jets are not transferred to the selected ground.",
    "Per-phase cofinal depth is not simultaneous depth or depth at every aperture.",
    "Selected-ground shell dimension one does not reduce the original detector complement to one dimension.",
    "The ground shift lambda and detector shift -eta are different.",
    "Legal-to-neutral pole-normal loss and outer Galerkin residual are distinct and need not vanish.",
    "Local response L2 and compact inverse duality do not give global exterior or prime-field L2.",
    "Original interior nonvanishing does not yield a full continuous contact generator.",
    "Forward contraction and finite residual decrease do not give range membership or zero terminal projection.",
)
DOMAINS = (
    ("fixed_source_and_phase", "N01 N02 N03 N04 N05 N06 N07", "fixed source; admissible a; original sigma; L=2a+2c"),
    ("finite_transport_threshold", "N08 N09 N10 N11 N12 N13 N14 N15 N16 N37 G02", "own Kd=ceil(L^4); actual paid common source-only threshold"),
    ("selector_and_inverse", "N17 N18 N19 N20 N24 N25 N26", "D=exp(beta L)>0; D/3<eta<D/2; g=D/[12(Kd-1)]; first nonempty predecessor handled separately"),
    ("own_parity_residual", "N27 N28", "original unit p in its actual neutral parity; same operator/source in both residual formulas"),
    ("native_arithmetic_and_range", "N29 N30 N31 N32 N33 N34 G04", "unchanged integer/prime coefficients; actual positive damping and legitimate causal domains"),
    ("forcing_and_history", "N35 N36 N37 N38 N39 N40", "original finite p versus original smooth f explicitly distinguished; compact test support; retained initial history"),
)
BRANCHES = (
    ("STRICT_EVEN", "N20 N21 N22", "even neutral bottom strictly smaller; even identities on the stored ground"),
    ("STRICT_ODD", "N20 N21 N22", "odd neutral bottom strictly smaller; actual adjoint-side signs, no even M4 conclusion"),
    ("TIE", "N20 N21 N23", "equal neutral bottoms; retained kernel component and positive-complement inverse; no singular full resolvent"),
    ("EMPTY_PREDECESSOR", "N18 N19 N25", "zero-space endomorphism/inverse clause; no minimum of an empty spectrum"),
)
RESIDUALS = (
    ("own_parity_variance_and_complex_gram", "N27 N28", "r=(T_sigma-r0 I)p; ||r||^2=Re sum_ij <r_i,r_j>; all off-diagonal complex terms retained"),
    ("native_signed_histories", "N35 N36", "Arch + Pole - PrimeForward - PrimeReflected, with all four literal translated/reflected histories and q*X bridge"),
    ("finite_projection_error", "N14 N37", "quantified source transport/projection error with actual finite-mode factor, eta and common paid threshold"),
    ("original_ambient_decomposition", "N38", "Response_local = neutral + pole-normal + outer Galerkin; full legal coordinate preserves original parity"),
    ("normal_and_outer_terms", "N38", "pole-normal lies on actual elementary-pole normal line and is orthogonal to neutral; outer is orthogonal to full legal; neither asserted zero"),
    ("original_detector_shift", "N35 N38", "Response_local + eta*p projects to stored b_eta on predecessor: spectral shift is -eta, not lambda"),
    ("smooth_interior_and_exterior_history", "N39 N40", "actual smooth original response = retained interior + left/right exterior, with compact boundary histories; interior is not AE zero"),
)
CUT_ROOTS = {
    "A-X": "Zeta23.ExceptionalZero.riemannHypothesis_of_originalPrimeField_allDampedIntegral",
    "B-Y": "Zeta23.ExceptionalZero.riemannHypothesis_of_nativeInput_allRangeClosure",
    "C-Schur": "Zeta23.ExceptionalZero.riemannHypothesis_of_detectorSchurLoss_subexponential",
}
PAPER_PORTS = (
    ("C05_FULL_KERNEL", "full continuous source-bound contact and full-kernel exterior exponent", "N38 N39 N40", "full native contact producer, legitimate interior condition and analytic exterior theorem"),
    ("A03_ARITHMETIC", "sharp signed cofactors, rough core, coprime mixed energy and angle/Gram observables", "N29 N30", "unchanged-coefficient decompositions, rearrangement/covariance estimates and sufficient native upper law"),
    ("GROWING_ENDPOINT_HIGH_JET", "growing endpoint order and separate selected-ground high jets", "N08 N09 N10 N14 N20", "uniform order-dependent budgets and an actual selected-ground moment producer"),
    ("MOVING_NEUTRAL_CARRIER", "aperture-dependent pole-neutral projector/ground calculus", "N20 N21 N22 N23", "carrier connection, projector derivatives, extra terms and tie/branch control"),
    ("STRONG_ADJOINT_LIMIT", "strong iteration convergence and terminal adjoint-kernel projection", "N33 N34", "strong-limit theorem with operator hypotheses; zero terminal projection remains a further condition"),
)
CONTROLS = (
    ("MODIFIED_PRIME_K3", "exact modified-first-prime pole-neutral K3 vector; M4=-720 and rational atom-sign margins", "unchanged complete divisor coefficient law; first failure must come from its actual receipt", "test_required_research_controls.py:MODIFIED_PRIME_K3 (pinned supplied script, actual PN eigenvectors, margins145/7 and25); test_native_divisor_controls.py"),
    ("DEGENERATE_TIE", "degenerate tied eigenspace with M4-null eigenvector", "simple-even hypothesis is absent; no rejection by native divisor law inferred", "test_strict_odd_and_tie_exact.py"),
    ("STRICT_ODD_AND_TIE", "actual strict-odd adjoint signs and singular-safe tied code paths", "even-only or nonsingular-resolvent substitution is ineligible", "test_strict_odd_and_tie_exact.py"),
    ("MOMENT_NULL_NOT_GROUND", "negative moment-null trial with nonzero actual residual", "trial-equals-ground substitution fails at the eigen-equation", "test_required_research_controls.py:MOMENT_NULL_NOT_GROUND (NEW exact K4 pole-neutral synthetic operator; no supplied historical instance identified)"),
    ("SHIFTED_RAY", "historical unrestricted shifted-ray sign falsifier at its exact hypotheses", "generic shifted-ray sign law only; no native conjunction exclusion", "research/RHRC/routes/R003_ccm_bridge/post287/wp6_k2_signed_ray_probe.py"),
    ("PAIR_D_SOURCE_ONLY", "prior Pair-D/source-only controls at their original hypothesis scope", "structural/source-only sufficiency only; no new native exclusion", "research/RHRC/countermodels/check_post204_pair_d_scope.py; research/RHRC/integration/test_source_only_dependency_extract.py"),
    ("CONTRACTIVE_RANGE_OBSTRUCTION", "positive contractive forward operator with native-frequency inverse/range obstruction", "forward norm below one does not imply inverse/range membership", "test_required_research_controls.py:GENERIC_CONTRACTIVE_RANGE_OBSTRUCTION (synthetic diag(1/2,0)); distinct NATIVE_FREQUENCY_NAIVE_ITERATION row retains unchanged native multiplier and NATIVE_PARAMETER_EVALUATION origin, falsifies only (I-A) iteration; test_actual_input_zero_jets.py is a separate actual-input witness control"),
    ("SOURCE_SHIFT_NORMAL_HISTORY", "source mismatch, wrong shift, omitted normal multiplier, phase conjugation and discarded history", "actual source/domain/normal/history identity must be matched before interpreting a rejection", "test_forcing_history.py; test_mandatory_mutation_matrix.py"),
)


def _index(formal, head, tree):
    if (formal.get("head") != head or formal.get("source_tree") != tree
            or formal.get("execution_status") != "SUCCESS"
            or formal.get("integrity_status") != "PASS"
            or formal.get("claim_cap") != "RH_OPEN"):
        raise ValueError("symbolic indexes require successful exact-source compiler evidence")
    _, audited = validated_formal_roots(formal, {"head": head, "tree": tree})
    if not audited:
        raise ValueError("symbolic indexes require populated audited compiler records")
    result = {}
    for group in ("declarations", "definitions"):
        for i, row in enumerate(formal.get(group, [])):
            name = row.get("declaration", row.get("theorem"))
            result[name] = (row, f"FORMAL_BINDINGS.json#/{group}/{i}")
    return result


def _binding(index, name):
    if name not in index:
        raise ValueError("missing exact compiler statement: " + name)
    row, ref = index[name]
    return {"declaration": name, "module": row["module"],
            "declaration_kind": row["declaration_kind"],
            "normalized_type": row["normalized_type"],
            "normalized_type_sha256": row["normalized_type_sha256"],
            "full_type_expr_sha256": row["full_type_expr_sha256"],
            "full_type_expr_format": row["full_type_expr_format"],
            "structure_constructor_types": [
                {k: ctor[k] for k in ("constructor", "full_type_expr_sha256", "full_type_expr_format")}
                for ctor in row["structure_constructor_types"]],
            "axioms": deepcopy(row["axioms"]), "compiler_record_ref": ref,
            "compiler_authority": "PROVED_COMPONENT_ONLY" if row["declaration_kind"] == "THEOREM" else "DEFINED_DATA_NOT_A_THEOREM",
            "field_contract_approved": False}


def build_symbolic_index(formal, dossier, head, tree):
    """Return descriptions plus exact compiler statements; no review flags change."""
    index = _index(formal, head, tree)
    fields = dossier.get("fields", [])
    if (len(fields) != 44 or {f.get("id") for f in fields} != set(FIELD_IDS)
            or dossier.get("authority") != "UNREVIEWED_COMPILER_CANDIDATES_ONLY"):
        raise ValueError("symbolic indexes need the original complete unapproved dossier")
    statements = []
    by_id = {field["id"]: field for field in fields}
    for field_id in FIELD_IDS:
        field = by_id[field_id]
        names = [r.get("name") for r in field.get("candidate_declarations", [])]
        consumer = "Zeta23.RHRC.consume" + field_id
        if consumer not in names or len(names) != len(set(names)):
            raise ValueError("missing/duplicate actual typed field consumer: " + field_id)
        statements.append({"id": field_id, "interpretation_status": DESCRIPTION,
                           "origin": "FORMAL_CONDITIONAL", "resolution": "SYMBOLIC_FORMAL",
                           "compiler_statements": [_binding(index, name) for name in names]})
    def described(identifier, refs, **data):
        return {"id": identifier, "source_id": SOURCE_ID,
                "origin": "FORMAL_CONDITIONAL", "resolution": "SYMBOLIC_FORMAL",
                "interpretation_status": DESCRIPTION, "field_refs": refs.split(), **data}
    return {
        "schema": "post290.symbolic-source-index.v1", "head": head, "tree": tree,
        "claim_cap": "RH_OPEN", "independent_semantic_approval": False,
        "compiler_statements": statements,
        "objects": [described(i, refs, description=d, normalization=n)
                    for i, d, refs, n in OBJECTS],
        "maps": [described(i, refs, from_object=f, to_object=t, description=d)
                 for i, f, t, refs, d in MAPS],
        "non_preservations": list(LOST_PROPERTIES),
        "domains": [described(i, refs, description=d) for i, refs, d in DOMAINS],
        "branch_eligibility": [described(i, refs, description=d) for i, refs, d in BRANCHES],
        "residual_rows": [described(i, refs, row_kind=SYMBOLIC_KIND, description=d,
                                    compiler_statement_refs=["CONSTRAINTS.json#/symbolic_constraints/compiler_statements/" + str(FIELD_IDS.index(ref)) for ref in refs.split()])
                          for i, refs, d in RESIDUALS],
        "conditional_sufficiency": [described(cut, "G03 G04" if cut != "C-Schur" else "G02 G03 N24 N25",
                                             antecedent_status="OPEN", compiler_statement=_binding(index, name))
                                    for cut, name in CUT_ROOTS.items()],
        "optional_paper_ports": [described(i, refs, authority="PAPER", status="OPEN",
                                           description=d, remaining_dependencies=missing,
                                           newly_formalized=False)
                                 for i, d, refs, missing in PAPER_PORTS],
    }


def finite_residual_rows(panel):
    """Keep every received field, including complex-zero and normal corrections."""
    rows = []
    for pair in panel.get("pairs", []):
        for row in pair.get("rows", []):
            if row.get("is_hypothetical_zero_generated_detector") is not False:
                raise ValueError("finite row must explicitly reject hypothetical-zero identity")
            if row.get("origin", "NATIVE_PARAMETER_EVALUATION") != "NATIVE_PARAMETER_EVALUATION":
                raise ValueError("synthetic/conditional origin cannot be relabelled as native")
            if row.get("source_id", SOURCE_ID) != SOURCE_ID:
                raise ValueError("modified source cannot be relabelled as fixed native source")
            if row.get("status") == "EVALUATED_NATIVE_PROBE":
                required = {"channel_names", "residual_gram_real", "residual_gram_imaginary",
                            "channel_rayleigh", "native_source", "residual_norm_sq",
                            "spectral_variance", "consistency"}
                if not required <= row.keys():
                    raise ValueError("truncated evaluated residual row")
                geometry = {"Q", "L", "a", "pole_normal_even_norm_sq", "pole_normal_odd_norm_sq"}
                if not geometry <= pair.keys():
                    raise ValueError("truncated evaluated pair geometry/normal terms")
            copied = deepcopy(row)
            copied.update(aperture=pair.get("aperture"), K=pair.get("K"),
                          row_kind="FINITE_NATIVE_PARAMETER_EVALUATION",
                          source_id=SOURCE_ID, source_identity=deepcopy(panel["source_identity"]),
                          origin="NATIVE_PARAMETER_EVALUATION",
                          resolution="CERTIFIED_INTERVAL" if row.get("status") == "EVALUATED_NATIVE_PROBE" else "UNRESOLVED",
                          mathematical_scope="FINITE_POINT_GRAM_ONLY_NOT_ORIGINAL_ZERO_GENERATED_DETECTOR")
            copied["pair_geometry"] = {key: deepcopy(pair[key]) for key in
                ("Q", "L", "a", "pole_normal_even_norm_sq", "pole_normal_odd_norm_sq", "symbolic_seam_receipt") if key in pair}
            rows.append(copied)
    return rows


def matched_control_inventory(survival):
    """Preserve genuine optional receipt bytes without inventing their verdict.

    An input entry names a catalog control_id, local receipt_path and its
    sha256; original payload/source identity is copied unchanged.  It is an
    evidence attachment, not an automatic matched-hypothesis approval.
    """
    supplied = survival.get("control_receipt_inputs", [])
    if not isinstance(supplied, list):
        raise ValueError("invalid optional control receipt inputs")
    received = {}
    for item in supplied:
        if not isinstance(item, dict) or item.get("control_id") in received:
            raise ValueError("duplicate/invalid control receipt input")
        identifier = item.get("control_id")
        if identifier not in {r[0] for r in CONTROLS}:
            raise ValueError("unknown control receipt identifier")
        path = Path(item["receipt_path"])
        raw = path.read_bytes()
        if hashlib.sha256(raw).hexdigest() != item.get("sha256"):
            raise ValueError("control receipt byte hash mismatch")
        payload = json.loads(raw)
        if not isinstance(payload, dict):
            raise ValueError("control receipt must be an object")
        if any(payload.get(k, "RH_OPEN") not in ("RH_OPEN", "OPEN")
               for k in ("claim_cap", "terminal_claim", "RH_status")):
            raise ValueError("control receipt violates claim firewall")
        received[identifier] = {"input_provenance": deepcopy(item), "receipt_byte_count": len(raw),
                                "original_receipt": payload}
    return [{"id": i, "origin": "NATIVE_PARAMETER_EVALUATION" if i == "SHIFTED_RAY" else "SYNTHETIC_CONTROL", "source_model_tag": i,
             "matched_hypotheses_to_review": hypotheses,
             "first_incompatible_identity_or_scope_limit_to_review": identity,
             "registered_control_sources": source,
             "assessment": "RECEIPT_ATTACHED_MATCHED_HYPOTHESES_REVIEW_PENDING" if i in received else "UNRESOLVED_RECEIPT_NOT_SUPPLIED",
             "first_proved_incompatible_identity": None,
             "no_native_conjunction_exclusion_inferred": True,
             "receipt_evidence": received.get(i),
             "resolution": "UNRESOLVED"}
            for i, hypotheses, identity, source in CONTROLS]
