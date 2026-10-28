"""Strict, bounded certificate input and fail-closed evidence classification.

Schema validation checks shape. Only an independently configured recomputation
can establish CERTIFIED_FINITE. Python never manufactures Lean theorem authority.
"""
from __future__ import annotations

from collections.abc import Callable, Mapping
from copy import deepcopy
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
from typing import Any, NamedTuple

HERE = Path(__file__).resolve().parent
MAX_BYTES = 4 * 1024 * 1024
MAX_ITEMS = 100_000
MAX_NODES = 1_000_000
# Explicit callers may select a larger bounded structure budget. Ordinary
# certificates, schema checks and canonical hashes retain MAX_NODES by default.
MAX_EXPLICIT_NODES = 8_000_000
MAX_INPUT_RATIONAL_CHARS = 180
# Generated Arb bounds and sums of their dyadic endpoints can exceed the input
# coefficient budget even at supported precision. This separate finite budget
# covers their serialization without rounding; precision alone does not bound
# exponents, so larger endpoints still fail closed. JSON byte/node caps remain.
MAX_ENDPOINT_RATIONAL_CHARS = 4096
INTEGER = re.compile(r"-?(?:0|[1-9][0-9]*)\Z")
RATIONAL = re.compile(r"-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?\Z")
HASH = re.compile(r"[0-9a-f]{64}\Z")


class InvalidCertificate(ValueError):
    def __init__(self, code: str, message: str):
        super().__init__(message)
        self.code = code


class UnsupportedCertification(InvalidCertificate):
    """Well-formed evidence whose independent analytic verifier is unavailable."""


class SchemaDefinitionError(ValueError):
    pass


def require(ok: bool, code: str, message: str) -> None:
    if not ok:
        raise InvalidCertificate(code, message)


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        require(key not in result, "duplicate_key", "Duplicate JSON key: " + key)
        result[key] = value
    return result


def _reject_number(value: str) -> None:
    raise InvalidCertificate("noncanonical_number", "Use canonical integer or rational strings, not " + value)


def _json_integer(value: str) -> int:
    require(len(value) <= 180, "integer_size", "JSON integer exceeds the resource limit")
    require(value != "-0", "noncanonical_number", "Negative zero is not a canonical JSON integer")
    return int(value)


def _bounded_tree(value: Any, *, max_nodes: int = MAX_NODES) -> None:
    require(type(max_nodes) is int and 0 < max_nodes <= MAX_EXPLICIT_NODES,
            "node_limit", "Invalid JSON structure budget")
    pending = [(value, 0)]
    nodes = 0
    while pending:
        item, depth = pending.pop()
        nodes += 1
        require(nodes <= max_nodes and depth <= 64, "structure_size", "JSON structure exceeds limits")
        if type(item) is dict:
            require(len(item) <= MAX_ITEMS, "object_size", "Too many object members")
            require(all(type(k) is str and len(k) <= 1024 for k in item), "key_size", "Invalid object key")
            pending.extend((v, depth + 1) for v in item.values())
        elif type(item) is list:
            require(len(item) <= MAX_ITEMS, "array_size", "Too many array entries")
            pending.extend((v, depth + 1) for v in item)
        elif type(item) is str:
            require(len(item) <= 1024 * 1024, "string_size", "String exceeds resource limit")
        else:
            require(item is None or type(item) in (bool, int), "unsupported_value", "Unsupported JSON value")
            if type(item) is int:
                require(item.bit_length() <= 600 and len(str(item)) <= 180,
                        "integer_size", "JSON integer exceeds the resource limit")


def loads_strict_json(data: bytes | str, max_bytes: int = MAX_BYTES, *,
                      max_nodes: int = MAX_NODES) -> Any:
    require(type(max_bytes) is int and 0 < max_bytes <= 64 * MAX_BYTES,
            "byte_limit", "Invalid JSON byte limit")
    raw = data.encode("utf-8") if type(data) is str else data
    require(type(raw) is bytes and len(raw) <= max_bytes, "file_size", "JSON input exceeds byte limit")
    try:
        text = raw.decode("utf-8", errors="strict")
        obj = json.loads(text, object_pairs_hook=_unique_object, parse_float=_reject_number,
                         parse_constant=_reject_number, parse_int=_json_integer)
    except (UnicodeError, json.JSONDecodeError, RecursionError) as exc:
        raise InvalidCertificate("invalid_json", str(exc)) from exc
    _bounded_tree(obj, max_nodes=max_nodes)
    return obj


def load_strict_json(path: Path | str, max_bytes: int = MAX_BYTES, *,
                     max_nodes: int = MAX_NODES) -> Any:
    require(type(max_bytes) is int and 0 < max_bytes <= 64 * MAX_BYTES,
            "byte_limit", "Invalid JSON byte limit")
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), "input_path", "Regular JSON file required")
    require(path.stat().st_size <= max_bytes, "file_size", "JSON file exceeds byte limit")
    with path.open("rb") as handle:
        data = handle.read(max_bytes + 1)
    return loads_strict_json(data, max_bytes, max_nodes=max_nodes)


def canonical_bytes(obj: Any, *, max_nodes: int = MAX_NODES) -> bytes:
    _bounded_tree(obj, max_nodes=max_nodes)
    return json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(",", ":"),
                      allow_nan=False).encode("utf-8")


def canonical_sha256(obj: Any, *, max_nodes: int = MAX_NODES) -> str:
    return hashlib.sha256(canonical_bytes(obj, max_nodes=max_nodes)).hexdigest()


def parse_integer(value: Any, *, minimum: int | None = None, maximum: int | None = None) -> int:
    require(type(value) is str and len(value) <= 180 and INTEGER.fullmatch(value) is not None,
            "integer", "Canonical decimal integer string required")
    result = int(value)
    require(str(result) == value, "integer", "Noncanonical integer string")
    require(minimum is None or minimum <= result, "integer_range", "Integer below allowed minimum")
    require(maximum is None or result <= maximum, "integer_range", "Integer above allowed maximum")
    return result


def _parse_rational(value: Any, max_chars: int, *, nonnegative: bool) -> Fraction:
    require(type(value) is str and len(value) <= max_chars and RATIONAL.fullmatch(value) is not None,
            "rational", "Canonical rational string required")
    result = Fraction(value)
    require(str(result) == value, "rational", "Rational must be reduced and canonical")
    require(not nonnegative or result >= 0, "negative_budget", "Negative budget or squared norm")
    return result


def parse_rational(value: Any, *, nonnegative: bool = False) -> Fraction:
    """Parse a user coefficient/parameter with the original 180-character cap."""
    return _parse_rational(value, MAX_INPUT_RATIONAL_CHARS, nonnegative=nonnegative)


def parse_endpoint_rational(value: Any, *, nonnegative: bool = False) -> Fraction:
    """Parse an exact generated bound/budget; at most 4096 canonical characters."""
    return _parse_rational(value, MAX_ENDPOINT_RATIONAL_CHARS, nonnegative=nonnegative)


class RationalComplex(NamedTuple):
    re: Fraction
    im: Fraction


def parse_complex(value: Any) -> RationalComplex:
    require(type(value) is dict and set(value) == {"re", "im"},
            "complex", "Complex rational must have exactly re and im")
    return RationalComplex(parse_rational(value["re"]), parse_rational(value["im"]))


# Deliberately limited to the closed JSON Schema vocabulary used by this package.
# Unknown schema keywords fail; this evaluator never silently ignores a constraint.
_SCHEMA_KEYS = {"$schema", "description", "type", "properties", "required", "additionalProperties",
                "items", "minItems", "maxItems", "uniqueItems", "pattern", "minLength", "maxLength",
                "minimum", "maximum", "enum", "const", "anyOf", "allOf", "if", "then"}
_TYPES = {"object": dict, "array": list, "string": str, "integer": int, "boolean": bool, "null": type(None)}


def validate_schema_definition(schema: Any) -> None:
    if type(schema) is not dict or not set(schema) <= _SCHEMA_KEYS:
        raise SchemaDefinitionError("Unsupported or malformed schema keywords")
    types = schema.get("type")
    if types is not None:
        choices = types if type(types) is list else [types]
        if not choices or any(type(t) is not str or t not in _TYPES for t in choices):
            raise SchemaDefinitionError("Unsupported schema type")
    props = schema.get("properties", {})
    if type(props) is not dict or any(type(key) is not str for key in props):
        raise SchemaDefinitionError("Schema properties must be an object")
    for sub in props.values():
        validate_schema_definition(sub)
    if "required" in schema:
        required = schema["required"]
        if (type(required) is not list or any(type(x) is not str for x in required)
                or len(set(required)) != len(required) or not set(required) <= set(props)):
            raise SchemaDefinitionError("Malformed required property list")
    if "additionalProperties" in schema and type(schema["additionalProperties"]) is not bool:
        raise SchemaDefinitionError("Only Boolean additionalProperties is supported")
    if "uniqueItems" in schema and type(schema["uniqueItems"]) is not bool:
        raise SchemaDefinitionError("Boolean uniqueItems is required")
    if "items" in schema:
        validate_schema_definition(schema["items"])
    for key in ("anyOf", "allOf"):
        if key in schema:
            if type(schema[key]) is not list or not schema[key]:
                raise SchemaDefinitionError("Nonempty schema alternative list required")
            for sub in schema[key]:
                validate_schema_definition(sub)
    for key in ("if", "then"):
        if key in schema:
            validate_schema_definition(schema[key])
    if "then" in schema and "if" not in schema:
        raise SchemaDefinitionError("then without if")
    for key in ("minItems", "maxItems", "minLength", "maxLength"):
        if key in schema and (type(schema[key]) is not int or schema[key] < 0):
            raise SchemaDefinitionError("Nonnegative integer schema limit required")
    for key in ("minimum", "maximum"):
        if key in schema and type(schema[key]) is not int:
            raise SchemaDefinitionError("Integer schema bound required")
    for low, high in (("minItems", "maxItems"), ("minLength", "maxLength"), ("minimum", "maximum")):
        if low in schema and high in schema and schema[low] > schema[high]:
            raise SchemaDefinitionError("Reversed schema bounds")
    if "pattern" in schema:
        if type(schema["pattern"]) is not str:
            raise SchemaDefinitionError("String schema pattern required")
        try:
            re.compile(schema["pattern"])
        except re.error as exc:
            raise SchemaDefinitionError("Invalid schema pattern") from exc
    if "enum" in schema and (type(schema["enum"]) is not list or not schema["enum"]):
        raise SchemaDefinitionError("Nonempty enum required")


def _same_json(a: Any, b: Any) -> bool:
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return set(a) == set(b) and all(_same_json(a[k], b[k]) for k in a)
    if type(a) is list:
        return len(a) == len(b) and all(_same_json(x, y) for x, y in zip(a, b))
    return a == b


def validate_schema(obj: Any, schema: dict[str, Any]) -> None:
    validate_schema_definition(schema)

    def check(value: Any, rule: dict[str, Any], where: str) -> None:
        if "type" in rule:
            kinds = rule["type"] if type(rule["type"]) is list else [rule["type"]]
            require(any(type(value) is _TYPES[t] for t in kinds), "schema_type", where + ": wrong type")
        if "const" in rule:
            require(_same_json(value, rule["const"]), "schema_const", where + ": wrong constant")
        if "enum" in rule:
            require(any(_same_json(value, x) for x in rule["enum"]), "schema_enum", where + ": unknown tag")
        if "anyOf" in rule:
            matched = False
            for sub in rule["anyOf"]:
                try:
                    check(value, sub, where)
                except InvalidCertificate:
                    continue
                matched = True
                break
            require(matched, "schema_any_of", where + ": no schema alternative matches")
        for sub in rule.get("allOf", []):
            check(value, sub, where)
        if "if" in rule:
            try:
                check(value, rule["if"], where)
            except InvalidCertificate:
                pass
            else:
                if "then" in rule:
                    check(value, rule["then"], where)
        if type(value) is dict:
            props = rule.get("properties", {})
            require(set(rule.get("required", [])) <= set(value), "schema_required", where + ": missing fields")
            if rule.get("additionalProperties") is False:
                require(set(value) <= set(props), "schema_extra", where + ": unknown fields")
            for key, sub in props.items():
                if key in value:
                    check(value[key], sub, where + "." + key)
        if type(value) is list:
            require(len(value) >= rule.get("minItems", 0), "schema_array", where + ": too few entries")
            require(len(value) <= rule.get("maxItems", MAX_ITEMS), "schema_array", where + ": too many entries")
            if rule.get("uniqueItems"):
                require(len({canonical_bytes(x) for x in value}) == len(value), "schema_unique", where + ": duplicate entries")
            if "items" in rule:
                for i, item in enumerate(value):
                    check(item, rule["items"], where + "[" + str(i) + "]")
        if type(value) is str:
            require(len(value) >= rule.get("minLength", 0) and len(value) <= rule.get("maxLength", MAX_BYTES),
                    "schema_string", where + ": string length out of range")
            if "pattern" in rule:
                pattern = rule["pattern"]
                match = re.fullmatch(pattern, value) if pattern.startswith("^") and pattern.endswith("$") else re.search(pattern, value)
                require(match is not None, "schema_pattern", where + ": invalid string")
        if type(value) is int:
            require(value >= rule.get("minimum", value) and value <= rule.get("maximum", value),
                    "schema_number", where + ": number out of range")

    _bounded_tree(obj)
    check(obj, schema, "$")


def _schema(name: str) -> dict[str, Any]:
    value = load_strict_json(HERE / "schemas" / name)
    validate_schema_definition(value)
    return value


def validate_certificate(obj: Any, expected_source: Mapping[str, Any] | None = None, *,
                         independent_checker: Callable[[dict[str, Any]], Mapping[str, Any]] | None = None,
                         expected_checker_sha256: str | None = None,
                         approved_analytic_dependencies: Mapping[str, Mapping[str, str]] | None = None) -> dict[str, Any]:
    """Validate input; finite analytic acceptance additionally needs recomputation.

    The configured source, checker digest and analytic registry are trusted caller
    configuration, never values chosen from this input certificate itself.
    """
    schema = _schema("certificate.schema.json")
    validate_schema(obj, schema)
    require(expected_source is not None and dict(expected_source) == obj["source"],
            "source_identity", "Certificate must match independently configured source identity")
    validate_schema(dict(expected_source), schema["properties"]["source"])
    require(type(obj["source"]["source_product_copies"]) is int, "source_copy", "Boolean source copy is invalid")
    indices = [parse_integer(x, minimum=1, maximum=10**12) for x in obj["dictionary_indices"]]
    require(indices == sorted(set(indices)), "dictionary_indices", "Dictionary indices must be strictly increasing")
    coefficients = [parse_complex(x) for x in obj["coefficients"]]
    require(len(indices) == len(coefficients), "column_count", "Index/coefficient counts differ")
    region = {k: parse_rational(v) for k, v in obj["region"].items()}
    require(0 < region["delta_lower"] <= region["delta_upper"] < Fraction(1, 2),
            "region", "Region must lie strictly in 0<delta<1/2")
    require(0 <= region["abs_tau_lower"] <= region["abs_tau_upper"],
            "region", "Invalid absolute ordinate region")
    lag = parse_rational(obj["kernel_lag_horizon"], nonnegative=True)
    horizon = parse_rational(obj["absolute_output_horizon"], nonnegative=True)
    require(lag > 0 and horizon > lag, "horizons", "Positive distinct lag and output horizons required")
    require(obj["source_prefix_M"] <= 1_000_000, "source_prefix_limit", "Source prefix exceeds resource limit")
    budgets = {k: parse_endpoint_rational(v, nonnegative=True) for k, v in obj["error_budget"].items()}
    require(budgets["filter_operator_norm_upper"] > 0, "filter_norm", "Nonzero filter needs positive norm upper")
    # Each component is an absolute error in the final output norm. Any filter
    # multiplication must already be included by the independent analytic checker.
    names = ("source_norm_error", "kernel_lag_norm_error", "output_target_tail_norm_error",
             "quadrature_norm_error", "rounding_norm_error")
    require(budgets["total_norm_error"] >= sum((budgets[k] for k in names), Fraction()),
            "incomplete_budget", "Total norm budget does not cover all components")
    upper = parse_endpoint_rational(obj["upper_square"], nonnegative=True)
    lower = parse_endpoint_rational(obj["witness_lower_square"], nonnegative=True)
    names_seen: set[str] = set()
    for dep in obj["analytic_dependencies"]:
        require(dep["declaration"] not in names_seen, "duplicate_dependency", "Duplicate analytic dependency")
        names_seen.add(dep["declaration"])
    if obj["outcome"] == "KERNEL_CHECKED_THEOREM":
        raise UnsupportedCertification("kernel_authority", "Only an exact Lean compiler receipt can establish theorem authority")
    if obj["outcome"] == "EXACT_FINITE_ARITHMETIC":
        raise UnsupportedCertification("finite_route", "Use the independent fixed-baseline checker for exact finite arithmetic")
    if obj["outcome"] == "NO_CERTIFICATE":
        require(upper >= lower, "outcome", "NO_CERTIFICATE requires upper >= lower")
    if obj["outcome"] == "CERTIFIED_FINITE":
        if independent_checker is None or expected_checker_sha256 is None or approved_analytic_dependencies is None:
            raise UnsupportedCertification("independent_checker_required", "Independent analytic recomputation is required")
        require(HASH.fullmatch(expected_checker_sha256) is not None
                and obj["checker_sha256"] == expected_checker_sha256,
                "checker_identity", "Checker does not match configured implementation")
        for dep in obj["analytic_dependencies"]:
            require(approved_analytic_dependencies.get(dep["declaration"]) ==
                    {k: dep[k] for k in ("type_sha256", "compiler_receipt_sha256")},
                    "analytic_identity", "Unaccepted analytic theorem dependency")
        before = canonical_sha256(obj)
        checker_input = deepcopy(obj)
        recomputed = independent_checker(checker_input)
        require(canonical_sha256(checker_input) == before and canonical_sha256(obj) == before,
                "checker_mutation", "Independent checker mutated the certificate input")
        require(type(recomputed) is dict and set(recomputed) ==
                {"certificate_sha256", "upper_square", "witness_lower_square", "total_norm_error"},
                "checker_result", "Independent checker returned incomplete evidence")
        require(recomputed["certificate_sha256"] == canonical_sha256(obj), "stale_checker", "Checker evidence is stale")
        require(parse_endpoint_rational(recomputed["upper_square"], nonnegative=True) == upper
                and parse_endpoint_rational(recomputed["witness_lower_square"], nonnegative=True) == lower
                and parse_endpoint_rational(recomputed["total_norm_error"], nonnegative=True) == budgets["total_norm_error"],
                "checker_bounds", "Certificate differs from independent recomputation")
        require(0 <= upper < lower, "no_strict_margin", "Rigorous upper does not beat witness lower")
        authority = "CERTIFIED_FINITE_NOT_LEAN"
    else:
        authority = "VALIDATED_INPUT_ONLY_NO_ANALYTIC_AUTHORITY"
    return {"status": "VALIDATED", "claimed_outcome": obj["outcome"], "authority": authority,
            "certificate_sha256": canonical_sha256(obj), "upper_square": str(upper),
            "witness_lower_square": str(lower), "RH": "OPEN", "Step4": "OPEN"}


def failure_envelope(stage: str, error: Exception, *, source_identity: dict[str, str] | None = None,
                     outcome: str | None = None) -> dict[str, Any]:
    if outcome is None:
        outcome = "UNRESOLVED" if isinstance(error, UnsupportedCertification) else "INVALID_CERTIFICATE"
    obj = {"schema": "OPICA2_FAILURE_V1", "outcome": outcome, "stage": stage,
           "code": getattr(error, "code", "runtime_error"), "message": (str(error) or type(error).__name__)[:4096],
           "observed_at_utc": datetime.now(timezone.utc).isoformat(),
           "source_identity": source_identity, "artifact_hashes": [],
           "has_proof_authority": False, "full_core_accepted": False,
           "full_release_accepted": False, "RH": "OPEN", "Step4": "OPEN"}
    validate_failure_envelope(obj)
    return obj


def validate_failure_envelope(obj: Any) -> None:
    validate_schema(obj, _schema("failure.schema.json"))
    try:
        observed = datetime.fromisoformat(obj["observed_at_utc"].replace("Z", "+00:00"))
    except ValueError as exc:
        raise InvalidCertificate("failure_timestamp", "Invalid UTC observation time") from exc
    require(observed.tzinfo is not None and observed.utcoffset().total_seconds() == 0,
            "failure_timestamp", "Failure observation must use an explicit UTC offset")

