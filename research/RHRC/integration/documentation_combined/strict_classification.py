"""Check the strict donor's source and audit dispositions in the landed graph."""

from __future__ import annotations

import re
from pathlib import Path

from ...graph.views import reachability_view
from ...tools.lean_imports import import_modules
from ..documentation_2026_11_26.archive_scope import git, tree
from ..opica_composition.canonical import load_bytes, require

PREVIOUS = "4044e7335bc0499d77d6961a1bc20bdf46283224"
LANDING = "d649f57310bb05a306d3d488ba019e4ab45b0b20"
DONOR = "75c200a9c90f96c5b67e468afd1d8a3afeda4188"
CLASSES = "research/RHRC/graph/FILE_CLASSES.json"
SEMANTICS = "research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json"
PORT = "verification/opica-native-terminal/PORT_MANIFEST.json"
STRICT = "verification/opica-strict-step4/SOURCE_POLICY.json"
ADAPTER = "Zeta23Arithmetic/NativePrincipal.lean"


def donor_paths(repo):
    previous, landed, donor = (tree(repo, commit) for commit in (PREVIOUS, LANDING, DONOR))
    added = landed.keys() - previous.keys()
    require(len(added) == 952 and all(landed.get(p) == row for p, row in previous.items())
            and all(landed[p] == donor.get(p) for p in added), "Strict donor landing differs")
    return added


def exact_rules(added, ported):
    verification = {p for p in added if p.startswith(
        ("verification/opica-native-terminal/", "verification/opica-strict-step4/"))}
    fixtures = {p for p in verification if p.endswith(".lean")}
    scripts = {p for p in verification if p.endswith((".sh", ".py"))}
    metadata = {"Zeta23Arithmetic/LICENSE", "Zeta23Arithmetic/NOTICE"}
    require((len(ported), len(fixtures), len(scripts)) == (792, 36, 15)
            and ported | {ADAPTER} == {p for p in added if p.startswith("Zeta23Arithmetic/") and p.endswith(".lean")}
            and metadata <= added, "Unexpected strict donor file inventory")

    def rule(name, paths, file_class, trust_zone):
        return {"id": "opica_strict_donor_" + name,
                "pattern": r"\A(?:" + "|".join(re.escape(p) for p in sorted(paths)) + r")\Z",
                "file_class": file_class, "trust_zone": trust_zone}

    return [rule("arithmetic_port", ported, "LEAN_SOURCE", "UPSTREAM_DERIVED"),
            rule("arithmetic_adapter", {ADAPTER}, "LEAN_SOURCE", "AUXILIARY_FORMALIZATION"),
            rule("license", metadata, "LICENSE_OR_METADATA", "AUDIT_ONLY"),
            rule("staged_lean", fixtures, "RESEARCH_FIXTURE", "AUDIT_ONLY"),
            rule("verification_tools", scripts, "RESEARCH_EXECUTABLE", "AUDIT_ONLY")]


def donor_role(path, ported, strict_modules):
    if path in ported:
        return "UPSTREAM_DERIVED_STANDALONE"
    if path == ADAPTER:
        return "OPICA_SOURCE_BOUND_NATIVE_ADAPTER"
    if path.startswith("Zeta23/OPICANativeTerminal/"):
        return ("OPICA_DIRECT_ARITHMETIC_TYPE_AXIOM_AUDIT" if path.endswith("/AuditCore.lean")
                else "OPICA_DIRECT_ARITHMETIC_SUPPLIED_SOURCE")
    if path in strict_modules:
        if path.endswith(("Expected.lean", "Audit.lean")):
            return "OPICA_STRICT_SAME_OBSTRUCTION_TYPE_AXIOM_AUDIT"
        return "OPICA_STRICT_SAME_OBSTRUCTION_SUPPORTING_SOURCE"
    if path.startswith("Zeta23/OPICARound6/"):
        return ("OPICA6_FINITE_ARITHMETIC_AUDIT" if path.endswith("Verify.lean")
                else "OPICA6_FINITE_ARITHMETIC_SUPPORT")
    require(path.startswith("Zeta23/OPICASupport/"), "Undisposed strict donor module: " + path)
    return "POST290_SUPPORTING_SOURCE_COMPONENT"


def standalone_extension(repo, files, rules, added, ported, strict_modules, old_roles):
    # Independent source walk, using the same import parser and entrypoints as the graph.
    compiled = [(re.compile(r["pattern"]), r["file_class"]) for r in rules]
    modules = {}
    for path in files:
        file_class = next((c for pattern, c in compiled if pattern.search(path)), None)
        require(file_class is not None, "Unclassified tracked path: " + path)
        if file_class not in ("LEAN_ROOT", "LEAN_SOURCE"):
            continue
        require(path == "Zeta23.lean" or path.startswith(("Zeta23/", "Zeta23Arithmetic/", "comparator/")),
                "Unexpected local module root: " + path)
        name = path.removeprefix("comparator/").removesuffix(".lean").replace("/", ".")
        require(name not in modules, "Duplicate local module: " + name)
        modules[name] = path
    imports = {name: import_modules((repo / path).read_text(encoding="utf-8")) for name, path in modules.items()}
    comparators = [name for name, path in modules.items() if path.startswith("comparator/") and path.count("/") == 1]
    standalone = set(reachability_view(imports, comparators)["standalone_or_auxiliary"])
    require(set(old_roles) == {n for n in standalone if modules[n] not in added},
            "Historical standalone dispositions changed")
    roles = {n: donor_role(modules[n], ported, strict_modules) for n in sorted(standalone) if modules[n] in added}
    require(len(roles) == 878, "Unexpected number of standalone donor modules")
    return roles


def check_classification(repo: Path):
    repo = Path(repo)
    added = donor_paths(repo)
    old_classes, old_semantics = (load_bytes(git(repo, "show", PREVIOUS + ":" + p)) for p in (CLASSES, SEMANTICS))
    ported = {r["destination"] for r in load_bytes(git(repo, "show", DONOR + ":" + PORT))["modules"]}
    strict_modules = {r["path"] for r in load_bytes(git(repo, "show", DONOR + ":" + STRICT))["modules"]}
    rules = old_classes["rules"] + exact_rules(added, ported)
    require(load_bytes((repo / CLASSES).read_bytes()) == {**old_classes, "rules": rules},
            "Strict donor file classes or historical rules differ")
    old_roles = old_semantics["standalone_module_roles"]
    extension = standalone_extension(repo, tree(repo, "HEAD"), rules, added, ported, strict_modules, old_roles)
    expected = {**old_semantics, "standalone_module_roles": {**old_roles, **extension}}
    require(load_bytes((repo / SEMANTICS).read_bytes()) == expected, "Strict donor standalone dispositions differ")
    return {"added_paths": len(added), "standalone_donor_modules": len(extension), "terminal_claim": "RH_OPEN"}
