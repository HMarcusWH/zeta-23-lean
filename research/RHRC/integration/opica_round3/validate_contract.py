"""Round 3's closed source extension and scoped, independent proof checks.

Source inspection and exact synthetic falsifiers grant no theorem authority.
Only actual Lean commands establish the named declarations on the checked head.
Neither path grants full-release acceptance or an independent closing inequality.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
from typing import Any

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
BASE = "775692f2e72d76b6a97cf66926a86cc96342c109"
BASE_TREE = "acd548eb97ddaee68eb6c9df73f82756ee10d13f"
PREFIX = "research/RHRC/integration/opica_round3/"
DESCRIPTOR = PREFIX + "DESCENDANT_EXTENSION.json"
PROVIDER = PREFIX + "validate_contract.py"
R2 = "research/RHRC/integration/opica_round2/"
ROOT_NAMES = (
    "neutral_parity_cover_of_off_line_zero",
    "cofinally_both_neutral_negative_of_off_line_zero",
    "cofinally_uniform_neutral_interval_of_off_line_zero",
    "first_simultaneous_neutral_negative_cutoff",
)
MODULES = ("NeutralParityCover", "CofinalSimultaneousNegative", "UniformNeutralInterval",
           "FirstSimultaneousNegative")
MATH_MODULES = ("NeutralParityCover", "NeutralParityTopology", "CofinalSimultaneousNegative",
                "UniformNeutralInterval", "FirstNeutralCutoff", "KernelSafeSchur",
                "FirstSimultaneousNegative")
ADDITIONS = frozenset(
    ["Zeta23/OPICARound3/" + n + ".lean" for n in MATH_MODULES]
    + ["Zeta23/OPICARound3/Validation/" + n + ".lean" for n in MODULES]
    + ["Zeta23/OPICARound3.lean", "Zeta23/OPICARound3/All.lean",
       "Zeta23/OPICARound3/Validation.lean", "Zeta23/RHRC/OpicaRound3Bindings.lean",
       ".github/workflows/rhrc_opica_round3.yml"]
    + [PREFIX + n for n in ("README.md", "PUBLIC_ROOTS.json", "SOURCE_REGISTER.json",
       "OPEN_RESEARCH.json", "POST_GREEN_RESEARCH.md", "DESCENDANT_EXTENSION.json",
       "validate_contract.py", "tests/test_contract.py")]
    + [PREFIX + "paper/" + n for n in ("draft_spec.md", "proposed_contracts.json",
       "ucdp_research_report.md", "first_neutral_bad_one_shell_schur.md",
       "first_simultaneous_neutral_cutoff.md")])
EDITS = frozenset([
    "Zeta23/RHRC/RegisteredClaimBindings.lean", "research/RHRC/CLAIM_REGISTRY.json",
    "research/RHRC/REGISTERED_THEOREM_BINDINGS.json", "research/RHRC/graph/FILE_CLASSES.json",
    "research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json", ".github/workflows/rhrc_opica_round2.yml",
] + [R2 + n for n in ("certificate_io.py", "primal_certifier.py", "gram_diagnostics.py",
    "schemas/certificate.schema.json", "tests/test_certificate_io.py", "tests/test_primal_certifier.py",
    "tests/test_gram.py", "ancestor_projection.py", "validate_contract.py")])
EDITS = EDITS | frozenset({R2 + "tests/test_file_classes.py", R2 + "tests/test_receipt.py"})
SHA = re.compile(r"[0-9a-f]{64}\Z")
CAPS = {"full_core_accepted": False, "full_release_accepted": False,
        "human_review": "NOT_ESTABLISHED", "RH": "OPEN", "Step4": "OPEN"}
PREMISES = {
    "R3-D01": ["actual_off_line_zero", "strict_eventual_aperture", "complete_weil_form",
                "physical_neutral_parities"],
    "R3-D02": ["actual_off_line_zero", "complete_weil_form", "physical_neutral_parities",
                "open_parity_negative_sets", "individual_cofinality", "eventual_union_cover",
                "connected_halfline", "same_aperture", "common_cutoff_by_nesting"],
    "R3-D03": ["actual_simultaneous_strict_witnesses", "moving_neutral_continuity",
                "constructed_unit_frame", "fixed_cutoff_on_chosen_interval",
                "interval_specific_positive_margin", "complete_complex_span_bound"],
    "R3-D04": ["least_parity_cutoffs", "maximum_simultaneous_cutoff", "newborn_only_psd",
                "empty_predecessor_boundary", "one_dimensional_successor_shell",
                "kernel_projected_coupling", "regular_or_resonant_schur"],
}
FORBIDDEN = frozenset(("cofinality_only", "unprojected_output_residual", "both_predecessors_psd",
                       "equal_cutoffs_imply_spectral_tie", "globally_uniform_eta",
                       "desired_frame_assumed", "imported_false_source_sign"))


class InvalidContract(ValueError):
    pass


def need(condition: bool, message: str) -> None:
    if not condition:
        raise InvalidContract(message)


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def strict_json(raw: bytes) -> Any:
    def pairs(rows):
        out = {}
        for key, value in rows:
            need(key not in out, "Duplicate JSON key: " + key)
            out[key] = value
        return out
    return json.loads(raw.decode("utf-8"), object_pairs_hook=pairs,
                      parse_constant=lambda value: (_ for _ in ()).throw(InvalidContract("Nonfinite JSON")))


def read_json(path: Path) -> Any:
    need(path.stat().st_size <= 32 * 1024 * 1024, "Oversized metadata")
    return strict_json(path.read_bytes())


def relative(value: Any) -> str:
    need(type(value) is str and bool(value) and "\\" not in value and ":" not in value,
         "Canonical relative POSIX path required")
    p = PurePosixPath(value)
    need(not p.is_absolute() and ".." not in p.parts and "." not in value.split("/")
         and p.as_posix() == value, "Unsafe relative path")
    return value


def git(repo: Path, *args: str) -> bytes:
    env = {**os.environ, "GIT_NO_LAZY_FETCH": "1", "GIT_TERMINAL_PROMPT": "0"}
    result = subprocess.run(["git", "-C", str(repo), *args], capture_output=True, timeout=120, env=env)
    need(result.returncode == 0, "Read-only Git inspection failed: " + " ".join(args))
    return result.stdout


def git_text(repo: Path, *args: str) -> str:
    return git(repo, *args).decode("utf-8").strip()


def base_inventory(repo: Path) -> dict[str, tuple[str, str]]:
    need(git_text(repo, "rev-parse", BASE + "^{tree}") == BASE_TREE, "Round 2 base tree changed")
    git(repo, "merge-base", "--is-ancestor", BASE, "HEAD")
    rows = {}
    for entry in git(repo, "ls-tree", "-rz", BASE).split(b"\0"):
        if not entry:
            continue
        header, name = entry.split(b"\t", 1)
        mode, kind, blob = header.decode("ascii").split()
        path = relative(name.decode("utf-8"))
        need(mode in ("100644", "100755") and kind == "blob" and path not in rows,
             "Unexpected base tree entry")
        rows[path] = (mode, blob)
    need(bool(rows), "Missing base inventory")
    return rows


def path_policy(repo: Path) -> dict[str, Any]:
    manifest = strict_json(git(repo, "show", BASE + ":" + R2 + "BUILD_MANIFEST.json"))
    generated = sorted(relative(row["path"]) for row in manifest["generated"])
    need(len(generated) == 81 and len(set(generated)) == 81, "Frozen 81-product inventory changed")
    need(not (ADDITIONS & EDITS or (ADDITIONS | EDITS) & set(generated)), "Overlapping source policies")
    return {"base": BASE, "base_tree": BASE_TREE, "additions": sorted(ADDITIONS),
            "edits": sorted(EDITS), "generated": generated}


def policy_digest(policy: dict[str, Any]) -> str:
    return hashlib.sha256(json.dumps(policy, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def validate_descriptor(doc: Any, policy: dict[str, Any]) -> dict[str, dict[str, Any]]:
    need(type(doc) is dict and set(doc) == {"schema", "state", "policy", "path_policy_sha256", "files",
         "premise_contracts", "authority", *CAPS}, "Closed Round 3 descriptor required")
    need(doc["schema"] == "OPICA3_DESCENDANT_EXTENSION_V1" and doc["state"] == "FROZEN",
         "Round 3 descriptor is not finalized")
    need(doc["policy"] == policy and doc["path_policy_sha256"] == policy_digest(policy),
         "Round 3 audited path policy differs")
    need(doc["premise_contracts"] == PREMISES and doc["authority"] == "SOURCE_SCOPE_ONLY",
         "Premise declarations or authority changed")
    need(all(doc.get(key) == value and type(doc.get(key)) is type(value) for key, value in CAPS.items()),
         "Descriptor attempts to promote theorem/release authority")
    # Producer outputs hash authored sources, including this descriptor. Pinning
    # their bytes back into it would require a cryptographic fixed point.
    # Their exact scope stays closed here; canonical receipts/source freezes
    # authenticate their bytes independently.
    expected = (ADDITIONS | EDITS) - {DESCRIPTOR}
    need(type(doc["files"]) is list and len(doc["files"]) == len(expected), "Incomplete pinned source inventory")
    rows = {}
    for row in doc["files"]:
        need(type(row) is dict and set(row) == {"path", "sha256", "bytes"}, "Closed source record required")
        path = relative(row["path"])
        need(path in expected and path not in rows, "Unknown/duplicate pinned source path")
        need(type(row["sha256"]) is str and SHA.fullmatch(row["sha256"]) is not None
             and type(row["bytes"]) is int and row["bytes"] >= 0, "Invalid source hash/length")
        rows[path] = row
    need(set(rows) == expected, "Missing source pin")
    return rows


def check_claim_extension(old: Any, new: Any, key: str, public: dict[str, Any]) -> None:
    need(type(old) is dict and type(new) is dict and set(old) == set(new), "Registry shape changed")
    need({k: v for k, v in old.items() if k != key} == {k: v for k, v in new.items() if k != key},
         "Original registry metadata changed")
    def index(doc):
        need(type(doc[key]) is list, "Registry rows required")
        out = {}
        for row in doc[key]:
            need(type(row) is dict and type(row.get("id")) is str and row["id"] not in out,
                 "Malformed/duplicate registry row")
            out[row["id"]] = row
        return out
    before, after = index(old), index(new)
    need(all(after.get(cid) == row for cid, row in before.items()), "An original claim/binding drifted")
    expected = {row["claim_id"]: row for row in public["roots"]}
    need(set(after) - set(before) == set(expected), "Exactly four new Round 3 registry rows required")
    for cid, root in expected.items():
        need(after[cid].get("theorem") == root["theorem"] and after[cid].get("source") == root["source"],
             "New registry identity differs from public root")
        if key == "claims":
            need(after[cid].get("status") == "PROVED_UNCONDITIONAL"
                 and after[cid].get("promotion_cap") == "PROVED_UNCONDITIONAL",
                 "Supporting claim authority differs")


def check_public(doc: Any) -> None:
    need(type(doc) is dict and doc.get("schema") == "OPICA3_PUBLIC_ROOTS_V1", "Unknown public root schema")
    need(doc.get("RH") == doc.get("Step4") == "OPEN" and doc.get("full_release_accepted") is False,
         "Public root claim firewall changed")
    need(type(doc.get("roots")) is list and len(doc["roots"]) == 4, "Exactly four required roots")
    for i, (row, name, module) in enumerate(zip(doc["roots"], ROOT_NAMES, MODULES), 1):
        expected = {"id": f"R3-D{i:02d}", "claim_id": f"OPICA3_D{i:02d}",
            "theorem": "Zeta23.OPICARound3." + name, "module": "Zeta23.OPICARound3." + module,
            "source": "Zeta23/OPICARound3/" + module + ".lean",
            "consumer_module": "Zeta23.OPICARound3.Validation." + module,
            "consumer": "Zeta23/OPICARound3/Validation/" + module + ".lean",
            "consumer_declaration": "Zeta23.OPICARound3.Validation." + name + "_consumer", "required": True}
        need(type(row) is dict and all(row.get(k) == v and type(row.get(k)) is type(v)
             for k, v in expected.items()), "Actual-source root/consumer identity changed")


def check_premise_firewall(cid: str, premises: list[str], shortcuts: list[str]) -> dict[str, Any]:
    need(cid in PREMISES and type(premises) is list and type(shortcuts) is list,
         "Known premise contract required")
    need(len(set(premises)) == len(premises) and set(premises) == set(PREMISES[cid]),
         "Required premise lost or desired conclusion substituted")
    need(not shortcuts, "Unproved shortcut is not accepted")
    return {"status": "PASS_PREMISE_DECLARATIONS_ONLY", "authority": "NO_COMPILER_AUTHORITY", **CAPS}


def inspect_descendant(repo: Path = REPO) -> dict[str, Any]:
    repo = repo.resolve()
    before_head = git_text(repo, "rev-parse", "HEAD")
    base = base_inventory(repo)
    policy = path_policy(repo)
    pins = validate_descriptor(read_json(repo / DESCRIPTOR), policy)
    generated = set(policy["generated"])
    generated_bytes = []
    expected = set(base) | ADDITIONS
    observed = set()
    for current, dirs, files in os.walk(repo, followlinks=False):
        parent = Path(current)
        if parent == repo:
            dirs[:] = [d for d in dirs if d not in (".git", ".lake")]
        for name in dirs + files:
            path = parent / name
            need(not path.is_symlink() and not (hasattr(path, "is_junction") and path.is_junction()),
                 "Linked source provider outside declared compiler cache")
        for name in files:
            path = parent / name
            rel = path.relative_to(repo).as_posix()
            if rel == ".git":
                continue
            need(rel in expected, "Unapproved file, including ignored providers: " + rel)
            observed.add(rel)
            size = path.stat().st_size
            h = hashlib.sha1(b"blob " + str(size).encode("ascii") + b"\0")
            h256 = hashlib.sha256()
            length = 0
            with path.open("rb") as stream:
                for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                    h.update(chunk); h256.update(chunk); length += len(chunk)
            need(length == size == path.stat().st_size, "Source read race")
            if rel in pins:
                need(size == pins[rel]["bytes"] and h256.hexdigest() == pins[rel]["sha256"],
                     "Reviewed source pin differs: " + rel)
            elif rel in generated:
                generated_bytes.append({"path": rel, "bytes": size, "sha256": h256.hexdigest()})
            elif rel != DESCRIPTOR:
                need(rel in base and h.hexdigest() == base[rel][1], "Protected base source differs: " + rel)
    need(observed == expected, "Source inventory has missing paths")
    # Tree/index modes remain authenticated, independently of checked-out bytes.
    indexed = set()
    for entry in git(repo, "ls-files", "--stage", "-z").split(b"\0"):
        if not entry:
            continue
        header, name = entry.split(b"\t", 1)
        mode, _blob, stage = header.decode("ascii").split()
        rel = relative(name.decode("utf-8"))
        need(rel not in indexed, "Duplicate index entry")
        indexed.add(rel)
        need(stage == "0" and rel in expected, "Unmerged/unapproved indexed path")
        need(mode == (base[rel][0] if rel in base else "100644"), "Source mode changed")
    need(set(base) <= indexed, "A protected base path was removed from the index")
    public = read_json(repo / PREFIX / "PUBLIC_ROOTS.json")
    check_public(public)
    for path, key in (("research/RHRC/CLAIM_REGISTRY.json", "claims"),
                      ("research/RHRC/REGISTERED_THEOREM_BINDINGS.json", "bindings")):
        check_claim_extension(strict_json(git(repo, "show", BASE + ":" + path)), read_json(repo / path), key, public)
    for rel in sorted(ADDITIONS):
        if rel.endswith(".lean"):
            text = (repo / rel).read_text(encoding="utf-8")
            # Declaration scan is a source check, not the transitive kernel audit.
            text = re.sub(r"/\-.*?\-/", "", text, flags=re.S)
            text = re.sub(r"--[^\n]*", "", text)
            need(re.search(r"\b(?:sorry|admit)\b|^\s*(?:axiom|constant)\s", text, re.M) is None,
                 "Proof placeholder/project axiom in Round 3 source")
    need(git_text(repo, "rev-parse", "HEAD") == before_head, "HEAD changed during inspection")
    return {"schema": "OPICA3_DESCENDANT_SOURCE_INSPECTION_V1", "status": "PASS_SOURCE_SCOPE_ONLY",
            "checked_commit": before_head, "checked_tree": git_text(repo, "rev-parse", "HEAD^{tree}"),
            "base": BASE, "base_tree": BASE_TREE, "path_policy_sha256": policy_digest(policy),
            "descriptor_sha256": sha(repo / DESCRIPTOR), "source_files": len(observed),
            "pinned_extension_files": len(pins), "authority": "STATIC_SOURCE_AND_PREMISE_DECLARATIONS_ONLY",
            "generated_source_snapshot_sha256": hashlib.sha256(json.dumps(sorted(generated_bytes,
                key=lambda r: r["path"]), sort_keys=True, separators=(",", ":")).encode()).hexdigest(),
            "canonical_products_accepted": False,
            "current_tree_compiler_accepted": False, **CAPS}


def parse_axiom_audit(text: str, names: list[str]) -> dict[str, list[str]]:
    """Parse actual #print axioms output; duplicates and omissions fail closed."""
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    found = {}
    pattern = r"'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, text):
        name, raw = match.groups()
        if name not in names:
            continue
        need(name not in found, "Duplicate root/consumer axiom output")
        axioms = [a.strip() for a in (raw or "").split(",") if a.strip()]
        need(len(axioms) == len(set(axioms)) and set(axioms) <= allowed,
             "Unadmitted transitive/project axiom: " + name)
        found[name] = axioms
    need(set(found) == set(names), "Missing exact root/consumer axiom export")
    for name in names:
        need(re.search(r"(?m)^" + re.escape(name) + r"(?:\s|\.{)", text) is not None,
             "Missing exact #check type output: " + name)
    return found


def semantic_control_pair(index: int) -> tuple[str, str, str]:
    """Literal independent expected types and one semantic strengthening each.

    Rejection means the checked producer does not supply the stronger type;
    it does not establish that the stronger source theorem is mathematically
    false. The exact synthetic countermodels have a separate test scope.
    """
    need(type(index) is int and 0 <= index < 4, "Unknown native control")
    header = ("import Zeta23.OPICARound3.Validation." + MODULES[index] + "\n"
              "noncomputable section\nopen Zeta23.OPICARound3 Zeta23.OPICARound3.Validation\n"
              "open Zeta23.CCM\n")
    zero = "(ρ : Zeta23.zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2)"
    consumer = "Zeta23.OPICARound3.Validation." + ROOT_NAMES[index] + "_consumer"
    if index == 0:
        target = ("∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ < L → ∃ K : ℕ, 3 ≤ K ∧\n"
                  "  (EvenNeutralNegative L K ∨ OddNeutralNegative L K)")
        positive = header + "example " + zero + " : " + target + " := by\n  exact " + consumer + " ρ hoff\n"
        negative = positive.replace("EvenNeutralNegative L K ∨ OddNeutralNegative L K",
                                    "EvenNeutralNegative L K ∧ OddNeutralNegative L K")
        description = "D01_EVENTUAL_EITHER_PARITY_COVER_DOES_NOT_SUPPLY_EVENTUAL_BOTH"
    elif index == 1:
        target = "∃ L : ℝ, R < L ∧ 0 < L ∧ ∃ K : ℕ, 3 ≤ K ∧ BothNeutralNegative L K"
        positive = header + "example " + zero + " (R : ℝ) : " + target + " := by\n  exact " + consumer + " ρ hoff R\n"
        negative = positive.replace(consumer + " ρ hoff R",
            "Zeta23.OPICARound3.neutral_parity_cofinal_of_off_line_zero ρ hoff .even R")
        description = "D02_SINGLE_PARITY_COFINALITY_DOES_NOT_SUPPLY_COMMON_BOTH_PARITIES"
    elif index == 2:
        local = ("∀ R : ℝ, ∃ a b : ℝ, ∃ K : ℕ, ∃ η : ℝ, R < a ∧ 0 < a ∧ a < b ∧\n"
                 "  3 ≤ K ∧ 0 < η ∧ Nonempty (UniformNeutralNegativeFrame a b K η)")
        global_eta = ("∃ η : ℝ, 0 < η ∧ ∀ R : ℝ, ∃ a b : ℝ, ∃ K : ℕ, R < a ∧ 0 < a ∧ a < b ∧\n"
                      "  3 ≤ K ∧ Nonempty (UniformNeutralNegativeFrame a b K η)")
        positive = header + "example " + zero + " : " + local + " := by\n  exact " + consumer + " ρ hoff\n"
        negative = positive.replace(local, global_eta)
        description = "D03_LOCAL_INTERVAL_MARGIN_DOES_NOT_SUPPLY_ONE_GLOBAL_ETA"
    else:
        binders = "{L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 3 ≤ K) (hboth : BothNeutralNegative L K)"
        target = """∃ Ke Ko : ℕ, 3 ≤ Ke ∧ 3 ≤ Ko ∧
      EvenNeutralNegative L Ke ∧ OddNeutralNegative L Ko ∧
      (∀ M, 3 ≤ M → EvenNeutralNegative L M → Ke ≤ M) ∧
      (∀ M, 3 ≤ M → OddNeutralNegative L M → Ko ≤ M) ∧
      BothNeutralNegative L (max Ke Ko) ∧
      (∀ M, 3 ≤ M → BothNeutralNegative L M → max Ke Ko ≤ M) ∧
      PoleNeutralParityPSD .even L (Ke - 1) ∧
      PoleNeutralParityPSD .odd L (Ko - 1) ∧
      NeutralNewbornSchur .even L Ke ∧ NeutralNewbornSchur .odd L Ko ∧
      (Ke < Ko → EvenNeutralNegative L (Ko - 1)) ∧
      (Ko < Ke → OddNeutralNegative L (Ke - 1))"""
        positive = header + "example " + binders + " : " + target + " := by\n  exact " + consumer + " hL hK hboth\n"
        negative = positive.replace("PoleNeutralParityPSD .even L (Ke - 1)",
                                    "PoleNeutralParityPSD .even L (max Ke Ko - 1)")
        negative = negative.replace("PoleNeutralParityPSD .odd L (Ko - 1)",
                                    "PoleNeutralParityPSD .odd L (max Ke Ko - 1)")
        description = "D04_NEWBORN_PREDECESSORS_DO_NOT_SUPPLY_BOTH_PSD_AT_LATER_PREDECESSOR"
    need(positive != negative, "Semantic mutation did not change the expected type/producer")
    return positive, negative, description


def require_semantic_rejection(text: str) -> None:
    text = text.lower()
    forbidden = ("unknown identifier", "unknown constant", "unknown namespace", "unknown module", "object file",
                 "unexpected token", "invalid syntax", "file not found", "no such file", "unknown option",
                 "maximum recursion", "maximum number of heartbeats", "out of memory", "failed to synthesize")
    need(not any(word in text for word in forbidden), "Negative fixture failed for infrastructure/syntax/name reasons")
    need(any(word in text for word in ("type mismatch", "unsolved goals", "application type mismatch")),
         "Negative fixture lacks a semantic/type mismatch diagnostic")


def require_compiler_exit(code: int, positive: bool) -> None:
    need(type(code) is int and code == (0 if positive else 1),
         "Compiler must succeed or reject normally; crashes are not semantic rejection")


def formal_checks(repo: Path, output: Path, timeout: int) -> dict[str, Any]:
    """CI-only native commands. No invocation is made by a source preflight."""
    repo, output = repo.resolve(), output.resolve()
    need(not output.is_relative_to(repo) and not output.exists(), "Fresh external compiler evidence required")
    source = inspect_descendant(repo)
    need(not git_text(repo, "status", "--porcelain", "--untracked-files=all"), "Compiler gate needs clean source")
    expected_head = os.environ.get("REQUESTED_HEAD", source["checked_commit"])
    need(source["checked_commit"] == expected_head, "Compiler gate checked another requested head")
    public = read_json(repo / PREFIX / "PUBLIC_ROOTS.json")
    old = read_json(repo / R2 / "PUBLIC_ROOTS.json")
    old_rows = [r for r in old["roots"] if r.get("required_for_full_core") is True]
    need(len(old_rows) == 40, "Original forty required roots changed")
    names = [r["proposed_public_name"] for r in old_rows]
    names += [r[key] for r in public["roots"] for key in ("theorem", "consumer_declaration")]
    need(len(names) == len(set(names)) == 48, "Exact current forty-plus-eight audit required")
    output.mkdir(parents=True)
    commands = []
    def run(argv, label, success=True):
        log = output / (label + ".log")
        with log.open("xb") as stream:
            try:
                result = subprocess.run(argv, cwd=repo, stdout=stream, stderr=subprocess.STDOUT,
                                        timeout=timeout, check=False)
                code = result.returncode
            except subprocess.TimeoutExpired:
                commands.append({"argv": argv, "exit_code": None, "timeout": True, "log": log.name,
                                 "log_sha256": sha(log)})
                raise
        commands.append({"argv": argv, "exit_code": code, "timeout": False,
                         "log": log.name, "log_sha256": sha(log)})
        require_compiler_exit(code, success)
        return log.read_text(encoding="utf-8")
    report = {"schema": "OPICA3_CURRENT_COMPILER_GATE_V1", "status": "FAILED_OR_INCOMPLETE",
              "checked_commit": source["checked_commit"], "checked_tree": source["checked_tree"],
              "scope": "CURRENT_FOUR_ROOTS_AND_CONSUMERS_PLUS_CURRENT_ORIGINAL_FORTY",
              "build_mode": "FRESH_CI_PROJECT_BUILD_PACKAGE_CACHE_ALLOWED", "commands": commands,
              "current_tree_compiler_accepted": False, **CAPS}
    try:
        # Mathlib/package objects are explicitly allowed. The project itself
        # must have no Zeta23 objects, even when Lake created an empty build dir.
        project_objects = [p for p in (repo / ".lake/build").rglob("*")
                           if p.is_file() and any(part == "Zeta23" or part.startswith("Zeta23.")
                                                 for part in p.relative_to(repo / ".lake/build").parts)]
        need(not project_objects, "Fresh current CI project module objects required")
        old_path = list(sys.path)
        try:
            sys.path.insert(0, str(repo))
            from research.RHRC.integration.opica_round2 import build_receipt as compiler
        finally:
            sys.path[:] = old_path
        report["environment"] = compiler.validate_environment(repo)
        report["pinned_packages"] = compiler.validate_packages(repo)
        report["source_manifest_sha256"] = hashlib.sha256(json.dumps(compiler.source_manifest(repo),
            sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        version = run(["lake", "env", "lean", "--version"], "lean-version").strip()
        need(version.startswith("Lean (version 4.33.0-rc2,"), "Actual Lean version differs from pinned toolchain")
        report["lean_version"] = version
        run(["lake", "build", "Zeta23.OPICARound2.All", "Zeta23.OPICARound2.Validation",
             "Zeta23.RHRC.OpicaRound2Bindings", "Zeta23.OPICARound3.All",
             "Zeta23.OPICARound3.Validation", "Zeta23.RHRC.OpicaRound3Bindings"], "current-build")
        query = output / "CurrentRootAudit.lean"
        query.write_text("import Zeta23.OPICARound2.All\nimport Zeta23.OPICARound3.Validation\n"
                         "set_option pp.universes true\nset_option pp.fullNames true\n"
                         + "\n".join("#check " + n + "\nset_option pp.universes false in\n#print axioms " + n
                                     for n in names) + "\n",
                         encoding="utf-8", newline="\n")
        text = run(["lake", "env", "lean", "-R", str(output), "-o",
                    str(output / "CurrentRootAudit.olean"), str(query)], "current-root-audit")
        need((output / "CurrentRootAudit.olean").is_file(), "Missing genuine compiler object")
        report["axioms"] = parse_axiom_audit(text, names)
        report["query_sha256"] = sha(query)
        report["object_sha256"] = sha(output / "CurrentRootAudit.olean")
        report["semantic_controls"] = []
        for index in range(4):
            positive, negative, description = semantic_control_pair(index)
            pair = {"id": f"R3-D{index+1:02d}", "scope": description,
                    "negative_authority": "PRODUCER_TYPE_REJECTION_ONLY_NOT_SOURCE_FALSE_THEOREM"}
            for mode, content in (("positive", positive), ("negative", negative)):
                label = f"D{index+1:02d}-{mode}"
                path = output / ("Control" + str(index+1) + mode + ".lean")
                obj = path.with_suffix(".olean")
                path.write_text(content, encoding="utf-8", newline="\n")
                log = run(["lake", "env", "lean", "-R", str(output), "-o", str(obj), str(path)],
                          label, success=(mode == "positive"))
                if mode == "positive":
                    need(obj.is_file(), "Positive typed control lacks its actual object")
                else:
                    need(not obj.exists(), "Negative control unexpectedly emitted a compiler object")
                    require_semantic_rejection(log)
                pair[mode] = {"source": path.name, "sha256": sha(path), "command_index": len(commands)-1,
                              "object_sha256": sha(obj) if obj.exists() else None}
            report["semantic_controls"].append(pair)
        after = inspect_descendant(repo)
        need(compiler.validate_environment(repo) == report["environment"]
             and compiler.validate_packages(repo) == report["pinned_packages"], "Pinned compiler package sources changed")
        need(after == source and not git_text(repo, "status", "--porcelain", "--untracked-files=all"),
             "Source changed during current compiler gate")
        report.update(status="PASS_CURRENT_COMPILER_SCOPE_ONLY", current_tree_compiler_accepted=True)
        return report
    finally:
        (output / "result.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=REPO)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--formal-output", type=Path,
                        help="Explicit CI native compiler gate; never implied by preflight")
    parser.add_argument("--timeout", type=int, default=20000)
    args = parser.parse_args()
    try:
        need(1 <= args.timeout <= 22000, "Bounded compiler timeout required")
        report = (formal_checks(args.repo, args.formal_output, args.timeout) if args.formal_output
                  else inspect_descendant(args.repo))
    except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as exc:
        report = {"schema": "OPICA3_DESCENDANT_SOURCE_INSPECTION_V1", "status": "FAIL_SOURCE_SCOPE",
                  "errors": [str(exc)], "authority": "NO_ACCEPTANCE", **CAPS}
    if args.output:
        need(not args.output.resolve().is_relative_to(args.repo.resolve()), "Evidence must be external")
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 0 if report["status"].startswith("PASS_") else 1


if __name__ == "__main__":
    raise SystemExit(main())
