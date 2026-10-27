"""Round 3's closed source extension and scoped, independent proof checks.

Source inspection and exact synthetic falsifiers grant no theorem authority.
Only actual Lean commands establish the named declarations on the checked head.
Neither path grants full-release acceptance or an independent closing inequality.
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
from pathlib import Path, PurePosixPath, PureWindowsPath
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
    "first_simultaneous_newborn_source_witnesses",
)
MODULES = ("NeutralParityCover", "CofinalSimultaneousNegative", "UniformNeutralInterval",
           "FirstSimultaneousNegative", "NewbornSource")
MATH_MODULES = ("NeutralParityCover", "NeutralParityTopology", "CofinalSimultaneousNegative",
                "UniformNeutralInterval", "FirstNeutralCutoff", "KernelSafeSchur",
                "FirstSimultaneousNegative", "SchurNegativeWitness", "NewbornSource")
ADDITIONS = frozenset(
    ["Zeta23/OPICARound3/" + n + ".lean" for n in MATH_MODULES]
    + ["Zeta23/OPICARound3/Validation/" + n + ".lean" for n in MODULES]
    + ["Zeta23/OPICARound3.lean", "Zeta23/OPICARound3/All.lean",
       "Zeta23/OPICARound3/Validation.lean", "Zeta23/RHRC/OpicaRound3Bindings.lean",
       "Zeta23/RHRC/OpicaRound3AtlasExport.lean",
       ".github/workflows/rhrc_opica_round3.yml"]
    + [PREFIX + n for n in ("README.md", "PUBLIC_ROOTS.json", "SOURCE_REGISTER.json",
       "OPEN_RESEARCH.json", "POST_GREEN_RESEARCH.md", "DESCENDANT_EXTENSION.json",
       "validate_contract.py", "tests/test_contract.py", "BUILD_PLAN.md",
       "constraint_atlas.py", "schemas/constraint_atlas.schema.json",
       "atlas/SEMANTIC_OVERLAY.json", "atlas/CONSTRAINT_ATLAS.jsonl",
       "tests/test_constraint_atlas.py", "source_backend.py", "source_evaluator.py",
       "source_checker.py", "fixtures/source_evaluator_cases.json",
       "schemas/source_evaluator.schema.json", "tests/test_source_evaluator.py")]
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
    "R3-D05": ["actual_first_parity_cutoffs", "same_aperture_cutoff_and_witness",
                "constructed_negative_schur_witness", "regular_and_resonant_branches",
                "both_selected_parities", "complete_corrected_source_identity",
                "retained_shifted_operator_output", "distinct_parity_and_cutoff_maps"],
}
FORBIDDEN = frozenset(("cofinality_only", "unprojected_output_residual", "both_predecessors_psd",
                       "equal_cutoffs_imply_spectral_tie", "globally_uniform_eta",
                       "desired_frame_assumed", "imported_false_source_sign",
                       "source_alone_kernel_compatibility", "parity_map_is_cutoff_embedding",
                       "numerical_near_zero_is_exact_kernel"))


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
    need(set(after) - set(before) == set(expected), "Exactly five new Round 3 registry rows required")
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
    need(type(doc.get("roots")) is list and len(doc["roots"]) == 5, "Exactly five required roots")
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
    need(type(index) is int and 0 <= index < 5, "Unknown native control")
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
    elif index == 3:
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
    else:
        target = """∃ Ke Ko : ℕ, 3 ≤ Ke ∧ 3 ≤ Ko ∧
      EvenNeutralNegative L Ke ∧ OddNeutralNegative L Ko ∧
      (∀ M, 3 ≤ M → EvenNeutralNegative L M → Ke ≤ M) ∧
      (∀ M, 3 ≤ M → OddNeutralNegative L M → Ko ≤ M) ∧
      BothNeutralNegative L (max Ke Ko) ∧
      (∀ M, 3 ≤ M → BothNeutralNegative L M → max Ke Ko ≤ M) ∧
      Nonempty (NativeNewbornSourceWitness .even L Ke hL) ∧
      Nonempty (NativeNewbornSourceWitness .odd L Ko hL) ∧
      (Ko ≤ Ke → Nonempty (NativeNewbornSourceWitness .even L (max Ke Ko) hL)) ∧
      (Ke ≤ Ko → Nonempty (NativeNewbornSourceWitness .odd L (max Ke Ko) hL))"""
        positive = (header + "example {L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 3 ≤ K) "
                    "(hboth : BothNeutralNegative L K) : " + target
                    + " := by\n  exact " + consumer + " hL hK hboth\n"
                    + """example {L : ℝ} (hL : 0 < L) (p : ReversalParity) (K : ℕ)
    (W : NativeNewbornSourceWitness p L K hL) (lam : ℝ) :
    (nativePoleNeutralParityShifted (sourceOppositeParity p) L K lam).ker.starProjection
      (nativeParitySourceOutput p hL K W.w lam) = 0 := by
  exact newborn_source_full_output_projection_consumer hL p K W lam
""")
        negative = positive.replace("nativeParitySourceOutput p hL K W.w lam",
                                    "nativeParitySourceDefect p hL K W.w")
        description = "D05_WHOLE_OUTPUT_KERNEL_COMPATIBILITY_DOES_NOT_SUPPLY_SOURCE_ALONE"
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


PHASE1_JOBS = frozenset({"contract", "runtime-regressions", "current-formal", "source-evaluator"})
ARTIFACT_JOBS = ("contract", "runtime", "formal", "evaluator")
CONTRACT_TEST_FILES = ("test_contract.py", "test_constraint_atlas.py")
EVALUATOR_TEST_FILES = ("test_source_evaluator.py",)
NATIVE_CASE = "test_claim_firewall.NativeTypedSemanticControls.test_seven_positive_and_wrong_type_native_fixtures"


def current_audit_names(repo: Path) -> list[str]:
    public = read_json(repo / PREFIX / "PUBLIC_ROOTS.json")
    check_public(public)
    old = read_json(repo / R2 / "PUBLIC_ROOTS.json")
    rows = [r for r in old["roots"] if r.get("required_for_full_core") is True]
    need(len(rows) == 40, "Original forty required roots changed")
    names = [r["proposed_public_name"] for r in rows]
    names += [r[key] for r in public["roots"] for key in ("theorem", "consumer_declaration")]
    need(len(names) == len(set(names)) == 50, "Exact current forty-plus-ten audit required")
    return names


def render_current_audit(names: list[str]) -> bytes:
    return ("import Zeta23.OPICARound2.All\nimport Zeta23.OPICARound3.Validation\n"
            "set_option pp.universes true\nset_option pp.fullNames true\n"
            + "\n".join("#check " + n + "\nset_option pp.universes false in\n#print axioms " + n
                        for n in names) + "\n").encode("utf-8")


def require_phase1_needs(data: Any) -> None:
    need(type(data) is dict and set(data) == PHASE1_JOBS, "Exact four current build jobs required")
    for row in data.values():
        need(type(row) is dict and set(row) <= {"result", "outputs"}
             and row.get("result") == "success" and type(row.get("outputs", {})) is dict,
             "Missing, skipped, failed, cancelled or incomplete current Phase 1 job")


def evidence_file(root: Path, name: str) -> Path:
    relative(name)
    path = root
    for part in PurePosixPath(name).parts:
        path = path / part
        need(not path.is_symlink() and not (hasattr(path, "is_junction") and path.is_junction()),
             "Linked evidence path")
    need(path.is_file() and path.resolve().is_relative_to(root.resolve())
         and path.stat().st_size <= 64 * 1024 * 1024, "Missing, escaping or oversized evidence file: " + name)
    return path


def artifact_inventory(root: Path) -> list[dict[str, Any]]:
    need(root.is_dir() and not root.is_symlink()
         and root.absolute() == root.resolve()
         and not (hasattr(root, "is_junction") and root.is_junction()), "Plain artifact directory required")
    rows, total = [], 0
    for current, dirs, files in os.walk(root, followlinks=False):
        for name in dirs + files:
            path = Path(current) / name
            need(not path.is_symlink() and not (hasattr(path, "is_junction") and path.is_junction()),
                 "Linked artifact provider")
        for name in files:
            path = evidence_file(root, (Path(current) / name).relative_to(root).as_posix())
            size = path.stat().st_size
            total += size
            rows.append({"path": path.relative_to(root).as_posix(), "bytes": size, "sha256": sha(path)})
            need(len(rows) <= 512 and total <= 512 * 1024 * 1024, "Artifact census exceeds finite budget")
    need(bool(rows), "Empty aggregate artifacts")
    return sorted(rows, key=lambda r: r["path"])


def require_open_caps(data: dict[str, Any]) -> None:
    need(type(data) is dict and data.get("full_core_accepted") is False and data.get("full_release_accepted") is False
         and data.get("RH") == data.get("Step4") == "OPEN"
         and data.get("human_review", "NOT_ESTABLISHED") == "NOT_ESTABLISHED",
         "Phase 1 evidence cannot promote full release, human review, RH or Step4")


def same_json(actual: Any, expected: Any) -> bool:
    """Type-sensitive equality: Boolean/float substitutions are not integer identities."""
    return json.dumps(actual, sort_keys=True, separators=(",", ":"), allow_nan=False) == json.dumps(
        expected, sort_keys=True, separators=(",", ":"), allow_nan=False)


def require_clean_source(repo: Path) -> None:
    need(not git_text(repo, "status", "--porcelain", "--untracked-files=all"),
         "Current Phase 1 aggregate requires a clean committed checkout and index")


def test_descriptions(folder: Path, pattern: str = "test_*.py") -> dict[str, str | None]:
    """Read literal TestCase methods without importing or executing the tests."""
    names = {}
    for path in sorted(folder.glob(pattern)):
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in tree.body:
            if isinstance(node, ast.ClassDef) and any(isinstance(b, ast.Attribute) and b.attr == "TestCase"
                                                     for b in node.bases):
                for method in node.body:
                    if isinstance(method, ast.FunctionDef) and method.name.startswith("test_"):
                        name = path.stem + "." + node.name + "." + method.name
                        need(name not in names, "Ambiguous literal unit-test population")
                        doc = ast.get_docstring(method)
                        names[name] = doc.split("\n")[0].strip() if doc else None
    need(bool(names), "Missing literal unit-test population")
    return names


def test_inventory(folder: Path) -> list[str]:
    return sorted(test_descriptions(folder))


def selected_test_descriptions(folder: Path, filenames: tuple[str, ...]) -> dict[str, str | None]:
    """Closed lane partition: every test file has one owner and actually exists."""
    all_files = CONTRACT_TEST_FILES + EVALUATOR_TEST_FILES
    need(len(all_files) == len(set(all_files))
         and {p.name for p in folder.glob("test_*.py")} == set(all_files),
         "Round 3 unit files differ from the exact required lane partition")
    need(bool(filenames) and set(filenames) <= set(all_files), "Unknown unit-test lane")
    descriptions = {}
    for filename in filenames:
        for name, description in test_descriptions(folder, filename).items():
            need(name not in descriptions, "Repeated test across lane files")
            descriptions[name] = description
    return descriptions


def run_unit_lane(repo: Path, lane: str, mode: str, output: Path) -> int:
    """Execute only this lane's exact literal tests and record observed mode."""
    import unittest
    need(lane in ("contract", "evaluator") and mode in ("normal", "optimized"), "Unknown unit lane/mode")
    need(bool(sys.flags.optimize) is (mode == "optimized"), "Actual Python mode differs from requested unit mode")
    need(not output.exists() and not output.resolve().is_relative_to(repo.resolve()), "Fresh external unit receipt required")
    files = CONTRACT_TEST_FILES if lane == "contract" else EVALUATOR_TEST_FILES
    descriptions = selected_test_descriptions(repo / PREFIX / "tests", files)
    def flatten(suite):
        for item in suite:
            if isinstance(item, unittest.TestSuite):
                yield from flatten(item)
            else:
                yield item
    loader = unittest.TestLoader()
    cases = [case for filename in files for case in flatten(loader.discover(str(repo / PREFIX / "tests"), pattern=filename))]
    need(sorted(case.id() for case in cases) == sorted(descriptions), "Loaded unit population differs from current literal source")
    before = {"checked_commit": git_text(repo, "rev-parse", "HEAD"), "checked_tree": git_text(repo, "rev-parse", "HEAD^{tree}")}
    result = unittest.TextTestRunner(verbosity=2).run(unittest.TestSuite(cases))
    need(all(git_text(repo, "rev-parse", "HEAD" if key == "checked_commit" else "HEAD^{tree}") == value
             for key, value in before.items()), "Source ref changed during unit lane")
    report = {"schema": "OPICA3_CURRENT_UNIT_LANE_V1", "lane": lane, "mode": mode,
              "python_optimized": bool(sys.flags.optimize), **before, "test_ids": sorted(descriptions),
              "run": result.testsRun, "errors": len(result.errors), "failures": len(result.failures),
              "skipped": len(result.skipped), "successful": result.wasSuccessful(),
              "scope": "EXACT_CURRENT_LITERAL_TEST_PARTITION", **CAPS}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return 0 if result.wasSuccessful() and not result.skipped and result.testsRun == len(descriptions) else 1


def verify_unit_lane(root: Path, repo: Path, lane: str, source: dict[str, Any]) -> int:
    files = CONTRACT_TEST_FILES if lane == "contract" else EVALUATOR_TEST_FILES
    descriptions = selected_test_descriptions(repo / PREFIX / "tests", files)
    ids = sorted(descriptions)
    for mode in ("normal", "optimized"):
        report = read_json(evidence_file(root, lane + "-tests-" + mode + ".json"))
        expected = {"schema": "OPICA3_CURRENT_UNIT_LANE_V1", "lane": lane, "mode": mode,
                    "python_optimized": mode == "optimized", "checked_commit": source["checked_commit"],
                    "checked_tree": source["checked_tree"], "test_ids": ids, "run": len(ids),
                    "errors": 0, "failures": 0, "skipped": 0, "successful": True,
                    "scope": "EXACT_CURRENT_LITERAL_TEST_PARTITION", **CAPS}
        need(same_json(report, expected), "Unit lane changed source, observed mode, population or disposition: " + lane)
        verify_unit_log(evidence_file(root, lane + "-tests-" + mode + ".log").read_text(encoding="utf-8"), ids, descriptions)
    return len(ids)


def verify_unit_log(text: str, expected: list[str], descriptions: dict[str, str | None] | None = None) -> None:
    rows = []
    lines = text.splitlines()
    for index, line in enumerate(lines):
        match = re.fullmatch(r"(test_\w+) \(([\w.]+)\)( \.\.\. ok)?", line)
        if match:
            method, owner, suffix = match.groups()
            name = owner if owner.endswith("." + method) else owner + "." + method
            if not suffix:
                description = (descriptions or {}).get(name)
                need(description is not None and index + 1 < len(lines)
                     and lines[index + 1] == description + " ... ok", "Raw unit docstring/outcome differs from current source")
            rows.append(name)
    need(len(rows) == len(expected) and sorted(rows) == sorted(expected),
         "Raw unit log has missing, duplicate, skipped or changed tests")
    summaries = re.findall(r"(?m)^Ran (\d+) tests? in [0-9.]+s\s*$", text)
    need(summaries == [str(len(expected))] and re.search(r"\nOK\s*\Z", text) is not None
         and not re.search(r"(?im)^(?:FAILED|ERROR:|FAIL:)|\.\.\. (?:skipped|expected failure|unexpected success)", text),
         "Raw unit log did not complete the exact population successfully")


def verify_current_formal(root: Path, report: Any, names: list[str], source: dict[str, Any],
                          manifest_sha: str, environment: dict, packages: list[dict]) -> dict[str, Any]:
    fields = {"schema", "status", "checked_commit", "checked_tree", "scope", "build_mode", "commands",
              "current_tree_compiler_accepted", "environment", "pinned_packages", "source_manifest_sha256",
              "lean_version", "axioms", "query_sha256", "object_sha256", "semantic_controls", *CAPS}
    need(type(report) is dict and set(report) == fields, "Exact current compiler evidence fields required")
    require_open_caps(report)
    need(report["schema"] == "OPICA3_CURRENT_COMPILER_GATE_V1"
         and report["status"] == "PASS_CURRENT_COMPILER_SCOPE_ONLY"
         and report["current_tree_compiler_accepted"] is True
         and report["scope"] == "CURRENT_FIVE_ROOTS_AND_CONSUMERS_PLUS_CURRENT_ORIGINAL_FORTY"
         and report["build_mode"] == "FRESH_CI_PROJECT_BUILD_PACKAGE_CACHE_ALLOWED"
         and all(report[k] == source[k] for k in ("checked_commit", "checked_tree"))
         and report["source_manifest_sha256"] == manifest_sha
         and report["environment"] == environment and report["pinned_packages"] == packages,
         "Compiler source, pins, requested population or cold-project scope differs")
    commands = report["commands"]
    need(type(commands) is list and len(commands) == 13, "Exact thirteen native compiler commands required")
    audit = evidence_file(root, "CurrentRootAudit.lean")
    need(audit.read_bytes() == render_current_audit(names) and report["query_sha256"] == sha(audit)
         and report["object_sha256"] == sha(evidence_file(root, "CurrentRootAudit.olean")),
         "Current audit source or actual object changed")
    argv = commands[2].get("argv") if type(commands[2]) is dict else None
    need(type(argv) is list and len(argv) == 8 and all(type(v) is str for v in argv), "Exact audit argv required")
    value = argv[4]
    producer = PureWindowsPath(value) if re.match(r"^[A-Za-z]:[\\/]", value) else PurePosixPath(value)
    need(producer.is_absolute() and ".." not in producer.parts, "Absolute canonical producer root required")
    expected = [(["lake", "env", "lean", "--version"], "lean-version", True),
                (["lake", "build", "Zeta23.OPICARound2.All", "Zeta23.OPICARound2.Validation",
                  "Zeta23.RHRC.OpicaRound2Bindings", "Zeta23.OPICARound3.All",
                  "Zeta23.OPICARound3.Validation", "Zeta23.RHRC.OpicaRound3Bindings"], "current-build", True),
                (["lake", "env", "lean", "-R", str(producer), "-o",
                  str(producer / "CurrentRootAudit.olean"), str(producer / "CurrentRootAudit.lean")],
                 "current-root-audit", True)]
    pairs = report["semantic_controls"]
    need(type(pairs) is list and len(pairs) == 5, "All five current semantic pairs required")
    for index, pair in enumerate(pairs):
        positive, negative, description = semantic_control_pair(index)
        need(type(pair) is dict and set(pair) == {"id", "scope", "negative_authority", "positive", "negative"}
             and pair["id"] == f"R3-D{index+1:02d}" and pair["scope"] == description
             and pair["negative_authority"] == "PRODUCER_TYPE_REJECTION_ONLY_NOT_SOURCE_FALSE_THEOREM",
             "Semantic pair identity/scope changed")
        for mode, content in (("positive", positive), ("negative", negative)):
            name = "Control" + str(index+1) + mode
            path = evidence_file(root, name + ".lean")
            row = pair[mode]
            need(type(row) is dict and set(row) == {"source", "sha256", "command_index", "object_sha256"}
                 and row["source"] == path.name and path.read_bytes() == content.encode("utf-8")
                 and row["sha256"] == sha(path) and type(row["command_index"]) is int
                 and row["command_index"] == len(expected), "Semantic fixture source or command binding changed")
            obj = root / (name + ".olean")
            if mode == "positive":
                need(row["object_sha256"] == sha(evidence_file(root, obj.name)), "Positive semantic object changed")
            else:
                need(row["object_sha256"] is None and not obj.exists(), "Rejected semantic fixture emitted an object")
            expected.append((["lake", "env", "lean", "-R", str(producer), "-o",
                              str(producer / obj.name), str(producer / path.name)], f"D{index+1:02d}-{mode}", mode == "positive"))
    logs = {}
    for row, (recipe, label, success) in zip(commands, expected):
        need(type(row) is dict and set(row) == {"argv", "exit_code", "timeout", "log", "log_sha256"}
             and row["argv"] == recipe and row["timeout"] is False and row["log"] == label + ".log",
             "Current native command, timeout or log binding differs")
        require_compiler_exit(row["exit_code"], success)
        log = evidence_file(root, row["log"])
        need(row["log_sha256"] == sha(log), "Current raw compiler log hash differs")
        text = log.read_text(encoding="utf-8")
        need(not success or re.search(r"(?m)^.*\berror:", text) is None, "Successful command has a compiler error")
        if not success:
            need("error:" in text.lower(), "Negative fixture lacks an actual compiler error")
            require_semantic_rejection(text)
        logs[label] = text
    need(type(report["lean_version"]) is str and logs["lean-version"].strip() == report["lean_version"]
         and report["lean_version"].startswith("Lean (version 4.33.0-rc2,")
         and "d8b18978322de05a8f3dba51ef03cf5461676c17" in report["lean_version"], "Actual pinned Lean version differs")
    axioms = parse_axiom_audit(logs["current-root-audit"], names)
    need(axioms == report["axioms"], "Serialized axiom summary differs from raw50-name output")
    return {"status": "PASS_REPARSED_CURRENT_COMPILER_ARTIFACTS", "roots_and_consumers": len(names),
            "semantic_pairs": len(pairs), "axioms": axioms, "receipt_sha256": sha(evidence_file(root, "result.json"))}


def aggregate_phase1(repo: Path, artifacts: Path, needs_path: Path, *,
                     recompute_output: Path | None = None) -> dict[str, Any]:
    """Independently reparse same-run current artifacts; never run Lean or accept full release."""
    repo = repo.resolve()
    need(not artifacts.is_symlink() and not artifacts.resolve().is_relative_to(repo), "External plain downloaded artifacts required")
    before_artifacts = artifact_inventory(artifacts)
    need({p.name for p in artifacts.iterdir()} == set(ARTIFACT_JOBS), "Exact four separately downloaded job roots required")
    need(needs_path.is_file() and needs_path.absolute() == needs_path.resolve()
         and not needs_path.resolve().is_relative_to(repo), "External plain required-jobs input required")
    required_needs = read_json(needs_path)
    require_phase1_needs(required_needs)
    require_clean_source(repo)
    source = inspect_descendant(repo)
    need(source["checked_commit"] == os.environ.get("REQUESTED_HEAD", source["checked_commit"]), "Aggregate checked another requested head")
    old_path = list(sys.path)
    try:
        sys.path.insert(0, str(repo))
        from research.RHRC.integration.opica_round2 import build_receipt as compiler, controls
    finally:
        sys.path[:] = old_path
    manifest = compiler.source_manifest(repo)
    environment, packages = compiler.validate_environment(repo), compiler.validate_packages(repo)
    frozen = {"schema": "OPICA2_WORKFLOW_SOURCE_FREEZE_V1", "checked_commit": source["checked_commit"],
              "checked_tree": source["checked_tree"], "sources": manifest, "authority": "SOURCE_IDENTITY_ONLY",
              "full_core_accepted": False, "full_release_accepted": False, "RH": "OPEN", "Step4": "OPEN"}
    for job in ARTIFACT_JOBS:
        need(same_json(read_json(evidence_file(artifacts, job + "/source/before.json")), frozen),
             "Job source freeze is missing, stale or belongs to another checkout: " + job)
    for name, optimized in (("preflight.json", False), ("preflight-optimized.json", True)):
        need(same_json(read_json(evidence_file(artifacts, "contract/" + name)), {**source, "python_optimized": optimized}),
             "Current preflight source or actual Python mode differs from independent inspection")
    guard_count = verify_unit_lane(artifacts / "contract", repo, "contract", source)
    evaluator_count = verify_unit_lane(artifacts / "evaluator", repo, "evaluator", source)
    ids = test_inventory(repo / R2 / "tests")
    descriptions = test_descriptions(repo / R2 / "tests")
    need(len(ids) == 212 and ids.count(NATIVE_CASE) == 1, "Exact current212-test inventory required")
    ordinary = [name for name in ids if name != NATIVE_CASE]
    for mode in ("normal", "optimized"):
        data = read_json(evidence_file(artifacts, "runtime/runtime-" + mode + ".json"))
        fields = {"schema", "mode", "python_optimized", "checked_commit", "checked_tree", "discovered", "selected",
                  "selected_test_ids", "held_native_case", "run", "errors", "failures", "skipped", "successful", "scope",
                  "full_core_accepted", "full_release_accepted", "RH", "Step4"}
        need(type(data) is dict and set(data) == fields, "Exact current runtime report fields required")
        require_open_caps(data)
        need(data.get("schema") == "OPICA3_CURRENT_ROUND2_RUNTIME_REGRESSION_V1" and data.get("mode") == mode
             and data["python_optimized"] is (mode == "optimized")
             and all(data.get(k) == source[k] for k in ("checked_commit", "checked_tree"))
             and all(type(data.get(k)) is int and data[k] == v for k, v in
                     {"discovered": 212, "selected": 211, "run": 211, "errors": 0, "failures": 0, "skipped": 0}.items())
             and data.get("successful") is True and type(data["selected_test_ids"]) is list
             and all(type(name) is str for name in data["selected_test_ids"])
             and sorted(data["selected_test_ids"]) == ordinary
             and data["scope"] == "ALL_CURRENT211_NON_LEAN_TESTS_INCLUDING_ACTUAL_ARB_256_512_PRODUCER_GRAM_SCHEMA_AND_ADVERSARIES"
             and data.get("held_native_case") == {"id": NATIVE_CASE, "execution": "NOT_EXECUTED_HERE_REQUIRED_SEPARATE_CURRENT_NATIVE_GATE"},
             "Current runtime report changed population, mode, source or outcome")
        verify_unit_log(evidence_file(artifacts, "runtime/runtime-" + mode + ".log").read_text(encoding="utf-8"), ordinary, descriptions)
    formal_root = artifacts / "formal/formal"
    formal = verify_current_formal(formal_root, read_json(evidence_file(formal_root, "result.json")), current_audit_names(repo),
                                   source, compiler.canonical_sha256(manifest), environment, packages)
    old_path = list(sys.path)
    try:
        sys.path.insert(0, str(repo))
        from research.RHRC.integration.opica_round3 import constraint_atlas, source_checker
        atlas = constraint_atlas.check_atlas(repo, artifacts / "formal/atlas")
        evaluator_kwargs = {"expected_head": source["checked_commit"],
                            "expected_tree": source["checked_tree"], "recompute": True,
                            "artifact_collection_root": artifacts}
        if recompute_output is not None:
            need(not recompute_output.exists() and not recompute_output.resolve().is_relative_to(artifacts.resolve())
                 and not recompute_output.resolve().is_relative_to(repo), "Fresh recomputation output outside source and input artifacts required")
            evaluator_kwargs["recompute_output"] = recompute_output
        evaluator = source_checker.verify_evaluator_evidence(repo, artifacts / "evaluator", **evaluator_kwargs)
        for component, label in ((atlas, "statement atlas"), (evaluator, "complete-source evaluator")):
            require_open_caps(component)
            need(all(component.get(key) == source[key] for key in ("checked_commit", "checked_tree"))
                 and type(component.get("status")) is str and component["status"].startswith("PASS_"),
                 "Added component did not accept the exact current source: " + label)
    finally:
        sys.path[:] = old_path
    native = {}
    registry = read_json(repo / R2 / "CONTROL_REGISTRY.json")
    for mode in ("normal", "optimized"):
        data = read_json(evidence_file(artifacts, "formal/current-native-" + mode + ".json"))
        fields = {"schema", "mode", "python_optimized", "test_id", "run", "skipped", "checked_commit", "checked_tree",
                  "raw_artifacts", "independent_protected_reparse", "scope", "full_core_accepted", "full_release_accepted", "RH", "Step4"}
        need(type(data) is dict and set(data) == fields, "Exact current native unit report fields required")
        require_open_caps(data)
        need(data.get("schema") == "OPICA3_CURRENT_NATIVE_ROUND2_UNIT_V1" and data.get("mode") == mode
             and data["python_optimized"] is (mode == "optimized")
             and data["scope"] == "CURRENT_SINGLE_NATIVE_UNIT_ACTUAL_SEVEN_POSITIVE_AND_SEVEN_TYPE_REJECTION_COMMANDS"
             and data.get("test_id") == NATIVE_CASE and type(data.get("run")) is int and data["run"] == 1
             and type(data.get("skipped")) is int and data["skipped"] == 0
             and all(data.get(k) == source[k] for k in ("checked_commit", "checked_tree")), "Current native unit identity/outcome differs")
        verify_unit_log(evidence_file(artifacts, "formal/current-native-" + mode + ".log").read_text(encoding="utf-8"), [NATIVE_CASE], descriptions)
        parent = artifacts / ("formal/current-native-" + mode)
        children = list(parent.iterdir())
        need(len(children) == 1 and children[0].is_dir(), "One unique current native artifact population required")
        recorded = data.get("raw_artifacts")
        need(type(recorded) is str, "Recorded native producer root required")
        path = PureWindowsPath(recorded) if re.match(r"^[A-Za-z]:[\\/]", recorded) else PurePosixPath(recorded)
        need(path.is_absolute() and ".." not in path.parts and path.name == children[0].name
             and path.parent.name == "current-native-" + mode, "Native artifact relocation changed its original population")
        native[mode] = controls.verify_typed_control_artifacts(repo, children[0], registry, optimized=(mode == "optimized"))
        need(data.get("independent_protected_reparse") == native[mode], "Serialized native reparse summary differs")
    canonical_root = artifacts / "formal/current-canonical/generated"
    generated = read_json(evidence_file(canonical_root, "result.json"))
    need(type(generated) is dict and set(generated) == {"schema", "status", "before", "after", "command", "transport",
         "full_core_accepted", "full_release_accepted", "RH", "Step4"}, "Exact current canonical check fields required")
    require_open_caps(generated)
    policy = path_policy(repo)
    paths = [row["path"] for row in read_json(repo / R2 / "BUILD_MANIFEST.json")["generated"]]
    need(len(paths) == len(set(paths)) == 81 and sorted(paths) == policy["generated"], "Exact canonical producer inventory required")
    products = [{"path": name, "bytes": (repo / name).stat().st_size, "sha256": sha(repo / name)}
                for name in paths]
    command = generated.get("command", {})
    need(generated.get("schema") == "OPICA2_GENERATED_CHECK_V1"
         and generated.get("status") == "PASS_CANONICAL_CHECK_WITHOUT_REWRITE"
         and len(products) == 81 and same_json(generated.get("before"), products) and same_json(generated.get("after"), products)
         and type(command) is dict and set(command) == {"argv", "returncode", "stdout_sha256", "stderr_sha256", "working_tree_sha"}
         and type(command.get("returncode")) is int and command["returncode"] == 0
         and command.get("working_tree_sha") == source["checked_tree"], "Current exact81 check result differs or rewrote products")
    argv = command.get("argv")
    need(type(argv) is list and len(argv) == 4 and type(argv[0]) is str and argv[0]
         and argv[1:] == ["-B", "research/RHRC/tools/materialize_derived_state.py", "--check"]
         and generated.get("transport") == {"mode": "DIRECT_FROZEN_CLI_PLATFORM_DEFAULT_UNCHANGED", "original_argv": argv},
         "Exact Linux check-only canonical producer recipe required")
    for channel in ("stdout", "stderr"):
        need(command[channel + "_sha256"] == sha(evidence_file(canonical_root, "canonical-generated-check." + channel + ".log")),
             "Current canonical raw command log changed")
    need(inspect_descendant(repo) == source and compiler.source_manifest(repo) == manifest
         and compiler.validate_environment(repo) == environment and compiler.validate_packages(repo) == packages,
         "Current source or pinned packages changed during aggregate reparse")
    need(artifact_inventory(artifacts) == before_artifacts and same_json(read_json(needs_path), required_needs),
         "Input artifacts or required-job evidence changed during aggregate reparse")
    require_clean_source(repo)
    return {"schema": "OPICA3_CURRENT_BUILD_AGGREGATE_V2", "status": "PASS_CURRENT_BUILD_AGGREGATE",
            "checked_commit": source["checked_commit"], "checked_tree": source["checked_tree"],
            "descriptor_sha256": source["descriptor_sha256"], "path_policy_sha256": source["path_policy_sha256"],
            "scope": "USER_SELECTED_D01_D05_ATLAS_COMPLETE_SOURCE_K2_K3_ISSUE296_FALSIFIERS_CURRENT_ORIGINAL40_REGRESSION",
            "required_jobs": sorted(required_needs), "source_manifest_sha256": compiler.canonical_sha256(manifest),
            "formal": formal, "atlas": atlas, "evaluator": evaluator,
            "ordinary_tests_per_mode": len(ordinary), "guard_tests_per_mode": guard_count,
            "evaluator_tests_per_mode": evaluator_count,
            "current_native": native, "canonical_products": len(products), "artifact_inventory": before_artifacts,
            "fresh_compiler_replay": False, "provider_authenticity_established_here": False,
            "historical_baseline_substituted_for_current": False,
            "authority": "CURRENT_SELECTED_BUILD_ARTIFACT_COMPOSITION_ONLY_NOT_FULL_ROUND2_CORE_OR_RELEASE", **CAPS}


def formal_checks(repo: Path, output: Path, timeout: int) -> dict[str, Any]:
    """CI-only native commands. No invocation is made by a source preflight."""
    repo, output = repo.resolve(), output.resolve()
    need(not output.is_relative_to(repo) and not output.exists(), "Fresh external compiler evidence required")
    source = inspect_descendant(repo)
    need(not git_text(repo, "status", "--porcelain", "--untracked-files=all"), "Compiler gate needs clean source")
    expected_head = os.environ.get("REQUESTED_HEAD", source["checked_commit"])
    need(source["checked_commit"] == expected_head, "Compiler gate checked another requested head")
    names = current_audit_names(repo)
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
              "scope": "CURRENT_FIVE_ROOTS_AND_CONSUMERS_PLUS_CURRENT_ORIGINAL_FORTY",
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
        query.write_bytes(render_current_audit(names))
        text = run(["lake", "env", "lean", "-R", str(output), "-o",
                    str(output / "CurrentRootAudit.olean"), str(query)], "current-root-audit")
        need((output / "CurrentRootAudit.olean").is_file(), "Missing genuine compiler object")
        report["axioms"] = parse_axiom_audit(text, names)
        report["query_sha256"] = sha(query)
        report["object_sha256"] = sha(output / "CurrentRootAudit.olean")
        report["semantic_controls"] = []
        for index in range(5):
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
    parser.add_argument("--aggregate-artifacts", type=Path, help="Four separate same-run current job artifact roots")
    parser.add_argument("--required-needs-json", type=Path, help="Actual workflow needs object for all four current jobs")
    parser.add_argument("--aggregate-output", type=Path, help="Fresh external current build composition result directory")
    parser.add_argument("--timeout", type=int, default=20000)
    args = parser.parse_args()
    aggregate_output = None
    try:
        need(1 <= args.timeout <= 22000, "Bounded compiler timeout required")
        aggregate_args = (args.aggregate_artifacts, args.required_needs_json, args.aggregate_output)
        need(not any(p is not None for p in aggregate_args) or all(p is not None for p in aggregate_args),
             "Aggregate requires all artifact, needs and output arguments")
        need(not (args.formal_output and args.aggregate_artifacts), "Choose native producer or independent aggregate reparse")
        if args.aggregate_artifacts:
            need(not args.aggregate_output.exists() and not args.aggregate_output.resolve().is_relative_to(args.repo.resolve()),
                 "Fresh external aggregate output directory required")
            need(not args.aggregate_output.resolve().is_relative_to(args.aggregate_artifacts.resolve()),
                 "Aggregate result must be separate from immutable input artifacts")
            aggregate_output = args.aggregate_output
            aggregate_output.mkdir(parents=True, exist_ok=False)
            report = aggregate_phase1(args.repo, args.aggregate_artifacts, args.required_needs_json,
                                      recompute_output=aggregate_output / "recomputation")
        else:
            report = (formal_checks(args.repo, args.formal_output, args.timeout) if args.formal_output
                      else inspect_descendant(args.repo))
            if not args.formal_output:
                report = {**report, "python_optimized": bool(sys.flags.optimize)}
    except (OSError, ValueError, TypeError, KeyError, ArithmeticError, subprocess.SubprocessError) as exc:
        report = {"schema": "OPICA3_CURRENT_BUILD_AGGREGATE_V2" if args.aggregate_artifacts else "OPICA3_DESCENDANT_SOURCE_INSPECTION_V1",
                  "status": "FAIL_CURRENT_BUILD_AGGREGATE" if args.aggregate_artifacts else "FAIL_SOURCE_SCOPE",
                  "errors": [str(exc)], "authority": "NO_ACCEPTANCE", **CAPS}
    if args.output:
        need(not args.output.resolve().is_relative_to(args.repo.resolve()), "Evidence must be external")
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    if aggregate_output is not None:
        aggregate_output.mkdir(parents=True, exist_ok=True)
        (aggregate_output / "result.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 0 if report["status"].startswith("PASS_") else 1


if __name__ == "__main__":
    raise SystemExit(main())
