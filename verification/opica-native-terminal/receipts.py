#!/usr/bin/env python3
"""Bind successful jobs to exact source, audit inventories and actual log bytes.
No receipt itself proves a theorem or promotes a claim."""
import argparse, hashlib, json, pathlib

P = pathlib.Path
HERE = P(__file__).resolve().parent
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ROOT_SPEC = HERE / "ROOTS.json"
ROOTS = json.loads(ROOT_SPEC.read_text())["roots"]
TERMINAL = "Zeta23.OPICANativeTerminal.riemannHypothesis_step4_native_arithmetic"
C1 = "Zeta23.OPICANativeTerminal.step4C1_native_arithmetic"

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def digest(p):
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def read_json(p):
    return json.loads(p.read_text(encoding="utf-8"))

def inventory(path):
    return {p.relative_to(path).as_posix(): digest(p) for p in sorted(path.rglob("*"))
            if p.is_file() and p.name != "qualification.json"}

def expect_text(path, text):
    require(path.is_file() and path.read_text().strip() == text,
            "missing/wrong marker: " + str(path))

def contains(path, text):
    require(path.is_file(), "missing log " + str(path))
    require(any(text in line for line in path.open(encoding="utf-8", errors="replace")),
            "missing log evidence: " + text + " in " + str(path))

def root_specs(mode):
    if mode in {"terminal", "independent"}:
        return ROOTS
    if mode == "arithmetic":
        return [r for r in ROOTS if r["role"] == "arithmetic"]
    if mode == "native":
        return [r for r in ROOTS if r["role"] == "native"]
    return []

def validate_root(root, spec):
    require(root["root"] == spec["name"] and bool(root["type"]) and bool(root["type_expr"]),
            "root identity/type drift")
    require(len(root["axioms"]) == len(set(root["axioms"])) and set(root["axioms"]) <= AXIOMS,
            "axiom drift")
    require(root["native_only"] == (spec["role"] == "native") and
            root["arithmetic_only"] == (spec["role"] == "arithmetic") and
            root["smoke_fixture"] is False and root["with_edges"] == spec["edges"],
            "root policy drift " + spec["name"])
    deps = {d["name"]: d["module"] for d in root["dependencies"]}
    require(root["count"] == len(root["dependencies"]) == len(deps) and
            spec["name"] in deps and all(deps.values()), "dependency membership drift")
    require(set(root["required"]) <= set(deps), "required dependency missing")
    if spec["role"] == "native":
        require(not any(m == "Zeta23Arithmetic" or m.startswith("Zeta23Arithmetic.") for m in deps.values()),
                "native proof contaminated by arithmetic supplier")
    if spec["role"] == "arithmetic":
        require(not any(m == "Zeta23" or m.startswith("Zeta23.") for m in deps.values()),
                "arithmetic proof contaminated by native consumer")
    if spec["name"] == TERMINAL:
        require(root["type"] == "RiemannHypothesis", "terminal proposition drift")
    if spec["name"] == C1:
        require(root["type"].split(".")[-1] == "CofinalMomentSliceVanishingErrorBounds",
                "C1 proposition drift")
    return deps

def graph_digest(path, spec, members):
    rows = {}
    member_names = set(members)
    p = path / "audit" / (spec["name"] + ".edges.jsonl")
    with p.open() as f:
        for line in f:
            row = json.loads(line)
            n = row["name"]
            require(n not in rows and members.get(n) == row["module"], "edge origin/membership drift")
            for k in ("type_refs", "value_refs", "structural_refs"):
                row[k] = sorted(set(row[k]))
                require(set(row[k]) <= member_names, "edge leaves closure " + n)
            rows[n] = hashlib.sha256(json.dumps(row, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    require(set(rows) == set(members), "edge coverage incomplete")
    h = hashlib.sha256()
    for n in sorted(rows):
        h.update((n + "\0" + rows[n] + "\n").encode())
    return h.hexdigest()

def validate_audits(path, mode):
    specs = root_specs(mode)
    if not specs:
        return {}
    require({p.stem for p in (path / "audit").glob("*.json")} == {s["name"] for s in specs},
            "wrong root receipt inventory")
    require({p.name.removesuffix(".edges.jsonl") for p in (path / "audit").glob("*.edges.jsonl")} ==
            {s["name"] for s in specs if s["edges"]}, "wrong edge receipt inventory")
    edges = {}
    for spec in specs:
        row = read_json(path / "audit" / (spec["name"] + ".json"))
        members = validate_root(row, spec)
        contains(path / "audit.log", "NATIVE_TERMINAL_ROOT_PASS " + spec["name"] + " ")
        if spec["edges"]:
            edges[spec["name"]] = graph_digest(path, spec, members)
    return edges

def verify_evidence(path, mode):
    src = read_json(path / "source.json")
    require(src["schema"] == "NATIVE_TERMINAL_REPAIR_EPOCH_V6" and src["claim"] == "RH_OPEN" and
            src["toolchain"] == "leanprover/lean4:v4.35.0" and src["package_count"] == 1 and
            src["external_project_packages"] == 0, "wrong source receipt")
    require(len(src["head"]) == len(src["tree"]) == 40 and len(src["overlay"]) == 19,
            "wrong source identity")
    contains(path / "pins.log", "NATIVE_COMMON_PIN_PASS")
    contains(path / "pins-after.log", "NATIVE_COMMON_PIN_PASS")
    contains(path / "effective-source.log", "NATIVE_R6_EFFECTIVE_SOURCE_PASS " + src["head"])
    contains(path / "lean-version.log", "version 4.35.0")
    expect_text(path / "mode-pass.txt", "NATIVE_R6_" + mode.upper().replace("-", "_") + "_PASS")
    if mode in {"terminal", "independent"}:
        expect_text(path / "kernel-pass.txt", "NATIVE_TERMINAL_STOCK_KERNEL_AND_AUDITS_PASS")
        for mod in ("Zeta23Arithmetic.New.ArithmeticOnly", "Zeta23Arithmetic.NativePrincipal",
                    "Zeta23.OPICARound4.ArithmeticFrontier.ZeroFreeFloor",
                    "Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure",
                    "Zeta23.OPICANativeTerminal.Terminal"):
            contains(path / "leanchecker.log", "STOCK_KERNEL_PASS " + mod)
        if mode == "independent":
            contains(path / "fresh-kernel.log", "FRESH_KERNEL_PASS Zeta23.OPICANativeTerminal.Terminal")
    if mode == "arithmetic":
        for mod in ("Zeta23Arithmetic.New.ArithmeticOnly", "Zeta23Arithmetic.NativePrincipal"):
            contains(path / "leanchecker.log", "STOCK_KERNEL_PASS " + mod)
    if mode in {"checker-preflight", "comparator"}:
        env = read_json(path / "checker-environment.json")
        require(env["os"] == "ubuntu" and env["version"] == "22.04" and
                env["nonroot"] is True and bool(env["arch"]), "unqualified checker runner")
        tools = env["tools"]
        require(set(tools) == {"lake", "lean", "leanchecker", "leanexport", "nanoda_bin", "bwrap"} and
                all(len(v) == 64 and all(c in "0123456789abcdef" for c in v) for v in tools.values()),
                "checker tool identity missing")
        require((path / "checker-tools.sha256").read_text() ==
                "".join(f"{v}  {k}\n" for k, v in sorted(tools.items())),
                "checker tool hash inventory drift")
        require((path / "checker-runner.log").is_file() and (path / "userns-probe.log").is_file(),
                "missing sandbox runner evidence")
        contains(path / "bwrap-probe.log", "NATIVE_REAL_SANDBOX_PASS")
    if mode == "checker-preflight":
        expect_text(path / "checker-preflight-pass.txt", "NATIVE_CHECKER_PREFLIGHT_PASS")
        contains(path / "preflight-stock.log", "STOCK_PREFLIGHT_PASS")
        contains(path / "preflight-fresh.log", "FRESH_PREFLIGHT_PASS")
        contains(path / "preflight-clean.log", "Running nanoda kernel on solution")
        contains(path / "preflight-clean.log", "Your solution is okay!")
        expect_text(path / "preflight-forbidden-exit.txt", "1")
        contains(path / "preflight-forbidden.log", "nativePreflightForbidden")
        require((path / "preflight-tools.sha256").is_file(), "missing checker preflight provenance")
    if mode == "comparator":
        contains(path / "comparator.log", "Running nanoda kernel on solution")
        contains(path / "comparator.log", "Your solution is okay!")
        require((path / "comparator-tools.sha256").is_file(), "missing alternate checker provenance")
    if mode.startswith("leaf-") or mode == "native":
        contains(path / "native-leaves.log", "Build completed successfully")
    if mode == "native":
        require(bool(read_json(path / "public-types.json")), "missing native public types")
    if mode == "smoke":
        contains(path / "audit-smoke.log", "NATIVE_AUDIT_SMOKE_PASS")
    return src, validate_audits(path, mode)

def write(path, mode):
    src, edges = verify_evidence(path, mode)
    q = {"schema": "OPICA_NATIVE_QUALIFICATION_R6", "mode": mode, "head": src["head"],
         "tree": src["tree"], "claim": "RH_OPEN", "root_spec_sha256": digest(ROOT_SPEC),
         "source_sha256": digest(path / "source.json"), "edge_digests": edges,
         "files": inventory(path)}
    (path / "qualification.json").write_text(json.dumps(q, sort_keys=True, indent=2) + "\n")
    print("NATIVE_R6_QUALIFICATION_RECEIPT", mode, src["head"])

def verify(path, mode):
    q = read_json(path / "qualification.json")
    src, edges = verify_evidence(path, mode)
    require(q["schema"] == "OPICA_NATIVE_QUALIFICATION_R6" and q["mode"] == mode and
            q["claim"] == "RH_OPEN" and (q["head"], q["tree"]) == (src["head"], src["tree"]) and
            q["root_spec_sha256"] == digest(ROOT_SPEC) and
            q["source_sha256"] == digest(path / "source.json") and q["edge_digests"] == edges and
            q["files"] == inventory(path), "qualification receipt bytes/identity mismatch")
    return q

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("mode"); ap.add_argument("path", type=P)
    ap.add_argument("--verify", action="store_true")
    args = ap.parse_args()
    if args.verify: verify(args.path, args.mode)
    else: write(args.path, args.mode)
