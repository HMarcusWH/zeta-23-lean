#!/usr/bin/env python3
"""Lexical inventory of known migration families in the staged terminal import closure.
Not a Lean parser, dependency audit, or proof gate. Occurrences require review/compilation.
"""
import argparse, json, pathlib, re
from collections import Counter
from extract_all import imports, mask, require, sha
P = pathlib.Path
ROOT = "Zeta23.OPICANativeTerminal.Terminal"
PATTERNS = {
    "removed_probability_map": r"\bisProbabilityMeasure_map\b",
    "removed_euclidean_eval": r"\btoEuclideanLin_apply\b",
    "removed_euclidean_one": r"\btoEuclideanLin_one\b",
    "log_derivative": r"\blogDeriv_(?:mul|div)\b",
    "continuity": r"\bcomp_of_eq\b",
    "projection": r"\bmap_sub\b",
    "ordered_products": r"\b(?:mul_nonneg|prod_nonneg)\b",
    "additive_engine": r"\badditive_combination\b",
}
REGEX = {k: re.compile(p) for k, p in PATTERNS.items()}

def candidates(text):
    return [(i, family, hit.group(0)) for i, line in enumerate(mask(text).splitlines(), 1)
            for family, rx in REGEX.items() for hit in rx.finditer(line)]

def scan(work, receipt):
    source = json.loads(receipt.read_text())
    require(source["schema"] == "NATIVE_TERMINAL_REPAIR_EPOCH_V5" and
            source["claim"] == "RH_OPEN", "wrong source lock for scan")
    overlay = {r["destination"] for r in source["overlay"]}
    seen, pending, rows, external = set(), [ROOT], [], set()
    while pending:
        module = pending.pop()
        if module in seen or module in external:
            continue
        rel = module.replace(".", "/") + ".lean"
        p = work / rel
        if not p.is_file():
            require(not (module == "Zeta23" or module.startswith("Zeta23.") or
                         module == "Zeta23Arithmetic" or module.startswith("Zeta23Arithmetic.")),
                    "missing local import " + module)
            external.add(module)
            continue
        seen.add(module)
        text = p.read_text(encoding="utf-8")
        pending.extend(imports(text))
        for line, family, token in candidates(text):
            rows.append({"module": module, "path": rel, "line": line, "family": family,
                         "token": token, "source_class": "OVERLAY" if rel in overlay else
                         ("FROZEN_ARITHMETIC" if module.startswith("Zeta23Arithmetic.") else "HISTORICAL_NATIVE"),
                         "disposition": "REVIEW_OR_COMPILE"})
    rows.sort(key=lambda r: (r["path"], r["line"], r["family"], r["token"]))
    return {"schema": "NATIVE_R5_LEXICAL_COMPATIBILITY_SCAN", "status": "ADVISORY_ONLY",
            "head": source["head"], "tree": source["tree"], "source_sha256": sha(receipt.read_bytes()),
            "claim": "RH_OPEN", "root": ROOT, "local_modules": sorted(seen),
            "external_imports": sorted(external), "counts": dict(sorted(Counter(r["family"] for r in rows).items())),
            "occurrences": rows,
            "limitations": "Lexical import traversal and token matches only; no compatibility or proof authority."}

def self_test():
    text = '-- toEuclideanLin_apply\n/- isProbabilityMeasure_map /- map_sub -/ -/\n' + \
           'def x := "logDeriv_mul"\n  rw [Matrix.toEuclideanLin_apply, logDeriv_mul]\n'
    require(candidates(text) == [(4, "removed_euclidean_eval", "toEuclideanLin_apply"),
                                (4, "log_derivative", "logDeriv_mul")], "lexical scan control failed")
    print("NATIVE_R5_LEXICAL_SCAN_CONTROL_PASS")

if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--work", type=P)
    p.add_argument("--receipt", type=P)
    p.add_argument("--out", type=P)
    p.add_argument("--self-test", action="store_true")
    a = p.parse_args()
    if a.self_test:
        self_test()
    else:
        r = scan(a.work, a.receipt)
        a.out.write_text(json.dumps(r, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print("NATIVE_R5_LEXICAL_SCAN_COMPLETE", len(r["local_modules"]), len(r["occurrences"]), r["counts"])
