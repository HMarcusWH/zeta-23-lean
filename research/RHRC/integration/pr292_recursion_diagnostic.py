#!/usr/bin/env python3
"""Isolated, non-proof PR292 source-only Lean recursion diagnostics."""
from __future__ import annotations
import argparse
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

INTEGRATION = Path(__file__).resolve().parent
REPO = INTEGRATION.parents[2]
sys.path.insert(0, str(INTEGRATION))
import source_only_dependency_extract as extractor


def run(name: str, source: str, out: Path, timeout: int) -> dict:
    driver = out / (name + ".lean")
    driver.write_text(source, encoding="utf-8")
    log = out / (name + ".log")
    started = time.monotonic()
    with log.open("w", encoding="utf-8") as dest:
        try:
            result = subprocess.run(
                ["lake", "env", "lean", str(driver)],
                cwd=REPO, stdout=dest, stderr=subprocess.STDOUT,
                timeout=timeout)
            status = "EXIT_" + str(result.returncode)
        except subprocess.TimeoutExpired:
            status = "TIMEOUT_" + str(timeout)
    lines = log.read_text(encoding="utf-8", errors="replace").splitlines()
    summary = {
        "name": name, "status": status,
        "elapsed_seconds": round(time.monotonic() - started, 2),
        "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "run_cmd_line": next((i for i, s in enumerate(source.splitlines(), 1)
                              if s == "run_cmd do"), None),
        "marker_lines": [s for s in lines if "DIAG_" in s][:8],
        "declarations": sum("RHKG_DEP_DECL\t" in s for s in lines),
        "channels": sum("RHKG_DEP_CHANNEL\t" in s for s in lines),
        "errors": [s for s in lines if "error:" in s][-12:],
        "log_tail": lines[-18:],
    }
    (out / (name + ".json")).write_text(
        json.dumps(summary, indent=2, ensure_ascii=False) + "\n")
    print("PROBE "+json.dumps(
        {k:v for k,v in summary.items() if k != "log_tail"},
        ensure_ascii=False), flush=True)
    return summary


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--out", type=Path, required=True)
    out = p.parse_args().out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    roots = extractor.load_roots()
    names = [r["resolved_full_name"] for r in roots]
    modules = sorted({r["module"] for r in roots})
    metadata = {
        "root_count":len(roots), "module_count":len(modules),
        "root_hash":hashlib.sha256("\n".join(names).encode()).hexdigest(),
        "first_root":names[0], "last_root":names[-1],
        "authority":"DIAGNOSTIC_ONLY", "claim_cap":"RH_OPEN",
    }
    (out/"inventory.json").write_text(json.dumps(metadata,indent=2)+"\n")
    print("ROOT_INVENTORY "+json.dumps(metadata),flush=True)
    with (out/"module_build.log").open("w") as dest:
        result = subprocess.run(["lake","build",*modules],cwd=REPO,
            stdout=dest,stderr=subprocess.STDOUT)
    if result.returncode:
        print("MODULE_BUILD_FAILED "+str(result.returncode),flush=True)
        return
    print("MODULE_BUILD_SUCCEEDED "+str(len(modules)),flush=True)
    full=extractor.render_driver(roots)
    needle="  Zeta23.RHRC.exportDependencies roots"
    if full.count(needle)!=1:
        raise RuntimeError("full generated exporter call drifted")
    prefix=full[:full.index("run_cmd do")]
    single="run_cmd do\n  liftIO <| IO.println \"DIAG_SINGLE_ENTER\"\n"
    single+="  Zeta23.RHRC.exportDependencies #["+chr(96)*2+names[0]+"]\n"
    tests=[
        ("imports_only",prefix+"run_cmd do\n  liftIO <| IO.println \"DIAG_IMPORTS_ONLY\"\n",120),
        ("array_only",full.replace(needle,
            "  liftIO <| IO.println (\"DIAG_ARRAY_SIZE:\" ++ toString roots.size)"),240),
        ("first_root",prefix+single,300),
        ("first64",extractor.render_driver(roots[:64]).replace(needle,
            "  liftIO <| IO.println (\"DIAG_FIRST64_SIZE:\" ++ toString roots.size)\n"+needle),300),
        ("all_roots",full.replace(needle,
            "  liftIO <| IO.println (\"DIAG_ALL_ENTER:\" ++ toString roots.size)\n"+needle),900),
    ]
    findings=[]
    for name,source,timeout in tests:
        rec=run(name,source,out,timeout)
        findings.append(rec)
        if name=="all_roots" and rec["status"]!="EXIT_0":
            alt=source.replace("run_cmd do",
                "set_option maxRecDepth 4096\nrun_cmd do",1)
            findings.append(run("all_roots_depth4096",alt,out,900))
    (out/"SUMMARY.json").write_text(
        json.dumps({"inventory":metadata,"probes":findings,
           "firewall":"no D2, no RH claim, no production commit"},indent=2)+"\n")
    print("DONE "+json.dumps({x["name"]:{"status":x["status"],
          "markers":x["marker_lines"],"declarations":x["declarations"]}
          for x in findings}),flush=True)


if __name__=="__main__":
    main()
