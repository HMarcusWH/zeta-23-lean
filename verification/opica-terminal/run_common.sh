#!/usr/bin/env bash
# Same-pin source compilation and independent audit frontiers. Diagnostic builds
# may proceed after audit failures; candidate evidence never may.
set -euo pipefail
native="$(realpath "$1")"
source_receipt="$(realpath "$2")"
out="$(realpath "$3")"
mkdir -p "$out"
test ! -e "$out/evidence.json"
test ! -e "$out/audit"
mkdir "$out/audit"
export OPICA_TERMINAL_AUDIT_DIR="$out/audit"
source_prefix=src/
source "$native/verification/opica-terminal/frontier_helpers.sh"
test "$(cat lean-toolchain)" = "leanprover/lean4:v4.33.1"
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = "0df444a360eaa60ab8c11dca51a86af692955474"
python3 - <<'PY'
import json, subprocess
from pathlib import Path
for row in json.loads(Path("lake-manifest.json").read_text())["packages"]:
    actual=subprocess.check_output(["git","-C",str(Path(".lake/packages")/row["name"]),"rev-parse","HEAD"],text=True).strip()
    if actual!=row["rev"]:
        raise RuntimeError("dependency mismatch: "+row["name"])
PY
native_rc=0; host_rc=0; topg_rc=0; closed_rc=125; terminal_rc=125
controls_rc=0; na_rc=125; ha_rc=125; ta_rc=125; ca_rc=125; ea_rc=125
run_frontier auditor-controls auditor_controls || controls_rc=$?
run_frontier native-math native_math || native_rc=$?
run_frontier host-math build OPICATerminalSupplier.PrincipalHost host || host_rc=$?
run_frontier topg-math build OPICATerminalSupplier.TopGSource topg || topg_rc=$?
if (( host_rc == 0 && topg_rc == 0 )); then
  closed_rc=0
  run_frontier closed-principal-math build OPICATerminalSupplier.ClosedPrincipal closed-principal || closed_rc=$?
else
  skip_frontier closed-principal-math 'host or TopG mathematical build failed'
fi
if (( native_rc == 0 && closed_rc == 0 )); then
  terminal_rc=0
  run_frontier terminal-math build OPICATerminalSupplier.Terminal terminal || terminal_rc=$?
else
  skip_frontier terminal-math 'native or closed-principal mathematical build failed'
fi
# Run every eligible proof audit even when a different audit has failed.
if (( native_rc == 0 )); then
  na_rc=0
  run_frontier native-audit audit_module Zeta23.OPICATerminal.AuditNative native || na_rc=$?
else
  skip_frontier native-audit 'native mathematical build failed'
fi
if (( host_rc == 0 )); then
  ha_rc=0
  run_frontier host-audit audit_module OPICATerminalSupplier.AuditHost host || ha_rc=$?
else
  skip_frontier host-audit 'host mathematical build failed'
fi
if (( topg_rc == 0 )); then
  ta_rc=0
  run_frontier topg-audit audit_module OPICATerminalSupplier.AuditTopG topg || ta_rc=$?
else
  skip_frontier topg-audit 'TopG mathematical build failed'
fi
if (( closed_rc == 0 )); then
  ca_rc=0
  run_frontier closed-principal-audit audit_module OPICATerminalSupplier.AuditClosedPrincipal closed-principal || ca_rc=$?
else
  skip_frontier closed-principal-audit 'closed-principal mathematical build failed'
fi
if (( terminal_rc == 0 )); then
  ea_rc=0
  run_frontier terminal-audit audit_module OPICATerminalSupplier.AuditTerminal terminal || ea_rc=$?
else
  skip_frontier terminal-audit 'terminal mathematical build failed'
fi
if (( native_rc || host_rc || topg_rc || closed_rc || terminal_rc || controls_rc || na_rc || ha_rc || ta_rc || ca_rc || ea_rc )); then
  printf 'COMMON_PIN_FRONTIER_BLOCKED math=%s,%s,%s,%s,%s audits=%s,%s,%s,%s,%s controls=%s\n' \
    "$native_rc" "$host_rc" "$topg_rc" "$closed_rc" "$terminal_rc" "$na_rc" "$ha_rc" "$ta_rc" "$ca_rc" "$ea_rc" "$controls_rc" | tee "$out/terminal.status"
  exit 1
fi
verify_receipts() {
  python3 -B "$native/verification/opica-terminal/verify_audit_receipts.py" verify \
    --workspace . --native "$native" --source "$source_receipt" \
    --mode common --audit-dir "$out/audit" --output "$out/evidence.json" &&
  test -s "$out/evidence.json"
}
run_frontier receipt verify_receipts
printf '%s\n' 'COMMON_PIN_KERNEL_CANDIDATE_ONLY; INDEPENDENT_REPLAY_AND_RELEASE_REVIEW_REQUIRED'
