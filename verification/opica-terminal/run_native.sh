#!/usr/bin/env bash
set -euo pipefail
native="$(realpath .)"
out="$(realpath "$1")"
mkdir -p "$out"
test ! -e "$out/evidence.json"
test ! -e "$out/audit"
mkdir "$out/audit"
export OPICA_TERMINAL_AUDIT_DIR="$out/audit"
source_prefix=
source "$native/verification/opica-terminal/frontier_helpers.sh"
controls_rc=0; math_rc=0; audit_rc=125
run_frontier auditor-controls auditor_controls || controls_rc=$?
run_frontier native-math native_math || math_rc=$?
if (( math_rc == 0 )); then
  audit_rc=0
  run_frontier native-audit audit_module Zeta23.OPICATerminal.AuditNative native || audit_rc=$?
else
  skip_frontier native-audit 'native mathematical build failed'
fi
if (( controls_rc || math_rc || audit_rc )); then
  printf 'NATIVE_FRONTIER_BLOCKED math=%s audit=%s controls=%s\n' "$math_rc" "$audit_rc" "$controls_rc" | tee "$out/terminal.status"
  exit 1
fi
verify_receipts() {
  python3 -B verification/opica-terminal/verify_audit_receipts.py verify \
    --workspace . --native . --mode native --audit-dir "$out/audit" \
    --output "$out/evidence.json" &&
  test -s "$out/evidence.json"
}
run_frontier receipt verify_receipts
printf '%s\n' 'NATIVE_CANDIDATE_KERNEL_AND_DEPENDENCIES_ONLY; NO PROJECT PROMOTION'
