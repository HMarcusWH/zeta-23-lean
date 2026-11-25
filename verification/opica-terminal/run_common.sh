#!/usr/bin/env bash
# This script runs inside a freshly staged original source workspace.
# Separate receipts survive failure at a later frontier; no compiled native
# proof objects are imported from another pin.
set -euo pipefail
native="$(realpath "$1")"
source_receipt="$(realpath "$2")"
out="$(realpath "$3")"
mkdir -p "$out/audit"
export OPICA_TERMINAL_AUDIT_DIR="$out/audit"
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
build() {
  lake build "$1" 2>&1 | tee "$out/$2-build.log"
}
audit() {
  lake env lean "src/$1.lean" 2>&1 | tee "$out/$2-audit.log"
  ! grep -E 'sorryAx|error:|declaration uses .sorry.' "$out/$2-audit.log"
}
build Zeta23.OPICATerminal.LiteralEnergyGrowth literal-growth
build Zeta23.OPICATerminal.DisplacementGrowth displacement-growth
build Zeta23.OPICATerminal.DirectEnergyCrosscheck direct-crosscheck
build Zeta23.OPICATerminal.PowerDetectorSupply power-supply
build Zeta23.OPICATerminal.AuditNative native
audit Zeta23/OPICATerminal/AuditNative native
build OPICATerminalSupplier.AuditHost host
audit OPICATerminalSupplier/AuditHost host
build OPICATerminalSupplier.AuditTopG topg
audit OPICATerminalSupplier/AuditTopG topg
build OPICATerminalSupplier.ClosedPrincipal closed-principal
build OPICATerminalSupplier.AuditTerminal terminal
audit OPICATerminalSupplier/AuditTerminal terminal
python3 -B "$native/verification/opica-terminal/verify_audit_receipts.py" verify \
  --workspace . --native "$native" --source "$source_receipt" \
  --mode common --audit-dir "$out/audit" --output "$out/evidence.json"
printf '%s\n' 'COMMON_PIN_KERNEL_CANDIDATE_ONLY; INDEPENDENT_REPLAY_AND_RELEASE_REVIEW_REQUIRED'
