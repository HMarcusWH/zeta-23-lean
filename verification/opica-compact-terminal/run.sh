#!/usr/bin/env bash
set -euo pipefail
work="$1"
out="$2"
mode="$3"
here="$(cd "$(dirname "$0")" && pwd)"
cd "$work"
python "$here/stage.py" --verify-pins "$work" | tee "$out/pins.log"
lean --version | tee "$out/lean-version.log"
# Separate native and supplier build targets in one common source epoch.
# Do not require old large proof or its compiled modules.
if [[ "$mode" == "native" ]]; then
  lake build Zeta23.OPICARound4.ArithmeticFrontier.ZeroFreeFloor Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure 2>&1 | tee "$out/native.log"
  exit 0
fi
lake build New.PrincipalStrip Zeta23.OPICARound4.ArithmeticFrontier.ZeroFreeFloor Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure 2>&1 | tee "$out/frontiers.log"
lake build Zeta23.OPICACompactTerminal.Terminal 2>&1 | tee "$out/terminal.log"
export OPICA_COMPACT_TERMINAL_AUDIT_DIR="$out/audit"
lake env lean AuditCompactTerminal.lean 2>&1 | tee "$out/audit.log"
for mod in New.ArithmeticOnly New.PrincipalStrip Zeta23.OPICARound4.ArithmeticFrontier.ZeroFreeFloor Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure Zeta23.OPICACompactTerminal.Terminal; do
  lake env leanchecker "$mod" 2>&1 | tee -a "$out/leanchecker.log"
done
printf 'COMPACT_TERMINAL_STOCK_KERNEL_AND_AUDITS_PASS\n' > "$out/kernel-pass.txt"
