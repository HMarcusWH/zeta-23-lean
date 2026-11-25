#!/usr/bin/env bash
set -euo pipefail
work="$1"; out="$2"
here="$(cd "$(dirname "$0")" && pwd)"
cd "$work"
python "$here/epoch.py" --out "$work" --verify-pins | tee "$out/pins.log"
lean --version | tee "$out/lean-version.log"
lake build Zeta23Arithmetic.NativePrincipal Zeta23.OPICARound4.ArithmeticFrontier.ZeroFreeFloor Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure 2>&1 | tee "$out/frontiers.log"
lake build Zeta23.OPICANativeTerminal.Terminal 2>&1 | tee "$out/terminal.log"
export OPICA_NATIVE_TERMINAL_AUDIT_DIR="$out/audit"
lake env lean AuditNativeTerminal.lean 2>&1 | tee "$out/audit.log"
for m in Zeta23Arithmetic.New.ArithmeticOnly Zeta23Arithmetic.NativePrincipal Zeta23.OPICANativeTerminal.Terminal; do
  lake env leanchecker "$m" 2>&1 | tee -a "$out/leanchecker.log"
done
printf 'NATIVE_TERMINAL_STOCK_KERNEL_AND_AUDITS_PASS\n' > "$out/kernel-pass.txt"
