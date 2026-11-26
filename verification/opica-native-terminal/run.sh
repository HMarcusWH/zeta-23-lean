#!/usr/bin/env bash
set -euo pipefail
work="$1"; out="$2"; mode="$3"
here="$(cd "$(dirname "$0")" && pwd)"
cd "$work"
mkdir -p "$out/audit"
python "$here/epoch.py" --out "$work" --verify-pins | tee "$out/pins.log"
lean --version | tee "$out/lean-version.log"
export OPICA_NATIVE_TERMINAL_AUDIT_DIR="$out/audit"
case "$mode" in
  smoke)
    lake build Zeta23.OPICANativeTerminal.AuditCore 2>&1 | tee "$out/audit-core.log"
    lake env lean AuditSmoke.lean 2>&1 | tee "$out/audit-smoke.log"
    grep -F 'NATIVE_AUDIT_SMOKE_PASS' "$out/audit-smoke.log"
    ;;
  native)
    lake build Zeta23.FromPNTPlus.Tactic.AdditiveCombination \
      Zeta23.FromPNTPlus.ResidueCalcOnRectangles \
      Zeta23.CCM.UniversalSincSourceLaw Zeta23.FromPNTPlus.StrongPNTPrefix \
      Zeta23.FromPNTPlus.EulerMaclaurin Zeta23.CCM.DictionaryArchDiagonal \
      Zeta23.WeilEF.GammaRBracket Zeta23.RvM.GammaSide \
      Zeta23.GammaFacts.IntMu Zeta23.CCM.NativeDampedCompletionResidual 2>&1 | tee "$out/native-leaves.log"
    lake build Zeta23.OPICARound4.ArithmeticFrontier.ZeroFreeFloor \
      Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure \
      Zeta23.OPICANativeTerminal.AuditCore 2>&1 | tee "$out/native-frontier.log"
    lake env lean AuditNativeFrontier.lean 2>&1 | tee "$out/audit.log"
    printf 'NATIVE_FRONTIER_PASS\n' > "$out/frontier-pass.txt"
    ;;
  arithmetic)
    lake build Zeta23Arithmetic.New.ArithmeticOnly 2>&1 | tee "$out/arithmetic-core.log"
    lake build Zeta23Arithmetic.NativePrincipal Zeta23.OPICANativeTerminal.AuditCore 2>&1 | tee "$out/arithmetic-adapter.log"
    lake env lean AuditArithmetic.lean 2>&1 | tee "$out/audit.log"
    for mod in Zeta23Arithmetic.New.ArithmeticOnly Zeta23Arithmetic.NativePrincipal; do
      lake env leanchecker "$mod" 2>&1 | tee -a "$out/leanchecker.log"
    done
    printf 'NATIVE_ARITHMETIC_FRONTIER_PASS\n' > "$out/frontier-pass.txt"
    ;;
  terminal|independent)
    lake build Zeta23.OPICANativeTerminal.Terminal Zeta23.OPICANativeTerminal.AuditCore 2>&1 | tee "$out/terminal.log"
    lake env lean AuditNativeTerminal.lean 2>&1 | tee "$out/audit.log"
    for mod in Zeta23Arithmetic.New.ArithmeticOnly Zeta23Arithmetic.NativePrincipal \
       Zeta23.OPICARound4.ArithmeticFrontier.ZeroFreeFloor Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure \
       Zeta23.OPICANativeTerminal.Terminal; do
      lake env leanchecker "$mod" 2>&1 | tee -a "$out/leanchecker.log"
    done
    if [[ "$mode" == independent ]]; then
      lake env leanchecker --fresh Zeta23.OPICANativeTerminal.Terminal 2>&1 | tee "$out/fresh-kernel.log"
    fi
    printf 'NATIVE_TERMINAL_STOCK_KERNEL_AND_AUDITS_PASS\n' > "$out/kernel-pass.txt"
    ;;
  *) printf 'unknown mode %s\n' "$mode" >&2; exit 2 ;;
esac
