#!/usr/bin/env bash
set -euo pipefail
work="$1"; out="$2"; mode="$3"
here="$(cd "$(dirname "$0")" && pwd)"
cd "$work"
mkdir -p "$out/audit"
locked="${OPICA_R6_LOCKED_SOURCE_RECEIPT:?source-lock receipt required}"
cmp "$locked" "$out/source.json"
python "$here/epoch.py" --out "$work" --verify-pins | tee "$out/pins.log"
python "$here/epoch.py" --out "$work" --receipt "$out/source.json" --verify-stage | tee "$out/effective-source-before.log"
lean --version | tee "$out/lean-version.log"
toolbin="$(lean --print-prefix)/bin"
export PATH="$toolbin:$PATH"
export OPICA_NATIVE_TERMINAL_AUDIT_DIR="$out/audit"
# Mathlib may be cached; no project objects may predate this exact compilation.
if [[ -d .lake/build/lib/lean ]]; then
  [[ -z "$(find .lake/build/lib/lean -type f -name '*.olean' -print -quit)" ]] || {
    echo "pre-existing project olean" >&2; exit 2; }
fi
pnt=(Zeta23.FromPNTPlus.Tactic.AdditiveCombination Zeta23.FromPNTPlus.ResidueCalcOnRectangles Zeta23.FromPNTPlus.StrongPNTPrefix Zeta23.FromPNTPlus.EulerMaclaurin)
gamma=(Zeta23.CCM.DictionaryArchDiagonal Zeta23.WeilEF.GammaRBracket Zeta23.RvM.GammaSide Zeta23.GammaFacts.IntMu Zeta23.ThmE.IntMuChi)
operator=(Zeta23.CCM.UniversalSincSourceLaw Zeta23.CCM.NativeDampedCompletionResidual Zeta23.CCM.UniversalSincSourceCharacteristic Zeta23.CCM.UniversalSincSourceTail Zeta23.OPICARound4.SourceDiscrepancy Zeta23.CCM.OriginalDetectorPaddedFinitePhaseSymmetry)
analytic=(Zeta23.Analytic.RectangleLogDeriv Zeta23.WeilEF.Landau Zeta23.XiPrime.ExplicitFormula.ZeroFree Zeta23.CCM.NativeWeilResponse)
kernel_replay() {
  local mod="$1"
  lake env leanchecker --verbose "$mod" 2>&1 | tee -a "$out/leanchecker.log"
  printf 'STOCK_KERNEL_PASS %s\n' "$mod" | tee -a "$out/leanchecker.log"
}
case "$mode" in
  smoke)
    test -x "$toolbin/leanchecker"
    test -x "$toolbin/leanexport"
    lake help comparator | tee "$out/comparator-help.log"
    grep -F -- '--paranoid' "$out/comparator-help.log"
    if [[ -x "$toolbin/nanoda_bin" ]]; then
      echo "BUNDLED_NANODA_AVAILABLE" | tee "$out/alternate-preflight.log"
    else
      echo "BUNDLED_NANODA_UNAVAILABLE: alternate verification remains blocked" | tee "$out/alternate-preflight.log"
    fi
    lake build Zeta23.OPICANativeTerminal.AuditCore AuditSmokeFixtures 2>&1 | tee "$out/audit-core.log"
    lake env lean AuditSmoke.lean 2>&1 | tee "$out/audit-smoke.log"
    grep -F 'NATIVE_AUDIT_SMOKE_PASS' "$out/audit-smoke.log"
    ;;
  checker-preflight)
    bash "$here/checker-preflight.sh" "$out"
    ;;
  leaf-pnt) lake build "${pnt[@]}" 2>&1 | tee "$out/native-leaves.log" ;;
  leaf-gamma) lake build "${gamma[@]}" 2>&1 | tee "$out/native-leaves.log" ;;
  leaf-operator) lake build "${operator[@]}" 2>&1 | tee "$out/native-leaves.log" ;;
  leaf-analytic) lake build "${analytic[@]}" 2>&1 | tee "$out/native-leaves.log" ;;
  native)
    lake build "${pnt[@]}" "${gamma[@]}" "${operator[@]}" "${analytic[@]}" 2>&1 | tee "$out/native-leaves.log"
    OPICA_NATIVE_TYPE_SURFACE="$out/public-types.json" lake env lean TypeSurface.lean 2>&1 | tee "$out/public-types.log"
    lake build Zeta23.OPICARound4.ArithmeticFrontier.ZeroFreeFloor \
      Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure \
      Zeta23.OPICANativeTerminal.AuditCore 2>&1 | tee "$out/native-frontier.log"
    lake env lean AuditNativeFrontier.lean 2>&1 | tee "$out/audit.log"
    ;;
  arithmetic)
    lake build Zeta23Arithmetic.New.ArithmeticOnly 2>&1 | tee "$out/arithmetic-core.log"
    lake build Zeta23Arithmetic.NativePrincipal Zeta23.OPICANativeTerminal.AuditCore 2>&1 | tee "$out/arithmetic-adapter.log"
    lake env lean AuditArithmetic.lean 2>&1 | tee "$out/audit.log"
    for mod in Zeta23Arithmetic.New.ArithmeticOnly Zeta23Arithmetic.NativePrincipal; do kernel_replay "$mod"; done
    ;;
  terminal|independent)
    lake build Zeta23.OPICANativeTerminal.Terminal Zeta23.OPICANativeTerminal.AuditCore 2>&1 | tee "$out/terminal.log"
    lake env lean AuditNativeTerminal.lean 2>&1 | tee "$out/audit.log"
    for mod in Zeta23Arithmetic.New.ArithmeticOnly Zeta23Arithmetic.NativePrincipal \
       Zeta23.OPICARound4.ArithmeticFrontier.ZeroFreeFloor Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure \
       Zeta23.OPICANativeTerminal.Terminal; do kernel_replay "$mod"; done
    if [[ "$mode" == independent ]]; then
      lake env leanchecker --fresh --verbose Zeta23.OPICANativeTerminal.Terminal 2>&1 | tee "$out/fresh-kernel.log"
      echo 'FRESH_KERNEL_PASS Zeta23.OPICANativeTerminal.Terminal' | tee -a "$out/fresh-kernel.log"
    fi
    printf 'NATIVE_TERMINAL_STOCK_KERNEL_AND_AUDITS_PASS\n' > "$out/kernel-pass.txt"
    ;;
  comparator)
    # Lean 4.35 bundles comparator, matching leanexport, and nanoda. No legacy
    # exporter checkout, fake sandbox, or prior build of the untrusted solution.
    test "$(id -u)" -ne 0
    test -x /usr/bin/bwrap
    test -x "$toolbin/nanoda_bin"
    test -x "$toolbin/leanexport"
    bash "$here/checker-preflight.sh" "$out" --probe-only
    cp "$out/checker-tools.sha256" "$out/comparator-tools.sha256"
    export COMPARATOR_BWRAP=/usr/bin/bwrap
    lake comparator --config comparator/config-native-rh.json 2>&1 | tee "$out/comparator.log"
    grep -F 'Running nanoda kernel on solution' "$out/comparator.log"
    grep -F 'Your solution is okay!' "$out/comparator.log"
    ;;
  *) printf 'unknown mode %s\n' "$mode" >&2; exit 2 ;;
esac
python "$here/epoch.py" --out "$work" --verify-pins | tee "$out/pins-after.log"
python "$here/epoch.py" --out "$work" --receipt "$out/source.json" --verify-stage | tee "$out/effective-source.log"
cmp "$locked" "$out/source.json"
printf 'NATIVE_R6_%s_PASS\n' "$(echo "$mode" | tr '[:lower:]-' '[:upper:]_')" > "$out/mode-pass.txt"
python "$here/receipts.py" "$mode" "$out"
