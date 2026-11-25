#!/usr/bin/env bash
# Sourced by both runners. The caller sets workspace, native, out, and source_prefix.
build() {
  lake build "$1" 2>&1 | tee "$out/$2-build.log"
}
audit_module() {
  local module="$1" label="$2" rel rc=0
  rel="${module//./\/}.lean"
  build "$module" "$label-audit-module" || return $?
  lake env lean "$source_prefix$rel" 2>&1 | tee "$out/$label-audit.log" || return $?
  grep -E 'sorryAx|error:|declaration uses .sorry.' "$out/$label-audit.log" || rc=$?
  # grep 1 = no forbidden match; match OR grep error fails closed.
  (( rc == 1 ))
}
run_frontier() {
  local label="$1" rc=0
  shift
  "$@" || rc=$?
  printf '%s exit=%s\n' "$label" "$rc" | tee "$out/$label.status" || return $?
  return "$rc"
}
skip_frontier() {
  printf '%s skipped: %s\n' "$1" "$2" | tee "$out/$1.status"
}
native_math() {
  build Zeta23.OPICATerminal.LiteralEnergyGrowth literal-growth &&
  build Zeta23.OPICATerminal.DisplacementGrowth displacement-growth &&
  build Zeta23.OPICATerminal.DirectEnergyCrosscheck direct-crosscheck &&
  build Zeta23.OPICATerminal.PowerDetectorSupply power-supply &&
  build Zeta23.OPICATerminal.VerifyNative native
}
auditor_controls() {
  build Zeta23.OPICATerminal.Audit auditor &&
  bash "$native/verification/opica-terminal/run_auditor_tests.sh" 2>&1 | tee "$out/auditor-controls.log" &&
  grep -Fx 'OPICA_TERMINAL_AUDITOR_CONTROLS_PASS' "$out/auditor-controls.log"
}
