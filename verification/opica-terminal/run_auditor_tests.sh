#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
cp "$here/auditor-tests/OPICAAuditFixture.lean.txt" "$tmp/OPICAAuditFixture.lean"
cp "$here/auditor-tests/OPICAAuditTest.lean" "$tmp/"
# Separate temporary environment: the intentionally bad test axiom must never
# enter the native or common terminal source closure or emit proof receipts.
unset OPICA_TERMINAL_AUDIT_DIR
lake env bash -c '
  set -euo pipefail
  cd "$1"
  export LEAN_PATH="$PWD${LEAN_PATH:+:$LEAN_PATH}"
  lean -o OPICAAuditFixture.olean OPICAAuditFixture.lean
  lean OPICAAuditTest.lean
' bash "$tmp"
printf '%s\n' OPICA_TERMINAL_AUDITOR_CONTROLS_PASS
