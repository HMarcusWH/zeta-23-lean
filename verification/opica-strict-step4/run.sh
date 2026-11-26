#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
repo="$(git rev-parse --show-toplevel)"
work="$1"
out="$2"
mode="$3"
baseline="$RUNNER_TEMP/strict-r7-checkout"
terminal="Zeta23.RHReference.CompactEnergyAdapter"
perron="Zeta23.RHReference.Perron.LiteralPerronFixedStripTransfer"

case "$mode" in
  prepare)
    mkdir -p "$out"
    for rev in 7b2414b97cbfefabf15e23707d31b02708c59284 21b1663d2b2e84f4d4b2c17a9f43bf09a72127f5 347c89e926a0f335caaab13d005ea738b80ee34b b1e3e3e99fd913ba2b3560ceb3b5436cdb71f736 c109fb02385bd4f7a00890594478e3bf664cbd14 2fe4a756e8576203cfb009314861616accdb6dde cfc0e6bc92be1db226d4a84f9542ace9c4868e16 176e582916156e1df90252aeb7746dd904f24983 92bfa975807f5bc22975c3f403ab79e680d64065 85bc42262d47a5e9da889ca95b65b249a64357c7 f2bc83962ec6d331f3503095a33a91e9af8fa286; do
      git cat-file -e "$rev^{commit}" || git fetch --no-tags --depth 1 origin "$rev"
    done
    git worktree add --detach "$baseline" 7b2414b97cbfefabf15e23707d31b02708c59284
    python "$here/stage.py" --repo "$repo" --baseline "$baseline" --stage "$work" \
      --baseline-receipt "$out/r7-source.json" --receipt "$out/source.json" --head "$GITHUB_SHA"
    exit 0
    ;;
  source)
    python "$here/stage.py" --self-test
    python -O "$here/stage.py" --self-test
    python "$here/compare.py" --self-test
    python -O "$here/compare.py" --self-test
    python -O "$here/stage.py" --repo "$repo" --baseline "$baseline" --stage "$RUNNER_TEMP/optimized-strict" \
      --baseline-receipt "$RUNNER_TEMP/optimized-r7.json" --receipt "$RUNNER_TEMP/optimized-source.json" \
      --head "$GITHUB_SHA"
    cmp "$out/r7-source.json" "$RUNNER_TEMP/optimized-r7.json"
    cmp "$out/source.json" "$RUNNER_TEMP/optimized-source.json"
    ;;
  *)
    locked="${STRICT_LOCKED_RECEIPT:?missing strict source lock}"
    cmp "$locked" "$out/source.json"
    python "$here/stage.py" --stage "$work" --receipt "$out/source.json" --verify-stage
    python "$baseline/verification/opica-native-terminal/epoch.py" --out "$work" --verify-pins
    cd "$work"
    lean --version > "$out/lean-version.log"
    toolbin="$(lean --print-prefix)/bin"
    export PATH="$toolbin:$PATH"
    if [[ -d .lake/build/lib/lean ]]; then
      test -z "$(find .lake/build/lib/lean -name '*.olean' -print -quit)"
    fi
    export OPICA_STRICT_AUDIT_DIR="$out/audit"
    export OPICA_NATIVE_TERMINAL_AUDIT_DIR="$out/arithmetic-audit"
    case "$mode" in
      perron)
        lake build "$perron" 2>&1 | tee "$out/perron.log"
        lake env leanchecker --verbose "$perron" 2>&1 | tee "$out/stock-kernel.log"
        ;;
      native)
        lake build Zeta23.RHReference.CompactEnergyClosure Zeta23.RHReference.Step123Expected 2>&1 | tee "$out/native.log"
        lake env lean Zeta23/RHReference/Step123MomentHandoffAudit.lean 2>&1 | tee "$out/witness.log"
        test "$(grep -c STRICT_C1_PROOF_EDGES_PASS "$out/witness.log")" = 3
        ;;
      arithmetic)
        lake build Zeta23Arithmetic.NativePrincipal Zeta23.OPICANativeTerminal.AuditCore 2>&1 | tee "$out/arithmetic.log"
        lake env lean AuditArithmetic.lean 2>&1 | tee "$out/arithmetic-roots.log"
        lake env leanchecker --verbose Zeta23Arithmetic.NativePrincipal 2>&1 | tee "$out/stock-kernel.log"
        ;;
      common|independent)
        lake build "$terminal" Zeta23.OPICANativeTerminal.AuditCore 2>&1 | tee "$out/terminal.log"
        lake env lean Zeta23/RHReference/CompactEnergyTerminalExpected.lean 2>&1 | tee "$out/expected-type.log"
        lake env lean AuditStrictReference.lean 2>&1 | tee "$out/dependency-audit.log"
        test "$(grep -c STRICT_ROOT_PASS "$out/dependency-audit.log")" = 4
        lake env leanchecker --verbose "$terminal" 2>&1 | tee "$out/stock-kernel.log"
        if [[ "$mode" == independent ]]; then
          lake env leanchecker --fresh --verbose "$terminal" 2>&1 | tee "$out/fresh-kernel.log"
          printf 'STRICT_FRESH_KERNEL_PASS\n' >> "$out/fresh-kernel.log"
        fi
        ;;
      checker)
        bash "$baseline/verification/opica-native-terminal/checker-preflight.sh" "$out" 2>&1 | tee "$out/checker.log"
        ;;
      alternate)
        test "$(id -u)" -ne 0
        test -x /usr/bin/bwrap
        test -x "$toolbin/nanoda_bin"
        test -x "$toolbin/leanexport"
        bash "$baseline/verification/opica-native-terminal/checker-preflight.sh" "$out" --probe-only
        export COMPARATOR_BWRAP=/usr/bin/bwrap
        lake comparator --config strict_comparator/config.json 2>&1 | tee "$out/alternate.log"
        grep -F 'Running nanoda kernel on solution' "$out/alternate.log"
        grep -F 'Your solution is okay!' "$out/alternate.log"
        ;;
      *) printf 'unknown strict mode %s\n' "$mode" >&2; exit 2 ;;
    esac
    python "$here/stage.py" --stage "$work" --receipt "$out/source.json" --verify-stage
    python "$baseline/verification/opica-native-terminal/epoch.py" --out "$work" --verify-pins
    cmp "$locked" "$out/source.json"
    ;;
esac
python "$here/compare.py" receipt "$mode" "$out"
