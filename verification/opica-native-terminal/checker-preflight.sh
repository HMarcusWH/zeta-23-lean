#!/usr/bin/env bash
# Small isolated checker qualification; never builds or alters the claim-bearing stage.
set -euo pipefail
out="$1"
work="$PWD"
scratch="$(mktemp -d)"
trap 'rm -rf -- "$scratch"' EXIT
test "$(id -u)" -ne 0
test -x /usr/bin/bwrap
toolbin="$(lean --print-prefix)/bin"
export PATH="$toolbin:$PATH"
test -x "$toolbin/leanchecker"
test -x "$toolbin/leanexport"
test -x "$toolbin/nanoda_bin"
# Record actual runner and tool identity; use identical probe in both checker jobs.
mkdir -p "$out"
test "$(uname -s)" = Linux
{
  uname -a
  cat /etc/os-release
  printf 'ImageOS=%s\nImageVersion=%s\n' "${ImageOS:-unknown}" "${ImageVersion:-unknown}"
  id
  /usr/bin/bwrap --version
} > "$out/checker-runner.log"
python - "$toolbin" "$out" <<'PY'
import hashlib, json, os, pathlib, sys, platform
bin_dir, out = map(pathlib.Path, sys.argv[1:])
release = platform.freedesktop_os_release()
tools = {n: bin_dir/n for n in ("lake", "lean", "leanchecker", "leanexport", "nanoda_bin")}
tools["bwrap"] = pathlib.Path("/usr/bin/bwrap")
digests = {n: hashlib.sha256(p.read_bytes()).hexdigest() for n,p in tools.items()}
(out/"checker-tools.sha256").write_text("".join(f"{v}  {k}\n" for k,v in sorted(digests.items())))
(out/"checker-environment.json").write_text(json.dumps({
    "os": release["ID"], "version": release["VERSION_ID"], "arch": platform.machine(),
    "tools": digests, "nonroot": os.getuid() != 0}, sort_keys=True, indent=2)+"\n")
PY
# Real namespace and sandbox operation, not merely executable discovery.
unshare --user --map-root-user /usr/bin/true 2>&1 | tee "$out/userns-probe.log"
/usr/bin/bwrap --unshare-user --unshare-pid --unshare-net --die-with-parent \
  --ro-bind / / --proc /proc --dev /dev -- /usr/bin/true 2>&1 | tee "$out/bwrap-probe.log"
printf 'NATIVE_REAL_SANDBOX_PASS\n' | tee -a "$out/bwrap-probe.log"
if [[ "${2:-}" == "--probe-only" ]]; then exit 0; fi
cp "$out/checker-tools.sha256" "$out/preflight-tools.sha256"
export COMPARATOR_BWRAP=/usr/bin/bwrap
setup() {
  local dir="$1"
  mkdir -p "$dir"
  cp "$work/lean-toolchain" "$dir/lean-toolchain"
  cat > "$dir/lakefile.toml" <<'TOML'
name = "NativeCheckerPreflight"
version = "0.1.0"
defaultTargets = ["Smoke"]
[[lean_lib]]
name = "Smoke"
[[lean_lib]]
name = "Challenge"
[[lean_lib]]
name = "Solution"
TOML
  cat > "$dir/Smoke.lean" <<'LEAN'
import Init
theorem nativeStockPreflight : True := True.intro
LEAN
  cat > "$dir/Challenge.lean" <<'LEAN'
import Init
theorem native_checker_preflight : True := by
  sorry
LEAN
  cat > "$dir/comparator.json" <<'JSON'
{
  "challenge_module": "Challenge",
  "solution_module": "Solution",
  "theorem_names": ["native_checker_preflight"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": true
}
JSON
}
setup "$scratch/clean"
cat > "$scratch/clean/Solution.lean" <<'LEAN'
import Init
theorem native_checker_preflight : True := True.intro
LEAN
(
  cd "$scratch/clean"
  lake build Smoke 2>&1 | tee "$out/preflight-build.log"
  lake env leanchecker --verbose Smoke 2>&1 | tee "$out/preflight-stock.log"
  echo STOCK_PREFLIGHT_PASS | tee -a "$out/preflight-stock.log"
  lake env leanchecker --fresh --verbose Smoke 2>&1 | tee "$out/preflight-fresh.log"
  echo FRESH_PREFLIGHT_PASS | tee -a "$out/preflight-fresh.log"
  # Comparator must build/export the solution itself, without project oleans.
  rm -rf .lake/build
  test -f lake-manifest.json
  lake comparator --config comparator.json 2>&1 | tee "$out/preflight-clean.log"
  grep -F 'Running nanoda kernel on solution' "$out/preflight-clean.log"
  grep -F 'Your solution is okay!' "$out/preflight-clean.log"
)
setup "$scratch/forbidden"
cat > "$scratch/forbidden/Solution.lean" <<'LEAN'
import Init
axiom nativePreflightForbidden : True
theorem native_checker_preflight : True := nativePreflightForbidden
LEAN
(
  cd "$scratch/forbidden"
  # The intentionally forbidden fixture must be well-typed before it is tested.
  lake build Solution 2>&1 | tee "$out/preflight-forbidden-build.log"
  rm -rf .lake/build
  test -f lake-manifest.json
  set +e
  lake comparator --config comparator.json > "$out/preflight-forbidden.log" 2>&1
  rc=$?
  set -e
  cat "$out/preflight-forbidden.log"
  printf '%s\n' "$rc" > "$out/preflight-forbidden-exit.txt"
  test "$rc" -eq 1
  grep -F nativePreflightForbidden "$out/preflight-forbidden.log"
  # Require an axiom-specific diagnostic, not merely sandbox/build failure.
  grep -Ei 'axiom' "$out/preflight-forbidden.log"
  if grep -Fq 'Your solution is okay!' "$out/preflight-forbidden.log"; then
    exit 2
  fi
)
printf 'NATIVE_CHECKER_PREFLIGHT_PASS\n' > "$out/checker-preflight-pass.txt"
