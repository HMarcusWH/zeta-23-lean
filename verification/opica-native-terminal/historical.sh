#!/usr/bin/env bash
set -euo pipefail
out="$1"; here="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$out"
lean --version | tee "$out/lean-version.log"
grep -F 'version 4.33.0-rc2' "$out/lean-version.log"
python - "$out" <<'PY'
import json,pathlib,subprocess,sys
r=json.loads(pathlib.Path("lake-manifest.json").read_text())
rev="51e6992efd06126df61a496bebf8f49482a4e129"
if next(p for p in r["packages"] if p["name"]=="mathlib")["rev"] != rev:
    raise RuntimeError("historical manifest pin drift")
if subprocess.check_output(["git","-C",".lake/packages/mathlib","rev-parse","HEAD"],text=True).strip() != rev:
    raise RuntimeError("historical checkout pin drift")
PY
lake build Zeta23.FromPNTPlus.Tactic.AdditiveCombination Zeta23.FromPNTPlus.ResidueCalcOnRectangles \
  Zeta23.FromPNTPlus.StrongPNTPrefix Zeta23.FromPNTPlus.EulerMaclaurin \
  Zeta23.CCM.DictionaryArchDiagonal Zeta23.WeilEF.GammaRBracket Zeta23.RvM.GammaSide \
  Zeta23.GammaFacts.IntMu Zeta23.CCM.UniversalSincSourceLaw Zeta23.CCM.NativeDampedCompletionResidual \
  Zeta23.OPICARound4.ArithmeticFrontier.ZeroFreeFloor Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure \
  2>&1 | tee "$out/historical-leaves.log"
OPICA_NATIVE_TYPE_SURFACE="$out/public-types.json" lake env lean "$here/TypeSurface.lean" 2>&1 | tee "$out/public-types.log"
python - "$out" <<'PY'
import json,pathlib,subprocess,sys
out=pathlib.Path(sys.argv[1])
def git(*args): return subprocess.check_output(["git",*args],text=True).strip()
(out/"historical.json").write_text(json.dumps({"schema":"NATIVE_R3_HISTORICAL_TYPE_SURFACE",
 "status":"PASS","head":git("rev-parse","HEAD"),"tree":git("rev-parse","HEAD^{tree}"),
 "toolchain":"leanprover/lean4:v4.33.0-rc2","mathlib":"51e6992efd06126df61a496bebf8f49482a4e129",
 "claim":"RH_OPEN"},indent=2)+"\n")
PY
