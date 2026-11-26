import Zeta23.CCM.DictionaryArchDiagonal
import Zeta23.CCM.NativeDampedCompletionResidual
import Zeta23.CCM.UniversalSincSourceLaw
import Zeta23.FromPNTPlus.EulerMaclaurin
import Zeta23.FromPNTPlus.ResidueCalcOnRectangles
import Zeta23.FromPNTPlus.StrongPNTPrefix
import Zeta23.FromPNTPlus.Tactic.AdditiveCombination
import Zeta23.GammaFacts.IntMu
import Zeta23.RvM.GammaSide
import Zeta23.WeilEF.GammaRBracket
import Zeta23.CCM.UniversalSincSourceCharacteristic
import Zeta23.Analytic.RectangleLogDeriv
import Zeta23.WeilEF.Landau
import Zeta23.ThmE.IntMuChi
import Lean

/-! Public declaration types, not proof bodies. The retired tactic engine is
intentionally excluded from the mathematical surface. Private/generated helper
names are excluded; any remaining public surface difference blocks admission. -/
open Lean Elab Command
set_option maxHeartbeats 0 in
run_cmd do
  let env := (← getEnv).setExporting false
  let modules := ["Zeta23.CCM.DictionaryArchDiagonal", "Zeta23.CCM.NativeDampedCompletionResidual",
    "Zeta23.CCM.UniversalSincSourceLaw", "Zeta23.FromPNTPlus.EulerMaclaurin",
    "Zeta23.FromPNTPlus.ResidueCalcOnRectangles", "Zeta23.FromPNTPlus.StrongPNTPrefix",
    "Zeta23.GammaFacts.IntMu", "Zeta23.RvM.GammaSide", "Zeta23.WeilEF.GammaRBracket",
    "Zeta23.CCM.UniversalSincSourceCharacteristic",
    "Zeta23.Analytic.RectangleLogDeriv",
    "Zeta23.WeilEF.Landau",
    "Zeta23.ThmE.IntMuChi"]
  let mut rows : Array Json := #[]
  for (n, c) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some origin := env.header.moduleNames[idx.toNat]? | continue
    let m := origin.toString
    let s := n.toString
    let isGenerated := (s.splitOn ".").any (fun p => p.startsWith "_")
    unless modules.contains m && !isGenerated do
      continue
    let kind := match c with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | _ => "other"
    rows := rows.push (Json.mkObj [("name", Json.str s), ("module", Json.str m),
      ("kind", Json.str kind), ("type_expr", Json.str (reprStr c.type))])
  unless rows.size > 0 do throwError "empty public type surface"
  let some path ← liftIO (IO.getEnv "OPICA_NATIVE_TYPE_SURFACE") |
    throwError "type surface output path required"
  let out : System.FilePath := path
  liftIO <| IO.FS.writeFile out ((Json.arr rows).compress ++ "\n")
  liftIO <| IO.println s!"NATIVE_PUBLIC_TYPE_SURFACE {rows.size}"
