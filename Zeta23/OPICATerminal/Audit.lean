import Lean

open Lean Elab Command
namespace Zeta23.OPICATerminal.Audit

def structuralDependencies : ConstantInfo → List Name
  | .inductInfo i => i.ctors ++ i.all
  | .ctorInfo i => [i.induct]
  | .recInfo i => i.all
  | _ => []

/-- Walk theorem values, opaque values, definitions, types and inductive links,
    not merely imported module names or pretty-printed theorem statements. -/
def closure (root : Name) : CoreM (Array Name) := do
  let mut seen : NameSet := {}
  let mut pending := #[root]
  seen := seen.insert root
  let mut i := 0
  while i < pending.size do
    let n := pending[i]!
    i := i+1
    let info ← getConstInfo n
    let mut used := info.type.getUsedConstantsAsSet
    if let some v := info.value? (allowOpaque := true) then
      used := used.merge v.getUsedConstantsAsSet
    for d in used.toList ++ structuralDependencies info do
      unless seen.contains d do
        seen := seen.insert d
        pending := pending.push d
  return pending

def banned (s : String) : Bool :=
  s.startsWith "UpperTheory.FinalTheorems." ||
  s.startsWith "UpperTheory.riemannHypothesis_of_everyCharacter" ||
  ["UpperTheory.Top.zeroFreeAll_of_topG",
   "UpperTheory.Top.zero_free_all_of_green_v_win",
   "UpperTheory.Top.every_character_of_green_v_win",
   "UpperTheory.Top.plugWin", "UpperTheory.Top.plugAll",
   "UpperTheory.Lit.everyE₂",
   "UpperTheory.Lit.every_character_of_theta_integrals_local_matching",
   "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin",
   "Zeta23.OPICARound4.ArithmeticFrontier.momentSliceLowerBounds_zero_of_riemannHypothesis",
   "Zeta23.OPICARound4.ArithmeticFrontier.cofinal_moment_slice_bounds_of_riemannHypothesis",
   "Zeta23.OPICARound4.ArithmeticFrontier.riemannHypothesis_iff_cofinal_moment_slice_bounds"].contains s

def audit (root : Name) (required : List Name) (nativeOnly : Bool) : CommandElabM Unit := do
  let axs ← Lean.collectAxioms root
  for ax in axs do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "terminal root {root} has forbidden axiom {ax}"
  let deps ← liftTermElabM (closure root)
  for n in deps do
    let s := n.toString
    if banned s then throwError "forbidden terminal dependency: {root} -> {n}"
    if nativeOnly && (s.startsWith "UpperTheory." || s.startsWith "Formalism." ||
        s.startsWith "OPICATerminalSupplier." || s.startsWith "OPICAR2Original.") then
      throwError "supplier contamination in {root}: {n}"
  for n in required do
    unless deps.contains n do
      throwError "required proof dependency absent: {root} -> {n}"
  liftIO <| IO.println s!"OPICA_TERMINAL_DEPENDENCY_AUDIT {root} constants={deps.size} nativeOnly={nativeOnly}"

end Zeta23.OPICATerminal.Audit
