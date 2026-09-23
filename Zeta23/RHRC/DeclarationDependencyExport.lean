import Zeta23.RHRC.RegisteredClaimBindings
import Lean.Elab.Command
import Lean.PrivateName
import Lean.Util.FoldConsts

open Lean
open Lean.Elab Command

namespace Zeta23.RHRC

/-
Compiler-facing dependency exporter for RHKG Phase 2B.

This is AUDIT_ONLY. It creates no theorem authority and proves no mathematics.
It reads the elaborated Lean environment and emits a deterministic line protocol
for the Python receipt builder. RH remains OPEN.
-/

private def moduleOf? (env : Environment) (decl : Name) : Option Name :=
  match env.getModuleIdxFor? decl with
  | none => none
  | some modIdx => some env.allImportedModuleNames[modIdx.toNat]!

private def isProjectLocalModule : Option Name → Bool
  | none => false
  | some modName =>
      let s := modName.toString
      s == "Zeta23" || s.startsWith "Zeta23."

private def kindString : ConstantInfo → String
  | .axiomInfo _ => "AXIOM"
  | .defnInfo _ => "DEFINITION"
  | .thmInfo _ => "THEOREM"
  | .opaqueInfo _ => "OPAQUE"
  | .quotInfo _ => "QUOTIENT"
  | .inductInfo _ => "INDUCTIVE"
  | .ctorInfo _ => "CONSTRUCTOR"
  | .recInfo _ => "RECURSOR"

private def structuralDependencies : ConstantInfo → Array Name
  | .inductInfo info => (info.ctors ++ info.all).toArray
  | .ctorInfo info => #[info.induct]
  | .recInfo info => info.all.toArray
  | _ => #[]

private def emitDeclaration (env : Environment) (decl : Name) : CommandElabM Unit := do
  let some info := env.find? decl
    | throwError "RHKG dependency export: unknown declaration {decl}"
  let moduleText := match moduleOf? env decl with
    | some modName => modName.toString
    | none => "-"
  let privateOrInternalText := if decl.isInternal || isPrivateName decl then "1" else "0"
  liftIO <| IO.println s!"RHKG_DEP_DECL\t{decl}\t{moduleText}\t{kindString info}\t{privateOrInternalText}"

private def emitEdge (source target : Name) (channel : String) : CommandElabM Unit := do
  liftIO <| IO.println s!"RHKG_DEP_EDGE\t{source}\t{target}\t{channel}"

private partial def visit
    (env : Environment) (pending : List Name) (visited : NameHashSet) : CommandElabM Unit := do
  match pending with
  | [] => return
  | decl :: rest =>
      if visited.contains decl then
        visit env rest visited
      else
        let some info := env.find? decl
          | throwError "RHKG dependency export: unknown declaration {decl}"
        emitDeclaration env decl
        let typeDeps := info.type.getUsedConstants
        let valueDeps := match info.value? (allowOpaque := true) with
          | some value => value.getUsedConstants
          | none => #[]
        let structureDeps := structuralDependencies info

        -- Preserve exact expression-level self references if Lean emits them.
        -- Structural membership self-links are filtered below because they are
        -- declaration-family bookkeeping rather than constant use.
        for dep in typeDeps do
          emitDeclaration env dep
          emitEdge decl dep "TYPE"
        for dep in valueDeps do
          emitDeclaration env dep
          emitEdge decl dep "VALUE"
        for dep in structureDeps do
          if dep != decl then
            emitDeclaration env dep
            emitEdge decl dep "STRUCTURE"

        let mut next := rest
        for dep in typeDeps ++ valueDeps ++ structureDeps do
          if isProjectLocalModule (moduleOf? env dep) then
            next := dep :: next
        visit env next (visited.insert decl)

/--
Emit the local Zeta23 dependency closure rooted at the supplied declarations.
External constants are emitted as boundary nodes but are not recursively expanded.
-/
public def exportDependencies (roots : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  visit env roots.toList {}

end Zeta23.RHRC
