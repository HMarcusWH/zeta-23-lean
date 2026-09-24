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

private def emitChannel
    (source : Name) (deps : NameSet) (channel : String) : CommandElabM Unit := do
  let mut line := s!"RHKG_DEP_CHANNEL\t{source}\t{channel}"
  for dep in deps do
    line := line ++ "\t" ++ dep.toString
  liftIO <| IO.println line

private partial def visit
    (env : Environment) (pending : List Name)
    (visited emitted scheduled : NameHashSet) : CommandElabM Unit := do
  match pending with
  | [] => return
  | decl :: rest =>
      if visited.contains decl then
        visit env rest visited emitted scheduled
      else
        let some info := env.find? decl
          | throwError "RHKG dependency export: unknown declaration {decl}"
        let mut emitted := emitted
        if !(emitted.contains decl) then
          emitDeclaration env decl
          emitted := emitted.insert decl
        -- The receipt records presence-by-channel, not occurrence multiplicity.
        -- NameSet prevents repeated appearances in a large proof term from
        -- creating duplicate protocol edges or duplicate traversal work.
        let typeDeps := info.type.getUsedConstantsAsSet
        let valueDeps := match info.value? (allowOpaque := true) with
          | some value => value.getUsedConstantsAsSet
          | none => ({} : NameSet)
        let structureDeps :=
          (NameSet.ofArray (structuralDependencies info)).filter fun dep => dep != decl

        -- Preserve exact expression-level self references if Lean emits them.
        -- Structural membership self-links are excluded because they are
        -- declaration-family bookkeeping rather than constant use.
        for dep in typeDeps do
          if !(emitted.contains dep) then
            emitDeclaration env dep
            emitted := emitted.insert dep
        for dep in valueDeps do
          if !(emitted.contains dep) then
            emitDeclaration env dep
            emitted := emitted.insert dep
        for dep in structureDeps do
          if !(emitted.contains dep) then
            emitDeclaration env dep
            emitted := emitted.insert dep

        -- Emit at most one protocol record per declaration/channel rather than
        -- one IO.println per edge. The Python side reconstructs the same exact
        -- channel presence relation from the batched records.
        emitChannel decl typeDeps "TYPE"
        emitChannel decl valueDeps "VALUE"
        emitChannel decl structureDeps "STRUCTURE"

        -- A visited set alone does not deduplicate declarations that are
        -- queued many times before their first visit. Track scheduled names
        -- so highly shared dependencies enter the pending list only once.
        let mut next := rest
        let mut scheduled := scheduled
        for dep in typeDeps do
          if isProjectLocalModule (moduleOf? env dep) && !(scheduled.contains dep) then
            next := dep :: next
            scheduled := scheduled.insert dep
        for dep in valueDeps do
          if isProjectLocalModule (moduleOf? env dep) && !(scheduled.contains dep) then
            next := dep :: next
            scheduled := scheduled.insert dep
        for dep in structureDeps do
          if isProjectLocalModule (moduleOf? env dep) && !(scheduled.contains dep) then
            next := dep :: next
            scheduled := scheduled.insert dep
        visit env next (visited.insert decl) emitted scheduled

/--
Emit the local Zeta23 dependency closure rooted at the supplied declarations.
External constants are emitted as boundary nodes but are not recursively expanded.
-/
public def exportDependencies (roots : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut scheduled : NameHashSet := {}
  for root in roots do
    scheduled := scheduled.insert root
  visit env roots.toList {} {} scheduled

end Zeta23.RHRC
