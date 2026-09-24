import Lean.Elab.Command
import Lean.PrivateName

open Lean
open Lean.Elab Command

namespace Zeta23.RHRC

/-
Compiler-facing source-candidate resolver for the RHRC integration layer.

AUDIT_ONLY. This module does not create theorem authority. It resolves
source-discovery candidates against Lean's elaborated environment using an exact
(module, final-name-component) key. Ambiguity and missing matches fail closed.
RH remains OPEN.
-/

structure SourceCandidateQuery where
  sourceId : String
  moduleName : String
  shortName : String
  sourceKind : String
deriving Repr

private def moduleOf? (env : Environment) (decl : Name) : Option Name :=
  match env.getModuleIdxFor? decl with
  | none => none
  | some modIdx => some env.allImportedModuleNames[modIdx.toNat]!

private def kindString : ConstantInfo → String
  | .axiomInfo _ => "AXIOM"
  | .defnInfo _ => "DEFINITION"
  | .thmInfo _ => "THEOREM"
  | .opaqueInfo _ => "OPAQUE"
  | .quotInfo _ => "QUOTIENT"
  | .inductInfo _ => "INDUCTIVE"
  | .ctorInfo _ => "CONSTRUCTOR"
  | .recInfo _ => "RECURSOR"

private def finalComponentString? (decl : Name) : Option String :=
  decl.components.getLast?.map (·.toString)

private def candidateKey (moduleName shortName : String) : String :=
  moduleName ++ "\u001f" ++ shortName

private def sanitizeProtocolField (s : String) : String :=
  ((s.replace "\t" " ").replace "\n" " ").replace "\r" " "

private def prettyType (type : Expr) : CommandElabM String :=
  liftTermElabM do
    let fmt ← Lean.PrettyPrinter.ppExpr type
    return sanitizeProtocolField s!"{fmt}"

private def sourceKindCompatible (sourceKind compilerKind : String) : Bool :=
  match sourceKind with
  | "THEOREM" | "LEMMA" => compilerKind == "THEOREM"
  | "DEF" | "ABBREV" => compilerKind == "DEFINITION"
  | "OPAQUE" => compilerKind == "OPAQUE"
  | "AXIOM" => compilerKind == "AXIOM"
  | "INDUCTIVE" => compilerKind == "INDUCTIVE"
  | _ => true

/--
Resolve source-discovery candidates against the exact compiler environment.

Protocol:
RHRC_CANDIDATE_RESULT <source-id> <status> <match-count>
  <full-name-or-dash> <module-or-dash> <compiler-kind-or-dash>
  <private/internal 0|1|-> <pretty-type-or-dash> <ambiguous-names-or-dash>

The output is a discovery/audit receipt only.
-/
public def resolveSourceCandidates (queries : Array SourceCandidateQuery) : CommandElabM Unit := do
  let env ← getEnv
  let mut index : Std.HashMap String (Array Name) := {}

  for (decl, _) in env.constants do
    match moduleOf? env decl, finalComponentString? decl with
    | some moduleName, some shortName =>
        let key := candidateKey moduleName.toString shortName
        let prior := index.getD key #[]
        index := index.insert key (prior.push decl)
    | _, _ => pure ()

  for query in queries do
    let matches := index.getD (candidateKey query.moduleName query.shortName) #[]
    if matches.isEmpty then
      liftIO <| IO.println s!"RHRC_CANDIDATE_RESULT\t{query.sourceId}\tNO_COMPILER_MATCH\t0\t-\t-\t-\t-\t-\t-"
    else if matches.size > 1 then
      let names := String.intercalate "," <| matches.toList.map (·.toString)
      liftIO <| IO.println s!"RHRC_CANDIDATE_RESULT\t{query.sourceId}\tAMBIGUOUS_COMPILER_MATCH\t{matches.size}\t-\t{query.moduleName}\t-\t-\t-\t{names}"
    else
      let decl := matches[0]!
      let some info := env.find? decl
        | throwError "candidate resolver: environment index lost declaration {decl}"
      let moduleText :=
        match moduleOf? env decl with
        | some moduleName => moduleName.toString
        | none => "-"
      let compilerKind := kindString info
      let privateOrInternal := decl.isInternal || isPrivateName decl
      let status :=
        if !sourceKindCompatible query.sourceKind compilerKind then
          "KIND_MISMATCH"
        else if privateOrInternal then
          "RESOLVED_PRIVATE_OR_INTERNAL"
        else
          "RESOLVED_UNIQUE"
      let typeText ← prettyType info.type
      let privateText := if privateOrInternal then "1" else "0"
      liftIO <| IO.println s!"RHRC_CANDIDATE_RESULT\t{query.sourceId}\t{status}\t1\t{decl}\t{moduleText}\t{compilerKind}\t{privateText}\t{typeText}\t-"

end Zeta23.RHRC
