import Lean
import Lean.Util.PtrSet
import Lean.Data.Json

/-!
AUDIT_ONLY adaptation of the private lossless Expr DAG codec in
Zeta23/RHRC/Step123OutputBindings.lean at base
97926d6a949fed7af0429a373b47abc772012834.
Original source SHA-256: 991582523a383c82e6170b94b10e7d4d2006ce2fedc4f53d7a1a63d948cfd6e9.
Only the namespace and exportType visibility change. Budgets remain fail-closed.
Unsafe pointer memoization serializes data; mathematical modules never import it.
-/

open Lean

namespace Zeta23.RHRC.OpicaTypeExprExport

private def format : String := "LEAN_EXPR_DAG_V1"
private def maxNodes : Nat := 1000000
private def maxAuxNodes : Nat := 2000000
private def maxTextBytes : Nat := 1000000
private def maxPayloadBytes : Nat := 100000000

private abbrev AuxM := StateT Nat (Except String)

private def tick : AuxM Unit := do
  let n ← get
  if n == 0 then throw "DAG auxiliary serialization budget exceeded"
  set (n - 1)

private def text (s : String) : AuxM Json := do
  if s.utf8ByteSize > maxTextBytes then throw "DAG scalar text budget exceeded"
  pure (.str s)

private def tagged (tag : String) (xs : Array Json := #[]) : Json := .arr (#[.str tag] ++ xs)
private def decimal (n : Nat) : Json := .str (toString n)

private partial def nameJson (n : Name) : AuxM Json := do
  tick
  match n with
  | .anonymous => pure (tagged "anonymous")
  | .str p s => return tagged "str" #[← nameJson p, ← text s]
  | .num p n => return tagged "num" #[← nameJson p, decimal n]

private partial def levelJson (u : Level) : AuxM Json := do
  tick
  match u with
  | .zero => pure (tagged "zero")
  | .succ a => return tagged "succ" #[← levelJson a]
  | .max a b => return tagged "max" #[← levelJson a, ← levelJson b]
  | .imax a b => return tagged "imax" #[← levelJson a, ← levelJson b]
  | .param n => return tagged "param" #[← nameJson n]
  | .mvar _ => throw "DAG rejects universe metavariables"

private def substringJson (s : Substring.Raw) : AuxM Json := do
  tick
  return tagged "substring" #[← text s.str, decimal s.startPos.byteIdx, decimal s.stopPos.byteIdx]

private def sourceInfoJson (s : SourceInfo) : AuxM Json := do
  tick
  match s with
  | .none => pure (tagged "none")
  | .original leading pos trailing stop =>
      return tagged "original" #[← substringJson leading, decimal pos.byteIdx,
        ← substringJson trailing, decimal stop.byteIdx]
  | .synthetic pos stop canonical =>
      return tagged "synthetic" #[decimal pos.byteIdx, decimal stop.byteIdx, .bool canonical]

private def preresolvedJson (s : Syntax.Preresolved) : AuxM Json := do
  tick
  match s with
  | .namespace n => return tagged "namespace" #[← nameJson n]
  | .decl n fields => return tagged "decl" #[← nameJson n, .arr (← fields.toArray.mapM text)]

private partial def syntaxJson (s : Syntax) : AuxM Json := do
  tick
  match s with
  | .missing => pure (tagged "missing")
  | .node info kind args =>
      return tagged "node" #[← sourceInfoJson info, ← nameJson kind, .arr (← args.mapM syntaxJson)]
  | .atom info val => return tagged "atom" #[← sourceInfoJson info, ← text val]
  | .ident info raw val resolved =>
      return tagged "ident" #[← sourceInfoJson info, ← substringJson raw,
        ← nameJson val, .arr (← resolved.toArray.mapM preresolvedJson)]

private def dataValueJson (v : DataValue) : AuxM Json := do
  tick
  match v with
  | .ofString s => return tagged "string" #[← text s]
  | .ofBool b => pure (tagged "bool" #[.bool b])
  | .ofName n => return tagged "name" #[← nameJson n]
  | .ofNat n => pure (tagged "nat" #[decimal n])
  | .ofInt n => pure (tagged "int" #[.str (toString n)])
  | .ofSyntax s => return tagged "syntax" #[← syntaxJson s]

private def metadataJson (d : MData) : AuxM Json := do
  let mut entries := #[]
  for (key, value) in d.entries do
    tick
    entries := entries.push (.arr #[← nameJson key, ← dataValueJson value])
  pure (.arr entries)

private def binderString : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

private inductive Node where
  | bvar (index : Nat)
  | sort (level : Level)
  | const (name : Name) (levels : List Level)
  | app (fn arg : Nat)
  | lam (name : Name) (info : BinderInfo) (domain body : Nat)
  | forallE (name : Name) (info : BinderInfo) (domain body : Nat)
  | letE (name : Name) (type value body : Nat) (nondep : Bool)
  | nat (value : Nat)
  | string (value : String)
  | mdata (data : MData) (child : Nat)
  | proj (name : Name) (index child : Nat)

private def nodeJson : Node → AuxM Json
  | .bvar i => pure (tagged "bvar" #[decimal i])
  | .sort u => do return tagged "sort" #[← levelJson u]
  | .const n us => do return tagged "const" #[← nameJson n, .arr (← us.toArray.mapM levelJson)]
  | .app f a => pure (tagged "app" #[decimal f, decimal a])
  | .lam n bi d b => do return tagged "lam" #[← nameJson n, .str (binderString bi), decimal d, decimal b]
  | .forallE n bi d b => do return tagged "forall" #[← nameJson n, .str (binderString bi), decimal d, decimal b]
  | .letE n t v b nd => do return tagged "let" #[← nameJson n, decimal t, decimal v, decimal b, .bool nd]
  | .nat n => pure (tagged "nat" #[decimal n])
  | .string s => do return tagged "string" #[← text s]
  | .mdata md child => do return tagged "mdata" #[← metadataJson md, decimal child]
  | .proj n i child => do return tagged "proj" #[← nameJson n, decimal i, decimal child]

private structure Graph where
  root : Nat
  nodes : Array Node

private unsafe structure BuildState where
  cache : PtrMap Expr Nat := mkPtrMap
  canonical : Std.HashMap String Nat := {}
  nodes : Array Node := #[]
  calls : Nat := 0
  auxRemaining : Nat := maxAuxNodes

private unsafe abbrev BuildM := StateT BuildState (Except String)

private unsafe def visit (e : Expr) : BuildM Nat := do
  if let some id := (← get).cache.find? e then return id
  if (← get).calls >= maxNodes then throw "DAG node/visit budget exceeded"
  modify fun s => { s with calls := s.calls + 1 }
  let node : Node ← match e with
    | .bvar i => pure (.bvar i)
    | .sort u => pure (.sort u)
    | .const n us => pure (.const n us)
    | .app f a => do pure (Node.app (← visit f) (← visit a))
    | .lam n d b bi => do pure (Node.lam n bi (← visit d) (← visit b))
    | .forallE n d b bi => do pure (Node.forallE n bi (← visit d) (← visit b))
    | .letE n t v b nd => do pure (Node.letE n (← visit t) (← visit v) (← visit b) nd)
    | .lit (.natVal n) => pure (.nat n)
    | .lit (.strVal s) => pure (.string s)
    | .mdata md child => do pure (Node.mdata md (← visit child))
    | .proj n i child => do pure (Node.proj n i (← visit child))
    | .fvar _ => throw "DAG rejects free variables"
    | .mvar _ => throw "DAG rejects expression metavariables"
  let (json, remaining) ← match (nodeJson node).run (← get).auxRemaining with
    | .ok result => pure result
    | .error msg => throw msg
  let key := json.compress
  modify fun s => { s with auxRemaining := remaining }
  if let some id := (← get).canonical[key]? then
    modify fun s => { s with cache := s.cache.insert e id }
    pure id
  else
    let id := (← get).nodes.size
    modify fun s => { s with nodes := s.nodes.push node, cache := s.cache.insert e id, canonical := s.canonical.insert key id }
    pure id

private unsafe def buildGraphUnsafe (e : Expr) : Except String Graph := do
  if e.hasLooseBVars then throw "DAG rejects a loose root bound variable"
  let (root, state) ← (visit e).run {}
  pure {root, nodes := state.nodes}

private def Graph.toJson (g : Graph) : Except String Json := do
  let (nodes, _) ← (g.nodes.mapM nodeJson).run maxAuxNodes
  pure <| Json.mkObj [("format", .str format), ("root", decimal g.root), ("nodes", .arr nodes)]

private def graph (e : Expr) : IO Graph := do
  let result := unsafe buildGraphUnsafe e
  match result with
  | .ok g => pure g
  | .error msg => throw <| IO.userError msg

def exportType (e : Expr) : IO String := do
  let g ← graph e
  let json ← match g.toJson with
    | .ok j => pure j
    | .error msg => throw <| IO.userError msg
  let payload := json.compress
  if payload.utf8ByteSize > maxPayloadBytes then throw <| IO.userError "DAG payload budget exceeded"
  pure payload

end Zeta23.RHRC.OpicaTypeExprExport
