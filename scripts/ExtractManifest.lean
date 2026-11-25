/-
Copyright (c) 2026 Tom Hutchcroft. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hutchcroft (with Codex assistance)

Uses the Lean 4.35.0 environment/attribute/axiom APIs. Dependency traversal design was
checked against VersoBlueprint/DependencyAnalysis.lean at
4943d3335ffa9221a39949e60836a8ad5dc2a456 (Lean FRO LLC, Emilio J. Gallego Arias,
Apache-2.0); no Verso code or prose dependency is imported.
-/
import Lean
import PercLib.Meta.Tag

open Lean

private def arr (xs : List Json) : Json := toJson xs
private def str := Json.str

private def levelJson (ps : List Name) : Level → Json
  | .zero => arr [str "zero"]
  | .succ u => arr [str "succ", levelJson ps u]
  | .max u v => arr [str "max", levelJson ps u, levelJson ps v]
  | .imax u v => arr [str "imax", levelJson ps u, levelJson ps v]
  | .param n => arr [str "param", toJson (ps.idxOf n)]
  | .mvar _ => arr [str "invalid-level-mvar"]

private def exprJson (ps : List Name) : Expr → Json
  | .bvar n => arr [str "bvar", toJson n]
  | .fvar _ => arr [str "invalid-fvar"]
  | .mvar _ => arr [str "invalid-mvar"]
  | .sort u => arr [str "sort", levelJson ps u]
  | .const n us => arr [str "const", str n.toString, toJson (us.map (levelJson ps))]
  | .app f a => arr [str "app", exprJson ps f, exprJson ps a]
  | .lam _ t b bi => arr [str "lam", str (reprStr bi), exprJson ps t, exprJson ps b]
  | .forallE _ t b bi => arr [str "forall", str (reprStr bi), exprJson ps t, exprJson ps b]
  | .letE _ t v b _ => arr [str "let", exprJson ps t, exprJson ps v, exprJson ps b]
  | .lit (.natVal n) => arr [str "nat", toJson n]
  | .lit (.strVal s) => arr [str "str", str s]
  | .mdata _ e => exprJson ps e
  | .proj n i e => arr [str "proj", str n.toString, toJson i, exprJson ps e]

/-- The constants a proof term mentions, as `build_manifest.py` uses them: every `const`
name and every `proj` structure name, deduplicated and sorted. Shared subterms are visited
once, so this is linear in the term's DAG size rather than its tree size. -/
private def proofConstants (e : Expr) : CoreM (List String) := do
  let names ← IO.mkRef ({} : NameSet)
  e.forEach fun
    | .const n _ => names.modify (·.insert n)
    | .proj n _ _ => names.modify (·.insert n)
    | _ => pure ()
  let strings := (← names.get).toList.map Name.toString |>.toArray.qsort (· < ·)
  return strings.toList.eraseDups

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def related : ConstantInfo → List Name
  | .inductInfo v => v.all ++ v.ctors
  | .ctorInfo v => [v.induct]
  | .recInfo v => v.all ++ v.rules.map (·.ctor)
  | _ => []

private def propositionBody? (info : ConstantInfo) : MetaM (Option Expr) :=
  Meta.forallTelescopeReducing info.type fun xs codomain => do
    let codomain ← Meta.whnf codomain
    unless codomain == mkSort .zero do return none
    let some value := info.value? (allowOpaque := true) | return none
    return some (← Meta.mkForallFVars xs (mkAppN value xs).headBeta)

private def record (publicNames : NameSet) (name mod : Name) (info : ConstantInfo) :
    CoreM Json := do
  let env ← getEnv
  let tag := PercLib.Meta.tagAttribute.getParam? env name
  let ranges ← findDeclarationRanges? name
  let axioms ← if tag.isSome then collectAxioms name else pure #[]
  let display ← if tag.isSome || publicNames.contains name then
    Meta.MetaM.run' do return (← Meta.ppExpr info.type).pretty
    else pure ""
  let proposition? ← Meta.MetaM.run' (propositionBody? info)
  let statementDisplay ← if tag.isSome then
    Meta.MetaM.run' do return (← Meta.ppExpr (proposition?.getD info.type)).pretty
    else pure ""
  let value? := info.value? (allowOpaque := true)
  -- Theorem proofs are summarised by the constants they reference; nothing downstream
  -- reads their structure, and writing them out in full made the snapshot unbounded.
  let body ← match info with
    | .thmInfo _ => pure ("proof_constants", toJson (← value?.mapM proofConstants))
    | _ => pure ("value", toJson (value?.map (exprJson info.levelParams)))
  return Json.mkObj [
    ("name", str name.toString), ("module", str mod.toString),
    ("kind", str (kind info)), ("tag", toJson tag),
    ("public", toJson (publicNames.contains name)),
    ("prop_valued", toJson proposition?.isSome),
    ("statement_expr", toJson (proposition?.map (exprJson info.levelParams))),
    ("type", exprJson info.levelParams info.type),
    body,
    ("related", toJson ((related info).map Name.toString)),
    ("universes", toJson info.levelParams.length),
    ("display_type", str display), ("display_statement", str statementDisplay),
    ("line", toJson (ranges.map (·.range.pos.line))),
    ("axioms", toJson (axioms.toList.map Name.toString))]

-- Each declaration gets its own heartbeat budget (`withCurrHeartbeats`), so the
-- `maxHeartbeats` limit bounds the cost of one declaration, not of the whole library.
private def extract (root : Name) (publicNames : NameSet) : CoreM Json := do
  let env ← getEnv
  let mut records : Array Json := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless root.isPrefixOf mod do continue
    records := records.push (← withCurrHeartbeats (record publicNames name mod info))
  return Json.mkObj [("declarations", toJson records)]

def main (args : List String) : IO Unit := do
  let root := (args.headD "PercLib").toName
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := root }] {} (trustLevel := 1024) (loadExts := true)
  -- The first .olean part contains exported declarations; private helpers live in
  -- later parts. Read only project modules here, without a second mathlib environment.
  let mut publicNames : NameSet := {}
  for mod in env.header.moduleNames do
    if root.isPrefixOf mod then
      let (data, _) ← readModuleData (← findOLean mod)
      for name in data.constNames do
        publicNames := publicNames.insert name
  let (result, _) ← Core.CoreM.toIO (extract root publicNames)
    { fileName := "<manifest>", fileMap := default } { env }
  IO.println result.compress
