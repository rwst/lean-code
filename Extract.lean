/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Lean
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Theorem-database extractor

Walks the imported environment and emits JSON conforming to
`schema/theoremdb.schema.json`:

* **declarations** — every non-internal theorem/def in a corpus module, with its
  category (TODO: pending the inherited `category` attribute), refs, extern ids,
  group, attribution, LaTeX (docstring), pretty type, and the *auto-derived*
  `formalization` block (`uses_sorry` via `collectAxioms` → `sorryAx`; the
  `status` is `proved` / `cited` / `stated_only`, where `cited` means every
  non-standard axiom carries a literature `@[ref]`).
* **informal_results** — the registry stub nodes.
* **groups** — problem-level facts rolled up by `group` key (`conflicts` is the
  deferred linter, emitted empty for now).
* **edges** — `states_with` (auto, from the type's corpus-def constants),
  `formal_uses` (manual, resolved → always `resolved`), `informal_uses` (manual,
  `resolved` iff the registry key exists).

Run with:  `lake env lean --run Extract.lean [Module.Name ...] > theoremdb.json`
Defaults to importing `Corpus.SmokeTest` when no modules are given.
-/

open Lean Meta TheoremDB

namespace TheoremDB.Extract

/-- Namespaces holding corpus content (as opposed to mathlib/Lean dependencies).
`ForMathlib` holds our bespoke notions (Pisot, lacunary, equidistribution, Lagrange,
…); it is corpus content too, so its declarations become nodes and valid
`states_with` targets. -/
def corpusRoots : List Name := [`Corpus, `DistributionModOne, `ForMathlib, `BertinPisot, `Bugeaud, `SRS, `CC, `CITED, `AB, `BL, `B3, `L90, `RT]

/-- A module whose declarations are corpus nodes: under a corpus root, but not
the `Corpus.Util` infrastructure. -/
def isCorpusModule (n : Name) : Bool :=
  corpusRoots.any (·.isPrefixOf n) && !(`Corpus.Util).isPrefixOf n

/-- The declaration kind we record (Lean erases the `lemma`/`theorem`
distinction, so both surface as `theorem`). An `axiom` records a result asserted
on the authority of its `@[ref]` literature citation (a literature-proved theorem
we have not yet formalized), so it is a first-class node too. -/
def declKind : ConstantInfo → Option String
  | .thmInfo _ => some "theorem"
  | .defnInfo _ => some "def"
  | .axiomInfo _ => some "axiom"
  | _ => none

/-- The foundational axioms a fully formalized (`proved`) term may depend on. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

def jStrs (xs : List String) : Json := Json.arr (xs.toArray.map Json.str)

/-- Order-preserving dedup. -/
def dedup [BEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def attribJson (who : String) (year : Option Nat) : Json :=
  Json.mkObj [("who", Json.str who), ("year", year.elim Json.null (toJson ·))]

/-- The five top-level array/object fields of the extract (everything except the
`schema_version` / `generated` envelope, which `main` adds). -/
def extractCore : MetaM (List (String × Json)) := do
  let env ← getEnv
  let refTags ← getRefTags
  let externTags ← getExternTags
  let groupTags ← getGroupTags
  let formalUsesTags ← getFormalUsesTags
  let informalUsesTags ← getInformalUsesTags
  let attrTags ← getAttributionTags
  let irEntries ← getInformalResults
  let catTags ← ProblemAttributes.getCategoryTags
  let subjTags ← ProblemAttributes.getSubjectTags
  let registryKeys : Std.HashSet String := irEntries.foldl (·.insert ·.key) {}

  -- Per-declaration accessors over the flat tag arrays.
  let refsOf (nm : Name) : List String :=
    dedup <| (refTags.filter (·.declName == nm)).foldl (· ++ ·.refs) []
  let externOf (nm : Name) : List String :=
    dedup <| (externTags.filter (·.declName == nm)).foldl (· ++ ·.ids) []
  let groupOf (nm : Name) : Option String :=
    (groupTags.find? (·.declName == nm)).map (·.key)
  let attribsOf (nm : Name) (role : AttrRole) : List (String × Option Nat) :=
    dedup <| (attrTags.filter (fun t => t.declName == nm && t.role == role)).toList.map
      (fun t => (t.who, t.year))
  let categoryOf (nm : Name) : Json :=
    let kv (k : String) (s : Json) : Json := Json.mkObj [("kind", Json.str k), ("status", s)]
    match (catTags.find? (·.declName == nm)).map (·.category) with
    | none => Json.null
    | some ProblemAttributes.Category.textbook => kv "textbook" Json.null
    | some (ProblemAttributes.Category.research s) =>
        kv "research" (Json.str (match s with
          | ProblemAttributes.ProblemStatus.«open» => "open"
          | ProblemAttributes.ProblemStatus.solved => "solved"))
    | some ProblemAttributes.Category.test => kv "test" Json.null
    | some ProblemAttributes.Category.API => kv "API" Json.null
  let amsOf (nm : Name) : List Nat :=
    ((subjTags.find? (·.declName == nm)).map (·.subjects)).getD [] |>.filterMap AMS.toNat?

  -- Collect corpus nodes (module, name, info), and the set of corpus definitions
  -- (the only valid `states_with` targets).
  let mut nodes : Array (Name × Name × ConstantInfo) := #[]
  let mut corpusDefs : NameSet := {}
  for (modName, modData) in env.header.moduleNames.zip env.header.moduleData do
    if isCorpusModule modName then
      for cn in modData.constNames do
        -- Skip compiler-generated declarations. `isInternalDetail` catches the
        -- `_`-marked auxiliaries (`._sunfold`, `.match_1`, and `.eq_1`/`.eq_2`…),
        -- but the equation lemma `f.eq_def` emitted by a recursive def is *not*
        -- flagged internal; `isReservedName` catches it (and only ever matches
        -- auto-reserved names, never authored declarations).
        if cn.isInternalDetail || isReservedName env cn then continue
        let some ci := env.find? cn | continue
        let some _ := declKind ci | continue
        nodes := nodes.push (modName, cn, ci)
        if ci matches .defnInfo _ then corpusDefs := corpusDefs.insert cn

  let mut declJsons : Array Json := #[]
  let mut edgeJsons : Array Json := #[]
  let mut swCount := 0
  let mut fuCount := 0
  let mut iuCount := 0

  for (modName, cn, ci) in nodes do
    -- formalization (auto-derived). `status` is three-way:
    --   • `proved`      — depends only on the standard foundational axioms;
    --   • `cited`       — every non-standard axiom carries a literature `@[ref]`
    --                     (the result is asserted on the authority of its citation,
    --                     e.g. a published theorem recorded as an `axiom`);
    --   • `stated_only` — depends on `sorryAx`, or on a custom axiom with no
    --                     `@[ref]` — a genuine, unbacked gap.
    let axs ← collectAxioms cn
    let usesSorry := axs.contains `sorryAx
    let nonStandard := axs.toList.filter (!standardAxioms.contains ·)
    -- A non-standard axiom is *unbacked* if it is `sorryAx` or carries no `@[ref]`.
    let unbacked := nonStandard.filter (fun a => a == `sorryAx || (refsOf a).isEmpty)
    let status :=
      if nonStandard.isEmpty then "proved"
      else if unbacked.isEmpty then "cited"
      else "stated_only"
    let formalization := Json.mkObj [
      ("uses_sorry", Json.bool usesSorry),
      ("status", Json.str status),
      ("axioms", jStrs (axs.toList.map (·.toString)))]
    -- LaTeX (docstring) and pretty type
    let tex := (← findDocString? env cn).elim Json.null Json.str
    let typeStr := (← ppExpr ci.type).pretty
    declJsons := declJsons.push <| Json.mkObj [
      ("name", Json.str cn.toString),
      ("decl_kind", Json.str ((declKind ci).getD "def")),
      ("module", Json.str modName.toString),
      ("category", categoryOf cn),
      ("ams", Json.arr ((amsOf cn).toArray.map (toJson ·))),
      ("statement_tex", tex),
      ("type", Json.str typeStr),
      ("refs", jStrs (refsOf cn)),
      ("extern", jStrs (externOf cn)),
      ("group", (groupOf cn).elim Json.null Json.str),
      ("conjectured_by", Json.arr ((attribsOf cn .conjectured).toArray.map (fun (w, y) => attribJson w y))),
      ("solved_by", Json.arr ((attribsOf cn .solved).toArray.map (fun (w, y) => attribJson w y))),
      ("formalization", formalization)]

    -- states_with edges: corpus-def constants appearing in the type (auto).
    let mut seen : NameSet := {}
    for t in ci.type.getUsedConstants do
      if t != cn && corpusDefs.contains t && !seen.contains t then
        seen := seen.insert t
        swCount := swCount + 1
        edgeJsons := edgeJsons.push <| Json.mkObj [
          ("kind", Json.str "states_with"), ("from", Json.str cn.toString),
          ("to", Json.str t.toString), ("to_type", Json.str "declaration"),
          ("resolved", Json.bool true)]
    -- formal_uses edges (manual, resolved at build → always resolved).
    for tag in formalUsesTags.filter (·.declName == cn) do
      for tgt in tag.targets do
        fuCount := fuCount + 1
        edgeJsons := edgeJsons.push <| Json.mkObj [
          ("kind", Json.str "formal_uses"), ("from", Json.str cn.toString),
          ("to", Json.str tgt.toString), ("to_type", Json.str "declaration"),
          ("resolved", Json.bool true)]
    -- informal_uses edges (manual, resolved iff the registry key exists).
    for tag in informalUsesTags.filter (·.declName == cn) do
      for k in tag.keys do
        iuCount := iuCount + 1
        edgeJsons := edgeJsons.push <| Json.mkObj [
          ("kind", Json.str "informal_uses"), ("from", Json.str cn.toString),
          ("to", Json.str k), ("to_type", Json.str "informal_result"),
          ("resolved", Json.bool (registryKeys.contains k))]

  -- informal_results
  let irJsons := irEntries.map fun e => Json.mkObj [
    ("key", Json.str e.key),
    ("statement_tex", if e.latex.isEmpty then Json.null else Json.str e.latex),
    ("refs", jStrs e.refs),
    ("formalized_as", e.formalizedAs.elim Json.null (Json.str ·.toString))]

  -- groups: roll up problem-level facts by key.
  let groupKeys := dedup (groupTags.toList.map (·.key))
  let groupJsons := groupKeys.toArray.map fun key =>
    let members := (groupTags.filter (·.key == key)).toList.map (·.declName)
    let refs := dedup (members.flatMap refsOf)
    let extern := dedup (members.flatMap externOf)
    let conj := dedup (members.flatMap (attribsOf · .conjectured))
    let solv := dedup (members.flatMap (attribsOf · .solved))
    Json.mkObj [
      ("key", Json.str key),
      ("members", jStrs (members.map (·.toString))),
      ("refs", jStrs refs),
      ("extern", jStrs extern),
      ("conjectured_by", Json.arr (conj.toArray.map (fun (w, y) => attribJson w y))),
      ("solved_by", Json.arr (solv.toArray.map (fun (w, y) => attribJson w y))),
      ("conflicts", Json.arr #[])]                   -- TODO: group-consistency linter

  let stats := Json.mkObj [
    ("declarations", toJson declJsons.size),
    ("informal_results", toJson irJsons.size),
    ("groups", toJson groupJsons.size),
    ("edges", Json.mkObj [("states_with", toJson swCount),
      ("formal_uses", toJson fuCount),
      ("informal_uses", toJson iuCount)])]

  return [
    ("declarations", Json.arr declJsons),
    ("informal_results", Json.arr irJsons),
    ("groups", Json.arr groupJsons),
    ("edges", Json.arr edgeJsons),
    ("stats", stats)]

/-- The first line of a string (drops trailing newline from command output). -/
def firstLine (s : String) : String := (s.takeWhile (fun c => c != '\n' && c != '\r')).toString

/-- Best-effort shell capture; returns `""` on failure. -/
def shOut (cmd : String) (args : Array String) : IO String := do
  try return firstLine (← IO.Process.output { cmd, args }).stdout
  catch _ => return ""

end TheoremDB.Extract

open TheoremDB.Extract in
unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mods := if args.isEmpty then [`Corpus.SmokeTest] else args.map String.toName
  let env ← importModules (mods.toArray.map ({ module := · })) {} (loadExts := true)
  let core ← extractCore.run'.toIO'
    { fileName := "<extract>", fileMap := default } { env }
  let commit ← shOut "git" #["rev-parse", "HEAD"]
  let toolchain := firstLine (← (try IO.FS.readFile "lean-toolchain" catch _ => pure ""))
  let timestamp ← shOut "date" #["-u", "+%Y-%m-%dT%H:%M:%SZ"]
  let generated := Json.mkObj [
    ("git_commit", Json.str commit),
    ("lean_toolchain", Json.str toolchain),
    ("timestamp", Json.str timestamp)]
  let json := Json.mkObj <|
    [("schema_version", Json.str "1.1"), ("generated", generated)] ++ core
  let out := "theoremdb.json"
  IO.FS.writeFile out json.pretty
  IO.println s!"wrote {out}"
