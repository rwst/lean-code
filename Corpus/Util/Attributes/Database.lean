/-
Copyright 2026 The lean-code Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-/
import Lean

/-!
# Theorem-database annotation attributes

These attributes carry the *authored* dimensions of the theorem database. They
follow the `formal-conjectures` pattern: each is registered as a builtin
attribute backed by a `SimplePersistentEnvExtension` keyed on the declaration
name, so a `lake build` type-checks the annotations and the extractor can read
them back out of the environment.

The `category`, `AMS`, and `formal_proof` attributes are inherited verbatim from
`formal-conjectures` (copy `Util/Attributes/AMS.lean` and the relevant parts of
`Util/Attributes/Basic.lean`); they are not redefined here.

Two dimensions are **not** attributes and are absent from this file:
* `states_with` — auto-derived by the extractor from the constants in a
  declaration's signature (your-namespace defs only);
* `formalization` status — auto-derived from `#print axioms` (`sorryAx`).

## Authored dimensions defined here

| Attribute / command          | Dimension                                  |
|------------------------------|--------------------------------------------|
| `@[ref "BEGL96" "Er97"]`     | literature references (opaque strings)     |
| `@[formal_uses Foo Bar]`     | proof-level deps with a Lean `Name`        |
| `@[informal_uses "rh"]`      | proof-level deps into the informal registry|
| `@[group "erdos124"]`        | variant-cluster key                        |
| `@[conjectured_by "Erdős" 1997]` | attribution + year                     |
| `@[solved_by "Alexeev" 2024]`| attribution + year                         |
| `@[extern_id "OEIS:A000045"]`| external identifiers                       |
| `informal_result "rh" ...`   | declare a registry stub node               |

Note: the database *field* is called `extern`, but the Lean attribute keyword is
`extern_id` to avoid colliding with Lean's builtin `@[extern]` compiler
attribute.
-/

open Lean Elab

namespace TheoremDB

/-! ## Tag types and environment extensions -/

/-- A reference tag: the opaque `@[ref ...]` strings on a declaration. -/
structure RefTag where
  declName : Name
  refs : List String
  deriving Inhabited, BEq, Hashable

/-- External-identifier tag from `@[extern_id ...]`. -/
structure ExternTag where
  declName : Name
  ids : List String
  deriving Inhabited, BEq, Hashable

/-- Variant-cluster key from `@[group ...]`. -/
structure GroupTag where
  declName : Name
  key : String
  deriving Inhabited, BEq, Hashable

/-- Proof-level dependencies with a Lean `Name`, from `@[formal_uses ...]`. -/
structure FormalUsesTag where
  declName : Name
  targets : List Name
  deriving Inhabited, BEq, Hashable

/-- Proof-level dependencies into the informal registry, from
`@[informal_uses ...]`. The strings are registry keys. -/
structure InformalUsesTag where
  declName : Name
  keys : List String
  deriving Inhabited, BEq, Hashable

/-- Whether an attribution is a conjecturing or a solving credit. -/
inductive AttrRole
  | conjectured
  | solved
  deriving Inhabited, BEq, Hashable, Repr

/-- One who/when credit from `@[conjectured_by ...]` / `@[solved_by ...]`. -/
structure AttributionTag where
  declName : Name
  role : AttrRole
  who : String
  year : Option Nat
  deriving Inhabited, BEq, Hashable

/-- A registry entry for a real-world result with no Lean `Name` (yet). The
target of `informal_uses` edges. -/
structure InformalResultEntry where
  key : String
  latex : String := ""
  refs : List String := []
  /-- Set once the result is formalized: the declaration that now states it. -/
  formalizedAs : Option Name := none
  deriving Inhabited, BEq, Hashable

-- `nm` is passed explicitly because the descriptor's `name` field otherwise
-- defaults to `decl_name%`, which would resolve to `mkExt` for every extension
-- and collide. Each call site supplies its own unique name.
private abbrev mkExt (nm : Name) (α) [Inhabited α] [BEq α] [Hashable α] :=
  registerSimplePersistentEnvExtension (α := α) (σ := Std.HashSet α) {
    name := nm
    addImportedFn := fun as => as.foldl Std.HashSet.insertMany {}
    addEntryFn := .insert
  }

initialize refExt : SimplePersistentEnvExtension RefTag (Std.HashSet RefTag) ←
  mkExt `TheoremDB.refExt RefTag
initialize externExt : SimplePersistentEnvExtension ExternTag (Std.HashSet ExternTag) ←
  mkExt `TheoremDB.externExt ExternTag
initialize groupExt : SimplePersistentEnvExtension GroupTag (Std.HashSet GroupTag) ←
  mkExt `TheoremDB.groupExt GroupTag
initialize formalUsesExt : SimplePersistentEnvExtension FormalUsesTag (Std.HashSet FormalUsesTag) ←
  mkExt `TheoremDB.formalUsesExt FormalUsesTag
initialize informalUsesExt : SimplePersistentEnvExtension InformalUsesTag (Std.HashSet InformalUsesTag) ←
  mkExt `TheoremDB.informalUsesExt InformalUsesTag
initialize attributionExt : SimplePersistentEnvExtension AttributionTag (Std.HashSet AttributionTag) ←
  mkExt `TheoremDB.attributionExt AttributionTag
initialize informalResultExt :
    SimplePersistentEnvExtension InformalResultEntry (Std.HashSet InformalResultEntry) ←
  mkExt `TheoremDB.informalResultExt InformalResultEntry

/-! ## `@[ref ...]` — literature references -/

syntax (name := refAttr) "ref" str+ : attr

/-- Records opaque literature-reference strings for a declaration.
Usage: `@[ref "BEGL96" "Er97"]`. The strings are deliberately unvalidated and
are not graph nodes — they are decoration. -/
initialize Lean.registerBuiltinAttribute {
  name := `refAttr
  descr := "Literature references (opaque strings)."
  applicationTime := .afterTypeChecking
  add := fun decl stx _kind => do
    match stx with
    | `(attr| ref $ss*) =>
      modifyEnv (refExt.addEntry · { declName := decl, refs := (ss.map (·.getString)).toList })
    | _ => throwUnsupportedSyntax
}

/-! ## `@[extern_id ...]` — external identifiers -/

syntax (name := externIdAttr) "extern_id" str+ : attr

/-- Records typed external identifiers for cross-referencing.
Usage: `@[extern_id "erdosproblems.com/124" "OEIS:A000045"]`. -/
initialize Lean.registerBuiltinAttribute {
  name := `externIdAttr
  descr := "External identifiers (erdosproblems.com, OEIS, Wikipedia, ...)."
  applicationTime := .afterTypeChecking
  add := fun decl stx _kind => do
    match stx with
    | `(attr| extern_id $ss*) =>
      modifyEnv (externExt.addEntry · { declName := decl, ids := (ss.map (·.getString)).toList })
    | _ => throwUnsupportedSyntax
}

/-! ## `@[group ...]` — variant clustering -/

syntax (name := groupAttr) "group" str : attr

/-- Clusters a declaration into a named variant group (one problem, many
variant declarations). Usage: `@[group "erdos124"]`. -/
initialize Lean.registerBuiltinAttribute {
  name := `groupAttr
  descr := "Variant-cluster key grouping the declarations of one problem."
  applicationTime := .afterTypeChecking
  add := fun decl stx _kind => do
    match stx with
    | `(attr| group $s) => modifyEnv (groupExt.addEntry · { declName := decl, key := s.getString })
    | _ => throwUnsupportedSyntax
}

/-! ## `@[formal_uses ...]` — proof-level deps by `Name` -/

syntax (name := formalUsesAttr) "formal_uses" ident+ : attr

/-- Records proof-level dependencies that have a Lean `Name`: the lemmas a
prospective proof of this (`sorry`'d) statement would invoke. Each target is
resolved at elaboration, so a typo fails `lake build`.
Usage: `@[formal_uses Foo.bar Baz.qux]`. -/
initialize Lean.registerBuiltinAttribute {
  name := `formalUsesAttr
  descr := "Proof-level dependencies referenced by Lean name."
  applicationTime := .afterTypeChecking
  add := fun decl stx _kind => do
    match stx with
    | `(attr| formal_uses $ids*) =>
      -- Resolves each identifier (adding hover info) and throws on an unknown
      -- name — the build-time guarantee that a typo fails `lake build`.
      let targets ← ids.toList.mapM fun id => realizeGlobalConstNoOverloadWithInfo id.raw
      modifyEnv (formalUsesExt.addEntry · { declName := decl, targets })
    | _ => throwUnsupportedSyntax
}

/-! ## `@[informal_uses ...]` — proof-level deps into the registry -/

syntax (name := informalUsesAttr) "informal_uses" str+ : attr

/-- Records proof-level dependencies on real-world results that are not
formalized yet, given as keys into the `informal_result` registry. An unknown
key only *warns* (drafting friction stays low). Usage:
`@[informal_uses "riemann-hypothesis"]`. -/
initialize Lean.registerBuiltinAttribute {
  name := `informalUsesAttr
  descr := "Proof-level dependencies into the informal-result registry."
  applicationTime := .afterTypeChecking
  add := fun decl stx _kind => do
    match stx with
    | `(attr| informal_uses $ss*) =>
      let keys := (ss.map (·.getString)).toList
      let known := informalResultExt.getState (← getEnv) |>.toArray.map (·.key)
      for k in keys do
        unless known.contains k do
          logWarning m!"informal_uses: unknown registry key {repr k}; \
            declare it with `informal_result {repr k}`."
      modifyEnv (informalUsesExt.addEntry · { declName := decl, keys })
    | _ => throwUnsupportedSyntax
}

/-! ## `@[conjectured_by ...]` / `@[solved_by ...]` — attribution -/

private def addAttributions (decl : Name) (role : AttrRole)
    (whos : Array (TSyntax `str)) (year : Option (TSyntax `num)) : AttrM Unit := do
  let y := year.map (·.getNat)
  for who in whos do
    modifyEnv (attributionExt.addEntry · { declName := decl, role, who := who.getString, year := y })

syntax (name := conjecturedByAttr) "conjectured_by" str+ (num)? : attr
syntax (name := solvedByAttr) "solved_by" str+ (num)? : attr

/-- Attributes a conjecture. Multiple names share the optional year.
Usage: `@[conjectured_by "Burr" "Erdős" "Graham" "Li" 1996]`. -/
initialize Lean.registerBuiltinAttribute {
  name := `conjecturedByAttr
  descr := "Who conjectured a problem, and when."
  applicationTime := .afterTypeChecking
  add := fun decl stx _kind => do
    match stx with
    | `(attr| conjectured_by $ss* $[$y]?) => addAttributions decl .conjectured ss y
    | _ => throwUnsupportedSyntax
}

/-- Attributes a solution. Multiple names share the optional year.
Usage: `@[solved_by "Boris Alexeev" 2024]`. -/
initialize Lean.registerBuiltinAttribute {
  name := `solvedByAttr
  descr := "Who solved a problem, and when."
  applicationTime := .afterTypeChecking
  add := fun decl stx _kind => do
    match stx with
    | `(attr| solved_by $ss* $[$y]?) => addAttributions decl .solved ss y
    | _ => throwUnsupportedSyntax
}

/-! ## `informal_result` — register a stub node -/

-- Non-reserved symbols (`&"..."`) so `latex`/`refs`/`formalized_as` stay usable
-- as ordinary identifiers (e.g. as struct field names) elsewhere.
syntax (name := informalResultCmd) "informal_result" str
  (&"latex" str)? (&"refs" str+)? (&"formalized_as" ident)? : command

/-- Declares an entry in the informal-result registry: a canonical node for a
real-world result that has no Lean `Name` yet, so that `informal_uses` edges can
point at it without fragmenting. Usage:
```
informal_result "riemann-hypothesis"
  latex "All nontrivial zeros of $\zeta$ have real part $1/2$."
  refs "Rie1859"
```
Add `formalized_as SomeDecl` once the result is formalized (the promotion link). -/
elab_rules : command
  | `(informal_result $key $[latex $l]? $[refs $rs*]? $[formalized_as $f]?) => do
    let formalizedAs ← match f with
      | some id => some <$> Lean.Elab.Command.liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
      | none => pure none
    let entry : InformalResultEntry := {
      key := key.getString
      latex := (l.map (·.getString)).getD ""
      refs := ((rs.map (·.toList.map (·.getString))).getD [])
      formalizedAs }
    modifyEnv (informalResultExt.addEntry · entry)

/-! ## Accessors for the extractor -/

variable {m : Type → Type} [Monad m] [MonadEnv m]

def getRefTags : m (Array RefTag) := return refExt.getState (← getEnv) |>.toArray
def getExternTags : m (Array ExternTag) := return externExt.getState (← getEnv) |>.toArray
def getGroupTags : m (Array GroupTag) := return groupExt.getState (← getEnv) |>.toArray
def getFormalUsesTags : m (Array FormalUsesTag) := return formalUsesExt.getState (← getEnv) |>.toArray
def getInformalUsesTags : m (Array InformalUsesTag) :=
  return informalUsesExt.getState (← getEnv) |>.toArray
def getAttributionTags : m (Array AttributionTag) := return attributionExt.getState (← getEnv) |>.toArray
def getInformalResults : m (Array InformalResultEntry) :=
  return informalResultExt.getState (← getEnv) |>.toArray

end TheoremDB
