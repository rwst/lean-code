/-
Adapted from the Formal Conjectures project (Apache License, Version 2.0):
https://github.com/google-deepmind/formal-conjectures
  FormalConjectures/Util/Attributes/Basic.lean
Changes: ported from the Lean module system to plain Lean 4; kept the `category`
and `AMS` attributes (and accessors for the extractor); dropped `formal_proof`,
the stats helpers, and `verifyCategoryCounts`.
-/
import Corpus.Util.Attributes.AMS
import Qq

/-! # Problem formalisation attributes: `category` and `AMS`

* `@[category textbook]`, `@[category research open]`, `@[category research solved]`,
  `@[category test]`, `@[category API]` — the kind/status of a statement.
* `@[AMS 11]` (or `@[AMS 11 5]`) — the AMS subject classification of a problem.
-/

open Lean Elab Meta Qq

namespace ProblemAttributes

inductive ProblemStatus
  /-- The problem is still open. -/
  | open
  /-- The problem is solved (a published informal proof is accepted by experts). -/
  | solved
  deriving Inhabited, BEq, Hashable, ToExpr

syntax problemStatus := &"open" <|> &"solved"

def problemStatus.toName (stx : TSyntax ``problemStatus) : Option Name :=
  match stx with
    | `(problemStatus| open) => ``ProblemStatus.open
    | `(problemStatus| solved) => ``ProblemStatus.solved
    | _ => none

/-- The kinds of statement that appear in our files. -/
inductive Category
  /-- A textbook level math problem. -/
  | textbook
  /-- A research level math problem, open or solved. -/
  | research : ProblemStatus → Category
  /-- A sanity-check statement (e.g. for a new definition). -/
  | test
  /-- An API statement building basic theory around a definition. -/
  | API
  deriving Inhabited, BEq, Hashable, ToExpr

syntax CategorySyntax := &"textbook"
    <|> (&"research" problemStatus) <|> &"test" <|> &"API"

structure CategoryTag where
  declName : Name
  category : Category
  informal : String
  deriving Inhabited, BEq, Hashable

initialize categoryExt : SimplePersistentEnvExtension CategoryTag (Std.HashSet CategoryTag) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl Std.HashSet.insertMany {}
    addEntryFn := .insert
  }

def addCategoryEntry {m : Type → Type} [MonadEnv m]
    (declName : Name) (cat : Category) (comment : String) : m Unit :=
  modifyEnv (categoryExt.addEntry · { declName := declName, category := cat, informal := comment })

structure SubjectTag where
  declName : Name
  subjects : List AMS
  informal : String
  deriving Inhabited, BEq, Hashable

initialize subjectExt : SimplePersistentEnvExtension SubjectTag (Std.HashSet SubjectTag) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl Std.HashSet.insertMany {}
    addEntryFn := .insert
  }

def addSubjectEntry {m : Type → Type} [MonadEnv m] (name : Name)
    (subjects : List AMS) (informal : String) : m Unit :=
  modifyEnv (subjectExt.addEntry · { declName := name, subjects := subjects, informal := informal })

/-- Convert a `CategorySyntax` node to a `Category`, annotating the syntax with
the corresponding constructor's docstring. -/
def Syntax.toCategory (stx : TSyntax ``CategorySyntax) : CoreM Category := do
  match stx with
  | `(CategorySyntax| textbook) =>
    Elab.addConstInfo stx ``Category.textbook
    return Category.textbook
  | `(CategorySyntax| research $status) =>
    let problemStatus ← do
      let some n := problemStatus.toName status | throwUnsupportedSyntax
      Elab.addConstInfo status n
      Lean.Meta.MetaM.run' <|
        unsafe Meta.evalExpr ProblemStatus q(ProblemStatus) (.const n [])
    Elab.addConstInfo stx ``Category.research
    return Category.research problemStatus
  | `(CategorySyntax| test) =>
    Elab.addConstInfo stx ``Category.test
    return Category.test
  | `(CategorySyntax| API) =>
    Elab.addConstInfo stx ``Category.API
    return Category.API
  | _ => throwUnsupportedSyntax

syntax (name := Category_attr) "category" CategorySyntax : attr

/-- Specifies the kind/status of a statement. See the file docstring. -/
initialize Lean.registerBuiltinAttribute {
  name := `Category_attr
  descr := "Annotation of status of a problem."
  add := fun decl stx _attrKind => do
    let oldDoc := (← findDocString? (← getEnv) decl).getD ""
    let (status, _comment) ← match stx with
      | `(attr| category $s) => withRef s do
        let cat ← Syntax.toCategory s
        return (cat, "")
      | _ => throwUnsupportedSyntax
    if status == .research .open then
      let env ← getEnv
      if (env.find? decl).bind (·.value?) |>.any (!·.hasSorry) then
        logWarning "If a problem has a sorry-free proof, it should not be categorised as `open`."
    addCategoryEntry decl status oldDoc
  applicationTime := .afterTypeChecking
}

syntax subjectList := many(num)

/-- Convert a `subjectList` syntax node to an array of `AMS` subjects, annotating
each numeral with the corresponding subject's docstring. -/
def Syntax.toSubjects (stx : TSyntax ``subjectList) : MetaM (Array AMS) := do
  match stx with
  | `(subjectList|$[$nums] *) =>
    nums.mapM fun (n : TSyntax `num) => do
      let nVal := n.getNat
      let name ← numToAMSName nVal
      Elab.addConstInfo n name
      unsafe Meta.evalExpr AMS q(AMS) (.const name [])
  | _ => throwUnsupportedSyntax

syntax (name := problemSubject) "AMS" subjectList : attr

/-- Specifies the AMS subject(s) of a math problem, e.g. `@[AMS 11]`. -/
initialize Lean.registerBuiltinAttribute {
  name := `problemSubject
  descr := "Annotation of the subject of a given problem statement"
  add := fun decl stx _attrKind => do
    let oldDoc := (← findDocString? (← getEnv) decl).getD ""
    let subjects ← match stx with
      | `(attr| AMS $n) => withRef n <|
        Lean.Meta.MetaM.run' (Syntax.toSubjects n)
      | _ => throwUnsupportedSyntax
    addSubjectEntry decl subjects.toList oldDoc
}

/-! ## Accessors for the extractor -/

variable {m : Type → Type} [Monad m] [MonadEnv m]

def getCategoryTags : m (Array CategoryTag) := return categoryExt.getState (← getEnv) |>.toArray
def getSubjectTags : m (Array SubjectTag) := return subjectExt.getState (← getEnv) |>.toArray

end ProblemAttributes
