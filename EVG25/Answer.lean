/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Adapted from the Formal Conjectures project
(`FormalConjecturesUtil/Answer/Syntax.lean` and `FormalConjecturesUtil/Answer.lean`)
to this repository, in the same spirit as `Corpus/Util/Attributes/Basic.lean`.
Changes from the original:
  * ported from the Lean module system to plain Lean 4;
  * only the default `alwaysTrue` behaviour is kept — the `google.answer` option,
    the `postpone` and `withAuxiliary` modes, the `InfoTree` answer collector and
    the `answerLinter` are dropped;
  * the syntax kind lives in the `EVG25` namespace instead of `Google`.
-/
import Lean.Elab.Term

/-!
# The `answer( )` elaborator

Marks up the unknown part of an *open question*, following the convention of the
`formal-conjectures` project: a question of the form "is `P` true?" is stated as

```
@[category research open, AMS 11]
theorem q : P ↔ answer(sorry) := by sorry
```

Replacing `sorry` by a proof is not enough to settle such a statement — one also
has to replace `answer(sorry)` by the actual answer, which is a mathematical
judgement, not a Lean one.  With the behaviour kept here, `answer(sorry)` in
`Prop` position elaborates to `True`, so the statement above is the assertion
`P ↔ True`, i.e. "the answer is yes"; any other `answer(e)` elaborates to `e`,
tagged with an `answer` annotation so that it can be recognised downstream.
-/

open Lean Elab Meta Term

namespace EVG25

/-- Indicates where the answer is in a problem statement. -/
syntax (name := EVG25.answer) "answer(" term ")" : term

/-- Tag an expression as the answer of a problem statement. -/
def mkAnswerAnnotation (e : Expr) : Expr := mkAnnotation `answer e

/-- Find the first subexpression carrying the `answer` annotation, returning the
inner (unwrapped) expression if found. -/
def findAnswerExpr (e : Expr) : Option Expr :=
  (e.find? fun
    | .mdata m _ => m.contains `answer
    | _ => false).map Expr.mdataExpr!

/-- Elaborator for `answer(e)`.  An `answer(sorry)` of type `Prop` elaborates to
`True`; anything else elaborates as written, under an `answer` annotation. -/
@[term_elab EVG25.answer]
def answerElab : TermElab := fun stx expectedType? => do
  match stx with
  | `(answer($a:term)) =>
    if expectedType? == some (Expr.sort .zero) && a == (← `(term| sorry)) then
      return .const ``True []
    else
      mkAnswerAnnotation <$> elabTerm a expectedType?
  | _ => Elab.throwUnsupportedSyntax

end EVG25
