# theoremdb

A queryable database of theorems and conjectures. The **Lean 4 source is the
source of truth**; a metaprogram extractor ([`Extract.lean`](Extract.lean)) walks
the build and emits [`theoremdb.json`](theoremdb.json) (conforming to
[`schema/theoremdb.schema.json`](schema/theoremdb.schema.json)), which is the
canonical queryable artifact. See [`plan.md`](plan.md) for the full design.

## Two layers, two QA policies

The repository is split into two layers with **different acceptance rules for
`sorry` and axioms**.

### 1. `ForMathlib/` — strict, upstreamable

Bespoke, mathlib-style definitions and lemmas intended for upstreaming to
[mathlib](https://github.com/leanprover-community/mathlib4). These files keep the
**usual strict QA**:

- **no `sorry`**, and
- **no axioms** beyond the three mathlib foundations (`propext`,
  `Classical.choice`, `Quot.sound`).

A statement that cannot meet this bar — an unproved literature theorem — is **not**
parked here as a `sorry` or an `axiom`. It is moved out to a corpus root (below);
any clean supporting *definitions* may stay.

### 2. Corpus roots (`Corpus/`, `DistributionModOne/`, `BertinPisot/`, …) — literature axioms allowed, if cited

Everything outside `ForMathlib/` is the catalogued corpus, where the rule is
relaxed to exactly one allowance:

> **A non-standard axiom is allowed iff it carries a literature reference
> `@[ref "…"]`.**

A result that is *proved in the literature* but not yet formalized here is recorded
as a Lean **`axiom`** annotated with its citation —

```lean
@[category research solved, AMS 11, ref "Bug12" "dMT04",
  solved_by "de Mathan" "Teulié" 2004]
axiom problem_10_8.variants.quadratic (ξ : ℝ) (p : ℕ) (hp : p.Prime)
    (hξ : (minpoly ℚ ξ).natDegree = 2) :
    sInf {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
      x = q * padicNorm p q * distToNearestInt (q * ξ)} = 0
```

— rather than as a `:= by sorry` stub. Because it is a genuine Lean `axiom`,
`#print axioms` surfaces the citation in **every** downstream proof that relies on
it: the literature dependency is transparent, not hidden behind a `sorry`.

Two things are deliberately **excluded** from this allowance and stay `:= by
sorry`:

- **Open conjectures** are *never* axiomatised — asserting an unproved conjecture
  as an axiom could make the corpus logically inconsistent.
- **Un-cited gaps** — a supporting lemma simply not yet finished — stay `sorry`
  until actually proved.

## Formalization status

The extractor classifies every declaration's `formalization.status` accordingly:

| status        | meaning                                                                 |
| ------------- | ----------------------------------------------------------------------- |
| `proved`      | depends only on the standard foundational axioms                        |
| `cited`       | ≥ 1 non-standard axiom, and **every** non-standard axiom carries a `@[ref]` |
| `stated_only` | depends on `sorryAx`, or on an axiom with **no** `@[ref]` (a genuine gap) |

## Build & extract

```sh
# build every corpus library (strict ForMathlib + the literature-axiom corpus)
lake build Corpus DistributionModOne ForMathlib BertinPisot

# regenerate theoremdb.json from the full corpus
lake env lean --run Extract.lean \
  $(find ForMathlib DistributionModOne BertinPisot -name '*.lean' \
     | sed 's#/#.#g; s#\.lean$##') \
  Corpus.ForMathlibAnnotations
```

Released under [CC0 1.0](LICENSE) (public-domain dedication), except
`DistributionModOne/`, which is ported from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) and
retains its Apache-2.0 headers.
