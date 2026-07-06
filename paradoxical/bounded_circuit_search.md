# Bounded-circuit search — research-program work package I.1.1

Implements the first work package of **Part I** of `research-program.html`:

> **Automate the bounded-circuit search.** Write a generator that, for each fixed
> pair (R,d), enumerates all circuit shapes (aᵢ,eᵢ), applies the closure identity
> and the transcendence lower bound, and outputs either (a) an unconditional
> length bound, or (b) a finite list of candidate shapes that survive the bound.
> Reuse `circuit_baker.py`. Start with R≤6 and d≤10.

## Files

| file | role |
|---|---|
| `circuit_baker.py` | copied verbatim from `../SRS/`; provides `decompose`, `length_cutoff`, `v2` |
| `para_yah.py`      | its dependency (`T`, `parity_vector`, `remainder_from_parity`) |
| `bounded_circuit_search.py` | the generator (new) |

Run: `python3 bounded_circuit_search.py` (defaults R≤6, d≤10, length cap j≤20, ~4 s).
Push it with `--jmax N` (j≤27 ≈ 2 min); `--dmax`, `--Rmax` also tunable.

## What it does

For each shape `1^{a₁}0^{e₁}…1^{a_R}0^{e_R}` (aᵢ≥1, interior eᵢ≥1, final e_R≥0,
2^j>3^q) it applies the **closure identity**

    (2^j − 3^q) n = s(V) − 2^j d,   s(V) = remainder_from_parity(V),

to solve for the unique start `n = (s(V) − 2^j d)/(2^j − 3^q)` at each d, keeping it
only when `n≥3` is odd and its own parity word is exactly `V` (Terras
self-consistency). Survivors are checked against the **Rhin** (`|j log2−q log3|≥j^{−13.3}`)
and **Ellison** (`2^j−3^q>2.56^q/2`) lower bounds and the full **Baker reduction
chain** (`n≤ρ_V j^{13.3}`, `m≤H(j)`, `M≥2^{j/2R}−1`) of `length-bound.html §4d`.

## Result (R≤6, d≤10)

- **Outcome (a), unconditional:** R=1 is empty for every d (Theorem R1); d=0 is
  empty for every R (no nontrivial cycle — Steiner / Simons–de Weger).
- **Outcome (b), finite candidate list:** the *only* surviving slice is
  **(R=3, d=1)** = the near-cycle rotation family `{7, 9, 19, 25}`, all j=8, q=5
  — exactly the table in `length-bound.html §4a`.
- **Empty up to the cap:** every other (R,d) with R≤6, 1≤d≤10 has no shape
  surviving up to j≤27; completeness *beyond* the cap is conditional on the
  excursion bound `M≤m^β` (RT Conj. 6.2) — the honest Collatz wall of §I.2. In
  particular no d≥2 sequence has R≤6 (smallest paradoxical d=2 is n=165, R=7).

Self-tests cross-validate the shape enumeration against a direct orbit scan
(n≤2·10⁶), check the closure identity two ways (circuit sum vs. remainder
recursion), and pin the (R=3,d=1) family. The conditional uniform cutoff table
(17396 / 12867 / 10957) reproduces `length-bound.html §5`.

## Map to the Lean formalization (`RT/theorems.txt`, ns `RT`)

Groundwork for work package II.8.5 ("Formalize Part I"):

| Python | RT Lean |
|---|---|
| `IsParadoxical` predicate (C_j<1 ∧ T^j n ≥ n) | `RT.IsParadoxical j n` |
| q = odd-step count | `num_odd_steps j n` |
| s(V) = 2^j E_j (integer remainder) | `decomposition_correction` / `E` |
| closure algebra of the circuit sum | `decomposition_correction_add`, `E_shift_mul` |
| `H(j)`, `m≤H(j)` | `RT.H`, `m_le_H` |
| conditional cutoff / heuristic collision | `Conjecture62`, `heuristic_chain`, `theorem_5_3` |

The circuit decomposition / closure identity itself is not yet a Lean theorem;
`decomposition_correction_add` is the building block for it.
