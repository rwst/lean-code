import Mathlib

open Finset Fintype Nat

/--
A tiling of a 2 times `n` rectangle into 2 times 1 dominoes
is a set of `n` pairs of tiles `(t₁, t₂)` (dominoes), with each tile a pair
of natural numbers `t = (x, y)`, such that `x < n` and `y ∈ {0, 1}`. Additional
conditions are that `t₁` and `t₂` are adjacent, and none of the
tiles occurs more than once.
-/

structure Tile (n : ℕ) where
  x : ℕ
  y : ℕ
  x_range : x < n
  y_zero_one : y = 0 ∨ y = 1

def adjacent (t₁ t₂ : Tile n) :=
  (((t₁.x : ℤ) - t₂.x).natAbs = 1 ∧ t₁.y = t₂.y) ∨ (t₁.x = t₂.x ∧ t₁.y ≠ t₂.y)

structure Domino (n : ℕ) where
  t₁ : Tile n
  t₂ : Tile n
  nodup : t₁ ≠ t₂
  adj : adjacent t₁ t₂

def isHorizontal (d : Domino n) := d.t₁.y = d.t₂.y
def isVertical (d : Domino n) := d.t₁.x = d.t₂.x

structure DominoTilingOf2xn (n : ℕ) where
  parts : Finset (Domino n)
  nodup : ∀ d₁ d₂ : Domino n, d₁ ≠ d₂ ∧
      d₁.t₁ ≠ d₂.t₁ ∧ d₁.t₁ ≠ d₂.t₂ ∧ d₁.t₂ ≠ d₂.t₁ ∧ d₁.t₂ ≠ d₂.t₂
  tiled : ∀ t : Tile n, ∃ d : Domino n, d ∈ parts ∧ (d.t₁ = t ∨ d.t₂ = t)
  dcard : parts.card = n

lemma horizontal_dominoes_match :
    ∀ n : ℕ, ∀ s : DominoTilingOf2xn n, ∀ d : Domino n,
    d ∈ s.parts ∧ isHorizontal d → ∃ d' : Domino n, d' ∈ s.parts ∧ d ≠ d' ∧
    ((d.t₁.x = d'.t₁.x) ∧ (d.t₂.x = d'.t₂.x)) ∨ ((d.t₁.x = d'.t₂.x) ∧ (d.t₂.x = d'.t₁.x)) := by
  sorry
