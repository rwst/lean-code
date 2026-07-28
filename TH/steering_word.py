#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# Released under CC0 1.0 Universal (public-domain dedication).
# See https://creativecommons.org/publicdomain/zero/1.0/
"""
Print the (3/2)^n steering word t_n and parity word b_n for n = 1..100.

Mirrors the definitions in TH/Basic.lean:

    m(n) = round((3/2)^n)      -- nearest integer to (3/2)^n
    t(n) = 2*m(n+1) - 3*m(n)   -- steering letter, always in {-2, ..., 2}
    b(n) = m(n) % 2            -- parity letter; the mod-2 reduction of the
                               --   steering word (b(n) = t(n) % 2, TH.t_emod_two)

Here `round` is Mathlib's `round x = floor(x + 1/2)` (round-half-UP: ties go up),
NOT Python's built-in `round`, which is banker's rounding (round-half-to-even).
Everything is exact integer arithmetic, so the values are correct all the way to
n = 100 (where (3/2)^100 has ~18 digits and floating point would be useless):

    m(n) = floor(3^n / 2^n + 1/2) = (2*3^n + 2^n) // 2^(n+1).

Sanity check (TH.t_sanity):  t_0, ..., t_4 = 1, -2, 0, 1, 1.
"""


def m(n: int) -> int:
    """Nearest integer to (3/2)^n, ties rounded up (matches Mathlib `round`)."""
    return (2 * 3**n + 2**n) // 2 ** (n + 1)


def t(n: int) -> int:
    """The steering letter t_n = 2*m(n+1) - 3*m(n)."""
    return 2 * m(n + 1) - 3 * m(n)


def b(n: int) -> int:
    """The parity letter b_n = m(n) % 2 (in {0, 1}); equals t(n) % 2."""
    return m(n) % 2


if __name__ == "__main__":
    ns = range(1, 150)
    print("t:", ", ".join(str(t(n)) for n in ns))
    print("b:", ", ".join(str(b(n)) for n in ns))
