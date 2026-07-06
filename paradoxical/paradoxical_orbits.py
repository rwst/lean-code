#!/usr/bin/env python3
"""
Print all orbits of paradoxical Collatz sequences for start values in a given range.

Following Rozier & Terracol, arXiv:2502.00948v5, a finite Collatz sequence
n, T(n), ..., T^j(n) is paradoxical (for n > 2) when
  (i)  C_j(n) = 3^q / 2^j < 1  (q = number of odd terms among the first j iterates)
  (ii) T^j(n) >= n.

The map T is the accelerated Collatz map:
  T(n) = (3n + 1) / 2  if n is odd
  T(n) = n / 2         if n is even
"""

import argparse
import math
import sys


def T(n: int) -> int:
    """Accelerated Collatz map."""
    if n & 1:
        return (3 * n + 1) >> 1
    return n >> 1


def find_paradoxical_orbits(start: int, end: int, max_j: int):
    """
    Yield all paradoxical orbits whose starting value n satisfies
    start <= n <= end and whose length j is at most max_j.

    Each yielded item is a tuple (n, j, q, coefficient, orbit).
    """
    for n in range(start, end + 1):
        if n <= 2:
            # The trivial cycle (1, 2) is excluded from the definition.
            continue

        current = n
        q = 0
        pow3_q = 1
        pow2_j = 1
        orbit = [n]

        for j in range(1, max_j + 1):
            if current & 1:
                q += 1
                pow3_q *= 3
            current = T(current)
            orbit.append(current)
            pow2_j *= 2

            # Condition (i): coefficient C_j(n) = 3^q / 2^j < 1
            if pow3_q >= pow2_j:
                continue

            # Condition (ii): T^j(n) >= n
            if current < n:
                continue

            coefficient = pow3_q / pow2_j
            yield n, j, q, coefficient, list(orbit)

            # Once we reach the trivial cycle we can stop this n:
            # subsequent iterates just alternate 1, 2, 1, 2, ...
            # and can never be >= n > 2.
            if current == 1:
                break


def main():
    parser = argparse.ArgumentParser(
        description="Print all orbits of paradoxical Collatz sequences for start values in [--start, --end]."
    )
    parser.add_argument(
        "--start",
        type=int,
        required=True,
        help="First start value to test (inclusive).",
    )
    parser.add_argument(
        "--end",
        type=int,
        required=True,
        help="Last start value to test (inclusive).",
    )
    parser.add_argument(
        "--max-j",
        type=int,
        default=1000,
        help="Maximum number of iterations j to test for each start value (default: 1000).",
    )
    args = parser.parse_args()

    if args.start > args.end:
        print("Error: --start must be less than or equal to --end.", file=sys.stderr)
        sys.exit(1)
    if args.max_j < 1:
        print("Error: --max-j must be positive.", file=sys.stderr)
        sys.exit(1)

    count = 0
    for n, j, q, coefficient, orbit in find_paradoxical_orbits(
        args.start, args.end, args.max_j
    ):
        count += 1
        print(f"n={n}, j={j}, q={q}, C={coefficient:.6f}")
        print(" -> ".join(str(x) for x in orbit))
        print()

    print(f"Total paradoxical orbits found: {count}")


if __name__ == "__main__":
    main()
