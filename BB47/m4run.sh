#!/bin/bash
# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
# M4 (plan-1047) driver.  Usage: m4run.sh <digitdir> <outdir> [N]
set -eu
D=${1:?digitdir}; O=${2:?outdir}; N=${3:-1000000000}
mkdir -p "$D" "$O"
cd "$(dirname "$0")/.."
gen() { [ -s "$D/$3" ] || python3 BB47/m4digits.py "$1" "$2" "$N" "$D/$3"; }

for b in 2 3 10; do for c in sqrt2 sqrt3 phi; do gen $c $b $c-b$b.bin; done; done
gen rand 2 rand-b2.bin ; gen rand 10 rand-b10.bin
gen fib  2 fib-b2.bin
for P in 1000 1000000 100000000; do gen "planted:$P:sqrt2" 2 planted$P-b2.bin; done

run() { # file base nexact ncert tag
  [ -s "$O/$5.tsv" ] && return 0
  /usr/bin/time -v ./BB47/m4stats "$D/$1" "$2" "$3" "$4" "$5" 6 > "$O/$5.tsv" 2> "$O/$5.time"
  echo "done $5  $(grep -m1 'Maximum resident' "$O/$5.time")  $(grep -m1 'Elapsed' "$O/$5.time")"
}
for c in sqrt2 sqrt3 phi rand fib planted1000 planted1000000 planted100000000; do
  [ -s "$D/$c-b2.bin" ] && run $c-b2.bin 2 27 63 $c-b2
done
for c in sqrt2 sqrt3 phi;      do run $c-b3.bin  3 17 39 $c-b3;  done
for c in sqrt2 sqrt3 phi rand; do run $c-b10.bin 10 8 18 $c-b10; done
