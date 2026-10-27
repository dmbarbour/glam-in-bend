#!/bin/sh
# Runs a command under `perf stat`, then reports its user-space
# instructions and cycles on stderr. Instruction counts are stable to a
# few parts in a hundred million across runs, unlike times: record them
# beside timings. Compose with the cap:
#
#   scripts/capped.sh MB SECONDS scripts/count.sh command [args...]
#
# Exits with the command's status.
set -u
[ $# -ge 1 ] || { echo "usage: $0 command [args...]" >&2; exit 2; }
out=$(mktemp)
perf stat -x, -e instructions:u,cycles:u -o "$out" -- "$@"
status=$?
ins=$(awk -F, '$3 == "instructions:u" {print $1}' "$out")
cyc=$(awk -F, '$3 == "cycles:u" {print $1}' "$out")
rm -f "$out"
echo "count.sh: ${ins:-?} instructions, ${cyc:-?} cycles (user)" >&2
exit "$status"
