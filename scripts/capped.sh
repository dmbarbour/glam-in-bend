#!/bin/sh
# Runs a command under a memory and time cap, killing its whole process
# group if either is passed. Use it for anything that might run away, such
# as reducing a net that may not normalize: an unbounded run once exhausted
# the machine's memory and crashed the session.
#
#   scripts/capped.sh MEGABYTES SECONDS command [args...]
#
# Polls the group's total resident memory every 0.1 s; exits 137 when it
# kills, else with the command's status.
set -u
[ $# -ge 3 ] || { echo "usage: $0 MEGABYTES SECONDS command [args...]" >&2; exit 2; }
cap_kb=$(( $1 * 1024 )); limit=$(( $2 * 10 )); shift 2

setsid "$@" &
pid=$!
ticks=0
while kill -0 "$pid" 2>/dev/null; do
  rss=$(ps -o rss= -g "$pid" 2>/dev/null | awk '{s += $1} END {print s + 0}')
  if [ "$rss" -gt "$cap_kb" ] || [ "$ticks" -ge "$limit" ]; then
    kill -9 -"$pid" 2>/dev/null
    wait "$pid" 2>/dev/null
    echo "capped.sh: killed after $((ticks / 10)) s at $((rss / 1024)) MB (cap $((cap_kb / 1024)) MB, $((limit / 10)) s)" >&2
    exit 137
  fi
  sleep 0.1
  ticks=$((ticks + 1))
done
wait "$pid"
