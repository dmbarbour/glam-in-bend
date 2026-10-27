#!/bin/sh
# Runs a command under a memory and time cap, killing everything it started
# if either is passed. Use it for anything that might run away, such as
# reducing a net that may not normalize: an unbounded run once exhausted
# the machine's memory and crashed the session.
#
#   scripts/capped.sh MEGABYTES SECONDS command [args...]
#
# Where scripts/cgroup-delegate.sh has run, the command runs in a cgroup of
# its own under /sys/fs/cgroup/capped: the kernel holds it to the cap, with
# no swap, and kills the whole group past it. Elsewhere this polls the
# process group's resident memory every 0.1 s, which overshoots by whatever
# the command allocates between polls. Exits 137 when it kills, else with
# the command's status.
set -u
[ $# -ge 3 ] || { echo "usage: $0 MEGABYTES SECONDS command [args...]" >&2; exit 2; }
mb=$1; limit=$(( $2 * 10 )); shift 2
parent=/sys/fs/cgroup/capped
ticks=0

killed() {
  echo "capped.sh: killed after $((ticks / 10)) s, $1 (cap $mb MB, $((limit / 10)) s)" >&2
  exit 137
}

if grep -qw memory "$parent/cgroup.subtree_control" 2>/dev/null; then
  cg=$parent/run$$
  mkdir "$cg" || exit 1
  echo $(( mb * 1048576 )) > "$cg/memory.max"
  [ ! -f "$cg/memory.swap.max" ] || echo 0 > "$cg/memory.swap.max"
  echo 1 > "$cg/memory.oom.group"
  trap 'echo 1 > "$cg/cgroup.kill"' INT TERM HUP
  # The command enters the group before it runs, so all it forks is inside.
  sh -c 'echo $$ > "$1/cgroup.procs" && shift && exec "$@"' capped "$cg" "$@" &
  pid=$!
  while kill -0 "$pid" 2>/dev/null && [ "$ticks" -lt "$limit" ]; do
    sleep 0.1
    ticks=$((ticks + 1))
  done
  late=0
  kill -0 "$pid" 2>/dev/null && late=1
  echo 1 > "$cg/cgroup.kill"   # the command, or what it left running
  wait "$pid" 2>/dev/null
  status=$?
  oom=$(awk '$1 == "oom_kill" {print $2}' "$cg/memory.events")
  peak=$(( $(cat "$cg/memory.peak" 2>/dev/null || echo 0) / 1048576 ))
  # A cgroup can be removed only once empty, a moment after the kill.
  n=0
  until rmdir "$cg" 2>/dev/null || [ "$n" -ge 50 ]; do sleep 0.1; n=$((n + 1)); done
  [ "$late" = 0 ] || killed "out of time at $peak MB"
  [ "${oom:-0}" = 0 ] || killed "out of memory"
  exit "$status"
fi

setsid "$@" &
pid=$!
cap_kb=$(( mb * 1024 ))
while kill -0 "$pid" 2>/dev/null; do
  rss=$(ps -o rss= -g "$pid" 2>/dev/null | awk '{s += $1} END {print s + 0}')
  if [ "$rss" -gt "$cap_kb" ] || [ "$ticks" -ge "$limit" ]; then
    kill -9 -"$pid" 2>/dev/null
    wait "$pid" 2>/dev/null
    killed "at $((rss / 1024)) MB"
  fi
  sleep 0.1
  ticks=$((ticks + 1))
done
wait "$pid"
