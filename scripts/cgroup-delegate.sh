#!/bin/sh
# Lets scripts/capped.sh cap a run's memory through the kernel's memory
# controller rather than by polling. Inside a container the cgroup root
# holds processes, so enabling a controller for child groups fails (EBUSY)
# until they move to a leaf: this moves them to /sys/fs/cgroup/init,
# enables memory and pids for children, and makes /sys/fs/cgroup/capped,
# the parent of capped runs. Idempotent. Needs root and a writable cgroup2
# mount (a privileged container); run at every container start, as the
# devcontainer's postStartCommand.
set -eu
cg=/sys/fs/cgroup
[ -f $cg/cgroup.controllers ] || { echo "cgroup-delegate: no cgroup2 at $cg" >&2; exit 1; }

if ! grep -qw memory $cg/cgroup.subtree_control; then
  mkdir -p $cg/init
  tries=0
  # Processes may arrive in the root while others move, so retry.
  until echo "+memory +pids" > $cg/cgroup.subtree_control 2>/dev/null; do
    tries=$((tries + 1))
    [ "$tries" -le 20 ] || { echo "cgroup-delegate: the root cgroup stays busy" >&2; exit 1; }
    while read -r pid; do
      echo "$pid" > $cg/init/cgroup.procs 2>/dev/null || :
    done < $cg/cgroup.procs
  done
fi

mkdir -p $cg/capped
grep -qw memory $cg/capped/cgroup.subtree_control \
  || echo "+memory +pids" > $cg/capped/cgroup.subtree_control
echo "cgroup-delegate: $cg/capped takes memory caps"
