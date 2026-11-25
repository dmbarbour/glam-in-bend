#!/usr/bin/env python3
"""The memory free to this process's runs, in MB: the least of the host's
MemAvailable and, at every level of the cgroup this process is in up to
the root, that level's limit less what it holds now, the inactive file
cache, which the kernel reclaims, not counted as held.

Inside a container /proc/meminfo is the host's: the container's own
limit (`--memory`, .devcontainer/devcontainer.json) is its cgroup's
memory.max, which a gate sized by MemAvailable alone once overran, the
container killed with the session in it (2026-11-25).

    python3 -I scripts/mem_avail.py          prints the MB free
    python3 -I scripts/mem_avail.py EACH     prints how many runs of EACH
                                             MB fit, at least one

Imported, avail_mb() gives the same number.
"""
import os
import sys

ROOT = "/sys/fs/cgroup"


def meminfo_mb():
    try:
        with open("/proc/meminfo") as f:
            for line in f:
                if line.startswith("MemAvailable:"):
                    return int(line.split()[1]) // 1024
    except OSError:
        pass
    return None


def cgroup_free_mb():
    """the least of limit less use over this process's cgroup and its
    ancestors (cgroup v2), or None where none has a limit"""
    try:
        with open("/proc/self/cgroup") as f:
            path = next((l.split(":", 2)[2].strip() for l in f if l.startswith("0::")), None)
    except OSError:
        return None
    if path is None:
        return None
    least = None
    d = os.path.normpath(ROOT + "/" + path)
    while True:
        try:
            with open(d + "/memory.max") as f:
                mx = f.read().strip()
            with open(d + "/memory.current") as f:
                cur = int(f.read().strip())
            # the file cache not lately used the kernel reclaims under
            # pressure: free for a run, as docker's own figures count it
            try:
                with open(d + "/memory.stat") as f:
                    for line in f:
                        if line.startswith("inactive_file "):
                            cur -= int(line.split()[1])
            except OSError:
                pass
            if mx != "max":
                free = max(0, int(mx) - cur) // 1048576
                least = free if least is None else min(least, free)
        except (OSError, ValueError):
            pass
        if d == ROOT or not d.startswith(ROOT):
            break
        d = os.path.dirname(d)
    return least


def avail_mb():
    found = [m for m in (meminfo_mb(), cgroup_free_mb()) if m is not None]
    return min(found) if found else 0


if __name__ == "__main__":
    mb = avail_mb()
    if len(sys.argv) > 1:
        print(max(1, mb // max(1, int(sys.argv[1]))))
    else:
        print(mb)
