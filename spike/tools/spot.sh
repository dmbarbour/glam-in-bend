#!/bin/sh
# A spot check of the kernel's instructions, for development
# (heap-strategies.measure.spot): spike/tools/count_builds.sh with the
# default and forced-inline builds alone, nothing trained, the erasure
# modes counted too, at k 18 so that it compares with every count in the
# store. About a minute: the C emitted once, both builds compiled side by
# side. Merges still take the four builds.
#
#   [BASE=RUN] spike/tools/spot.sh OUT [NOTE]
set -eu
[ $# -ge 1 ] || { echo "usage: $0 OUT [NOTE]" >&2; exit 2; }
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
BUILDS="default ai" EV=1 exec "$ROOT/spike/tools/count_builds.sh" "$1" 18 "spot: ${2:-}"
