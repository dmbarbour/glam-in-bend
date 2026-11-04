#!/bin/sh
# Runs Blend's executable, built first if stale (blend/build.sh); paths
# are taken from where it is run.
#
#   blend/run.sh read|objects|resolve FILE.blend
set -u
bin=$("$(dirname "$0")/build.sh") || exit 1
exec "$bin" "$@"
