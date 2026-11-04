#!/bin/sh
# Runs Blend's executable, built first if stale (blend/build.sh); paths
# are taken from where it is run.
#
#   blend/run.sh read|objects|resolve FILE.blend   prints a stage
#   blend/run.sh emit FILE.blend [DIR]             writes the module's
#     files into DIR, else beside FILE: FILE's .bend, and its _LAWS.bend
#     and _PROOF.bend where it has laws; prints each path written
set -u
bin=$("$(dirname "$0")/build.sh") || exit 1
exec "$bin" "$@"
