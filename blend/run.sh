#!/bin/sh
# Runs Blend's executable, built first if stale (blend/build.sh); paths
# are taken from where it is run.
#
#   blend/run.sh read|objects|resolve FILE.blend   prints a stage
#   blend/run.sh emit FILE.blend... [DIR]          writes each module's
#     files beside it, or into DIR: its .bend, and its _LAWS.bend and
#     _PROOF.bend where it has laws; prints each path written, or the
#     errors of any, writing none
set -u
bin=$("$(dirname "$0")/build.sh") || exit 1
exec "$bin" "$@"
