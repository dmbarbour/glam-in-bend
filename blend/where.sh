#!/bin/sh
# The .blend line an emitted .bend line comes from, for Bend's errors on
# emitted code: the nearest marker above it (`# blend: FILE:LINE`, before
# each definition) names its definition's line, and each line of the
# definition after it is the source's next (README.md).
#
#   where.sh FILE.bend LINE    prints FILE.blend:LINE
set -u
[ $# -eq 2 ] || { echo "usage: where.sh FILE.bend LINE" >&2; exit 2; }
awk -v want="$2" '
  NR > want + 0 { exit }
  /^# blend: / { m = substr($0, 10); i = match(m, /:[0-9]+$/); file = substr(m, 1, i - 1); src = substr(m, i + 1); at = NR }
  END {
    if (at == "") { print "blend: no marker at or above line " want > "/dev/stderr"; exit 1 }
    k = want - at - 1; if (k < 0) k = 0
    print file ":" (src + k)
  }' "$1"
