#!/bin/sh
# Every generated file matches what its generator writes now
# (`generated-sources`): generators are Bend programs that print the file,
# run from the generated file's directory. Checks, never writes: a stale
# file fails, and regenerating it is the developer's step. Run by
# scripts/check.sh and by the pre-commit hook in .githooks/.
#
#   scripts/check_generated.sh
set -u
cd "$(dirname "$0")/.." || exit 1
BEND=${BEND:-$(command -v bend || echo "$HOME/.bend/bin/bend")}
status=0

# one line each: the directory, the generated file, the generator, both
# relative to the directory
while read -r dir file gen; do
  [ -n "$dir" ] || continue
  if (cd "$dir" && "$BEND" "$gen" | cmp -s - "$file"); then
    echo "$dir/$file: matches $dir/$gen"
  else
    echo "$dir/$file differs from what $dir/$gen writes: regenerate it (cd $dir && bend $gen > $file)"
    status=1
  fi
done <<'EOF'
spike krules.bend tools/gen_krules.bend
EOF
exit "$status"
