#!/bin/sh
# Every generated file matches what its generator writes now
# (`generated-sources`): generators are Bend programs that print the file,
# run from the generated file's directory. Checks, never writes the files
# checked: a stale file fails, and regenerating it is the developer's
# step. Run by scripts/check.sh and by the pre-commit hook in .githooks/
# (with the other quick checks). Blend's generated samples are Blend's to
# check (blend/check_generated.sh, which its gate and hooks run).
#
#   scripts/check_generated.sh
set -u
cd "$(dirname "$0")/.." || exit 1
BEND=${BEND:-$(command -v bend || echo "$HOME/.bend/bin/bend")}
status=0

# one line each: the generator's kind and the directory it runs in; for
# `bend`, a Bend program printing a file, the file and its arguments
while read -r kind dir rest; do
  [ -n "$kind" ] || continue
  case $kind in
    bend)
      file=${rest%% *} args=${rest#* }
      # shellcheck disable=SC2086 # the arguments split as written
      if (cd "$dir" && $BEND $args | cmp -s - "$file"); then
        echo "$dir/$file: matches bend $args"
      else
        echo "$dir/$file differs from what bend $args writes: regenerate it (cd $dir && bend $args > $file)"
        status=1
      fi ;;
    *) echo "$dir: no generator of kind $kind"; status=1 ;;
  esac
done <<'EOF'
bend spike krules.bend tools/gen_krules.bend
EOF
exit "$status"
