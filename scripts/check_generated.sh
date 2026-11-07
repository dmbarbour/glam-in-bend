#!/bin/sh
# Every generated file matches what its generator writes now
# (`generated-sources`): generators are Bend programs that print the file,
# run from the generated file's directory. Checks, never writes the files
# checked: a stale file fails, and regenerating it is the developer's
# step. Run by scripts/check.sh and by the pre-commit hook in .githooks/
# (with the other quick checks). A `.bend` Blend writes from a `.blend`
# here is checked by Blend itself, `deps --bytes` over the module's tree
# (blend-stamps), the Blend glam records: the index's pointer, what a
# commit records; the submodule's checkout where it is that commit, else
# a worktree of it under results/blend-at/ (out of git), built once, so
# that a Blend checked out ahead of the pointer, its version stamp moved,
# leaves glam's commits alone until the pointer moves. Blend's generated
# samples are Blend's to check (blend/check_generated.sh, which its gate
# and hooks run).
#
#   scripts/check_generated.sh
set -u
# no update check: Bend's notice of a newer release would print beside
# what this reads, as scripts/check.sh has it
export BEND_NO_TELEMETRY=1
cd "$(dirname "$0")/.." || exit 1
root=$PWD
BEND=${BEND:-$(command -v bend || echo "$HOME/.bend/bin/bend")}
status=0

# the Blend glam records, and where it is checked out
rec=$(git ls-files -s blend | awk '{print $2}')
have=$(git -C blend rev-parse HEAD 2>/dev/null)
blend_dir=$root/blend
if [ -n "$rec" ] && [ "$rec" != "$have" ]; then
  blend_dir=$root/results/blend-at/$rec
  [ -d "$blend_dir" ] || git -C blend worktree add -q --detach "$blend_dir" "$rec" >/dev/null 2>&1 ||
    { echo "blend: no checkout of the Blend glam records, $rec"; status=1; }
  echo "blend: the Blend glam records, $(echo "$rec" | cut -c1-7), checks its modules, not the checkout's, $(echo "$have" | cut -c1-7)"
fi
# built first, its note on standard error, so that deps' lines alone are read
BEND=$BEND "$blend_dir/build.sh" >/dev/null || { echo "blend: the build at $blend_dir fails"; status=1; }

# one line each: the generator's kind and the directory it runs in; for
# `bend`, a Bend program printing a file, the file and its arguments; for
# `blend`, the module whose tree Blend writes
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
    blend)
      if got=$(cd "$dir" && BEND=$BEND "$blend_dir/run.sh" deps --bytes "$rest" 2>&1); then
        echo "$got" | while read -r state mod; do echo "$dir/${mod%.blend}.bend: matches blend"; done
      else
        echo "$got"
        echo "$dir/$rest's tree differs from what blend writes: regenerate it (cd $dir && blend emit --force $rest)"
        status=1
      fi ;;
    *) echo "$dir: no generator of kind $kind"; status=1 ;;
  esac
done <<'EOF'
bend spike krules.bend tools/gen_krules.bend
blend spike kdemand.blend
EOF
exit "$status"
