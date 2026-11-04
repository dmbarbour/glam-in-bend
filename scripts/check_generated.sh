#!/bin/sh
# Every generated file matches what its generator writes now
# (`generated-sources`): generators are Bend programs that print the file,
# or Blend emitting a .blend file (blend/README.md), run from the generated
# file's directory. Checks, never writes: a stale file fails, and
# regenerating it is the developer's step. Run by scripts/check.sh and by
# the pre-commit hook in .githooks/ (with the other quick checks). Blend
# runs built (blend/build.sh): its build, 13 s, comes once for each
# version of its sources, the gate's first run usually.
#
#   scripts/check_generated.sh
set -u
cd "$(dirname "$0")/.." || exit 1
root=$PWD
BEND=${BEND:-$(command -v bend || echo "$HOME/.bend/bin/bend")}
status=0

# one line each: the directory, the generated file, the generator's kind
# (`bend`, a Bend program; `blend`, Blend's emission) and its arguments,
# relative to the directory
while read -r dir file kind args; do
  [ -n "$dir" ] || continue
  case $kind in
    bend) run="$BEND $args"; again="bend $args" ;;
    blend) run="$root/blend/run.sh emit $args"
      again="$(echo "$dir" | sed 's#[^/][^/]*#..#g')/blend/run.sh emit $args" ;;
    *) echo "$dir/$file: no generator of kind $kind"; status=1; continue ;;
  esac
  # shellcheck disable=SC2086 # the arguments split as written
  if (cd "$dir" && $run | cmp -s - "$file"); then
    echo "$dir/$file: matches $kind $args"
  else
    echo "$dir/$file differs from what $kind $args writes: regenerate it (cd $dir && $again > $file)"
    status=1
  fi
done <<'EOF'
spike krules.bend bend tools/gen_krules.bend
blend/samples family.bend blend family.blend
blend/samples nested.bend blend nested.blend
blend/samples override.bend blend override.blend
blend/samples prior.bend blend prior.blend
blend/samples sharing.bend blend sharing.blend
blend/samples choice.bend blend choice.blend
blend/samples types.bend blend types.blend
blend/samples imports.bend blend imports.blend
blend/samples/lib shapes.bend blend shapes.blend
EOF
exit "$status"
