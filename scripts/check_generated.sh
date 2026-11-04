#!/bin/sh
# Every generated file matches what its generator writes now
# (`generated-sources`): generators are Bend programs that print the file,
# or Blend emitting a .blend file (blend/README.md), run from the generated
# file's directory. Checks, never writes the files checked: a stale file
# fails, and regenerating it is the developer's step. Run by
# scripts/check.sh and by the pre-commit hook in .githooks/ (with the
# other quick checks). Blend runs built (blend/build.sh): its build, 13 s,
# comes once for each version of its sources, the gate's first run
# usually.
#
#   scripts/check_generated.sh
set -u
cd "$(dirname "$0")/.." || exit 1
root=$PWD
BEND=${BEND:-$(command -v bend || echo "$HOME/.bend/bin/bend")}
status=0

# Blend's emission of one module, all of it at once: the code, and the
# laws and proofs beside it where the module has any
# (`blend-proofs-beside-code`), written into results/ (out of git, each
# file overwritten, none removed) and compared with the files in dir;
# a laws or proofs file the emission no longer writes is stale
blend_check() {
  dir=$1 file=$2 src=$3
  out=$root/results/blend/generated/$dir
  again="(cd $dir && $(echo "$dir" | sed 's#[^/][^/]*#..#g')/blend/run.sh emit $src)"
  mkdir -p "$out" || return 1
  if ! wrote=$(cd "$dir" && "$root/blend/run.sh" emit "$src" "$out"); then
    echo "$dir/$file: blend emit $src fails"
    return 1
  fi
  ok=0
  names=" "
  for p in $wrote; do
    name=${p##*/}
    names="$names$name "
    if cmp -s "$p" "$dir/$name"; then
      echo "$dir/$name: matches blend $src"
    else
      echo "$dir/$name differs from what blend $src writes: regenerate it $again"
      ok=1
    fi
  done
  for name in "${file%.bend}_LAWS.bend" "${file%.bend}_PROOF.bend"; do
    case $names in
      *" $name "*) ;;
      *) [ ! -e "$dir/$name" ] || { echo "$dir/$name: blend $src writes it no longer: remove it"; ok=1; } ;;
    esac
  done
  return "$ok"
}

# one line each: the directory, the generated file, the generator's kind
# (`bend`, a Bend program printing the file; `blend`, Blend's emission,
# the file its code) and its arguments, relative to the directory
while read -r dir file kind args; do
  [ -n "$dir" ] || continue
  case $kind in
    bend)
      # shellcheck disable=SC2086 # the arguments split as written
      if (cd "$dir" && $BEND $args | cmp -s - "$file"); then
        echo "$dir/$file: matches bend $args"
      else
        echo "$dir/$file differs from what bend $args writes: regenerate it (cd $dir && bend $args > $file)"
        status=1
      fi ;;
    blend) blend_check "$dir" "$file" "$args" || status=1 ;;
    *) echo "$dir/$file: no generator of kind $kind"; status=1 ;;
  esac
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
blend/samples family-nested.bend blend family-nested.blend
blend/samples nested-reach.bend blend nested-reach.blend
blend/samples laws.bend blend laws.blend
blend/samples laws-imported.bend blend laws-imported.blend
blend/samples/lib shapes.bend blend shapes.blend
blend/samples/lib adds.bend blend adds.blend
EOF
exit "$status"
