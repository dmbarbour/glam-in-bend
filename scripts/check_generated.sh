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

# Blend's emission of a directory's modules, all of it at once: each
# module's code, and its laws and proofs beside it where it has any
# (`blend-proofs-beside-code`), written into blend/results/ (out of git, each
# file overwritten, none removed) and compared with the files in dir; a
# laws or proofs file the emission no longer writes is stale
blend_check() {
  dir=$1
  shift
  out=$root/blend/results/generated/$dir
  again="(cd $dir && $(echo "$dir" | sed 's#[^/][^/]*#..#g')/blend/run.sh emit $*)"
  mkdir -p "$out" || return 1
  if ! wrote=$(cd "$dir" && "$root/blend/run.sh" emit "$@" "$out"); then
    echo "$dir: blend emit $* fails"
    return 1
  fi
  ok=0
  names=" "
  for p in $wrote; do
    name=${p##*/}
    names="$names$name "
    if cmp -s "$p" "$dir/$name"; then
      echo "$dir/$name: matches blend"
    else
      echo "$dir/$name differs from what blend writes: regenerate it $again"
      ok=1
    fi
  done
  for src in "$@"; do
    for name in "${src%.blend}_LAWS.bend" "${src%.blend}_PROOF.bend"; do
      case $names in
        *" $name "*) ;;
        *) [ ! -e "$dir/$name" ] || { echo "$dir/$name: blend writes it no longer: remove it"; ok=1; } ;;
      esac
    done
  done
  return "$ok"
}

# one line each: the generator's kind and the directory it runs in; for
# `bend`, a Bend program printing a file, the file and its arguments; for
# `blend`, Blend's emission, the directory's modules
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
    # shellcheck disable=SC2086 # the modules split as written
    blend) blend_check "$dir" $rest || status=1 ;;
    *) echo "$dir: no generator of kind $kind"; status=1 ;;
  esac
done <<'EOF'
bend spike krules.bend tools/gen_krules.bend
blend blend/samples family.blend nested.blend override.blend prior.blend sharing.blend choice.blend types.blend imports.blend family-nested.blend nested-reach.blend laws.blend laws-imported.blend declares.blend templates.blend
blend blend/samples/lib shapes.blend adds.blend
EOF
exit "$status"
