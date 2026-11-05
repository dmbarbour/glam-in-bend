#!/bin/sh
# Blend's generated files match what Blend writes now (glam-in-bend's
# `generated-sources`): a sample directory's modules emitted all at once,
# each module's code, and its laws and proofs beside it where it has any
# (`blend-proofs-beside-code`), written into results/generated (out of
# git, each file overwritten, none removed) and compared with the files
# beside the samples; a laws or proofs file the emission no longer writes
# is stale. Checks, never writes the files checked: a stale file fails,
# and regenerating it is the developer's step. Run by Blend's gate
# (check.sh) and by glam-in-bend's pre-commit hook. Blend runs built
# (build.sh): its build, 13 s, comes once for each version of its
# sources.
#
#   check_generated.sh
set -u
cd "$(dirname "$0")" || exit 1
root=$PWD
status=0

# one directory's modules, emitted all at once and compared
blend_check() {
  dir=$1
  shift
  out=$root/results/generated/$dir
  again="(cd $dir && $(echo "$dir" | sed 's#[^/][^/]*#..#g')/run.sh emit $*)"
  mkdir -p "$out" || return 1
  if ! wrote=$(cd "$dir" && "$root/run.sh" emit "$@" "$out"); then
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

# one line each: a directory and its modules
while read -r dir rest; do
  [ -n "$dir" ] || continue
  # shellcheck disable=SC2086 # the modules split as written
  blend_check "$dir" $rest || status=1
done <<'LIST'
samples family.blend nested.blend override.blend prior.blend sharing.blend choice.blend types.blend imports.blend family-nested.blend nested-reach.blend laws.blend laws-imported.blend declares.blend templates.blend
samples/lib shapes.blend adds.blend
LIST
exit "$status"
