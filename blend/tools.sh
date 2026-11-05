# Sourced by Blend's scripts: TOOLS, where the tools Blend shares with the
# repository it grew in are (capped.sh, count.sh, results.py, kept.py,
# one_law.py, check_docs.py, check_laws.py): its own scripts/ once it has
# one, as it will when it becomes a repository of its own
# (`blend-home.arrange`), else its parent's. Needs BLEND_ROOT, Blend's
# directory.
if [ -d "$BLEND_ROOT/scripts" ]; then
  TOOLS=$BLEND_ROOT/scripts
else
  TOOLS=$(cd "$BLEND_ROOT/.." && pwd)/scripts
fi
