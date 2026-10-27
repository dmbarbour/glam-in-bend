#!/bin/sh
# Sets up a dev container for glam-in-bend: Bend at a pinned release,
# checked by hash, on PATH; `clang` for native builds; `perf` for
# instruction counts (scripts/count.sh); the commit-msg hook.
# Idempotent. Run as root from the repository root, as the devcontainer's
# postCreateCommand; scripts/cgroup-delegate.sh is its postStartCommand.
set -eu
BEND_VERSION=2.0.39
BEND_SHA256=6cf462fd8f70b094a4950ebb709a9c4ffd8f1d1189d9cedf1fd63cd5d041c7ab
BEND_HOME=$HOME/.bend
TARBALL=/tmp/bend-$BEND_VERSION-linux-x64.tar.gz

# Bend: the release tarball holds bend/{bin,bend2,guide}, which the binary
# expects under ~/.bend.
if [ "$("$BEND_HOME/bin/bend" version 2>/dev/null)" != "bend $BEND_VERSION" ]; then
  curl -fsSL -o "$TARBALL" \
    "https://github.com/bendlang/bend/releases/download/v$BEND_VERSION/bend-$BEND_VERSION-linux-x64.tar.gz"
  echo "$BEND_SHA256  $TARBALL" | sha256sum -c -
  mkdir -p "$BEND_HOME"
  # The tarball carries macOS extended headers that GNU tar warns about.
  tar xzf "$TARBALL" -C "$BEND_HOME" --strip-components=1 --warning=no-unknown-keyword
  rm -f "$TARBALL"
fi
line='export PATH="$HOME/.bend/bin:$PATH"'
grep -qxF "$line" "$HOME/.bashrc" 2>/dev/null || echo "$line" >> "$HOME/.bashrc"

# clang: Bend's native builds call `clang`; the C/C++ feature installs only
# a versioned clang-N.
if ! command -v clang >/dev/null 2>&1; then
  newest=$(ls /usr/bin/clang-[0-9]* 2>/dev/null | sort -V | tail -n 1)
  [ -n "$newest" ] || { echo "dev-setup: no /usr/bin/clang-N to link" >&2; exit 1; }
  update-alternatives --install /usr/bin/clang clang "$newest" 100
fi

# perf: Debian packages it as linux-perf
if ! command -v perf >/dev/null 2>&1; then
  apt-get update && apt-get install -y linux-perf
fi

git config core.hooksPath .githooks
"$BEND_HOME/bin/bend" version
clang --version | head -n 1
