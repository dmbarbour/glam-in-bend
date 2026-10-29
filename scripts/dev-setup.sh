#!/bin/sh
# Sets up a dev container for glam-in-bend: Bend at a pinned release,
# checked by hash, on PATH; `clang` for native builds, with the LLVM
# profile tools of its version for profile-guided builds
# (spike/tools/inline_build.sh); `perf` for instruction counts
# (scripts/count.sh); Node, to run Bend's JavaScript output; Lean at a
# pinned release, checked by hash, for `bend --verdict`; GCC 16, built
# from source (scripts/gcc-setup.sh); the commit hooks.
# Idempotent. Run as root from the repository root, as the devcontainer's
# postCreateCommand; scripts/cgroup-delegate.sh is its postStartCommand.
set -eu
BEND_VERSION=2.0.39
BEND_SHA256=6cf462fd8f70b094a4950ebb709a9c4ffd8f1d1189d9cedf1fd63cd5d041c7ab
BEND_HOME=$HOME/.bend
TARBALL=/tmp/bend-$BEND_VERSION-linux-x64.tar.gz
LEAN_VERSION=4.34.0
LEAN_SHA256=caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b
LEAN_HOME=$HOME/.lean
LEAN_TARBALL=/tmp/lean-$LEAN_VERSION-linux.tar.zst

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

# profile-guided builds: llvm-profdata and the profile runtime, of clang's
# own version
clang_major=$(clang --version | sed -n 's/.*clang version \([0-9]*\).*/\1/p' | head -n 1)
if ! dpkg -s "llvm-$clang_major" "libclang-rt-$clang_major-dev" >/dev/null 2>&1; then
  apt-get update && apt-get install -y "llvm-$clang_major" "libclang-rt-$clang_major-dev"
fi

# perf: Debian packages it as linux-perf
if ! command -v perf >/dev/null 2>&1; then
  apt-get update && apt-get install -y linux-perf
fi

# Node, for `bend x.bend -o x.js`
if ! command -v node >/dev/null 2>&1; then
  apt-get update && apt-get install -y nodejs
fi

# pdftotext, to read papers fetched as PDF
if ! command -v pdftotext >/dev/null 2>&1; then
  apt-get update && apt-get install -y poppler-utils
fi

# Lean, for `bend PROOF.bend --verdict`: the proofs rechecked by BendTT's
# kernel (~/.bend/bend2/bendtt.lean), which has a proof in Lean that no
# def it accepts has type Empty; Bend builds it with Lean of this version.
# The release tarball, about 580 MB, is zstd-compressed.
if [ "$("$LEAN_HOME/bin/lean" --version 2>/dev/null | sed -n 's/^Lean (version \([0-9.]*\).*/\1/p')" != "$LEAN_VERSION" ]; then
  command -v zstd >/dev/null 2>&1 || { apt-get update && apt-get install -y zstd; }
  curl -fsSL -o "$LEAN_TARBALL" \
    "https://github.com/leanprover/lean4/releases/download/v$LEAN_VERSION/lean-$LEAN_VERSION-linux.tar.zst"
  echo "$LEAN_SHA256  $LEAN_TARBALL" | sha256sum -c -
  mkdir -p "$LEAN_HOME"
  tar --zstd -xf "$LEAN_TARBALL" -C "$LEAN_HOME" --strip-components=1
  rm -f "$LEAN_TARBALL"
fi
# last on the path: Lean's toolchain carries a clang of its own, without
# the system's headers, which Bend's native builds must not find first
line='export PATH="$PATH:$HOME/.lean/bin"'
grep -qxF "$line" "$HOME/.bashrc" 2>/dev/null || echo "$line" >> "$HOME/.bashrc"

# GCC 16 from source, a second compiler for reference (slow the first time)
sh scripts/gcc-setup.sh

git config core.hooksPath .githooks
"$BEND_HOME/bin/bend" version
"$LEAN_HOME/bin/lean" --version
clang --version | head -n 1
node --version
