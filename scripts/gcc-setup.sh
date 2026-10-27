#!/bin/sh
# Builds GCC from the GNU release into /opt/gcc-16.2.0, checked by hash: a
# second C compiler for Bend's emitted C, as a point of reference beside
# clang (spike/tools/inline_build.sh). Debian 13 packages GCC 14, which
# cannot build that C (it needs `musttail`). C only, no bootstrap: a
# quarter to half an hour on 8 threads. Idempotent; run as root.
set -eu
V=16.2.0
SHA512=c51c30ca7422d0cbecf504b2e0f33c3aca31e0f90a76b65217f465163fa6fa17b3f5de39e145c47e5bab90ac0ce7fff3b03c8d553ae36e01faaea5a50f8648d1
PREFIX=/opt/gcc-$V
BUILD=/tmp/gcc-build-$V
if [ -x "$PREFIX/bin/gcc" ]; then
  "$PREFIX/bin/gcc" --version | head -n 1
  exit 0
fi
apt-get update && apt-get install -y libgmp-dev libmpfr-dev libmpc-dev
mkdir -p "$BUILD"
cd "$BUILD"
[ -f "gcc-$V.tar.xz" ] || curl -fsSL -o "gcc-$V.tar.xz" "https://ftp.gnu.org/gnu/gcc/gcc-$V/gcc-$V.tar.xz"
echo "$SHA512  gcc-$V.tar.xz" | sha512sum -c -
[ -d "gcc-$V" ] || tar xf "gcc-$V.tar.xz"
mkdir -p obj
cd obj
"../gcc-$V/configure" --prefix="$PREFIX" --enable-languages=c --disable-multilib \
  --disable-bootstrap --disable-libsanitizer --disable-libgomp --disable-nls
make -j"$(nproc)"
make install
cd /
rm -rf /tmp/gcc-build-16.2.0
"$PREFIX/bin/gcc" --version | head -n 1
