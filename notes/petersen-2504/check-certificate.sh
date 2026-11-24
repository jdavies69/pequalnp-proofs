#!/bin/sh
set -eu
src=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$(git -C "$src" rev-parse --show-toplevel)
cd "$repo/lean"
lake build PEqualNP.Outside.L_meta_1667
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
lake env sh -eu -c '
  src=$1
  build=$2
  export LEAN_PATH="$build:$LEAN_PATH"
  check() {
    name=$1
    lean -j2 -R "$src" -o "$build/$name.olean" "$src/$name.lean"
  }
  check DeskForestData
  check ForestBridge
  for file in "$src"/Segment*.lean; do
    name=${file##*/}
    check "${name%.lean}"
  done
  check PetersenComplete
' sh "$src" "$build"
