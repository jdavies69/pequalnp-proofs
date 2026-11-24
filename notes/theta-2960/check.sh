#!/bin/sh
set -eu
src=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$(git -C "$src" rev-parse --show-toplevel)
cd "$repo/lean"
lake build PEqualNP.Defs
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
lake env sh -eu -c '
  src=$1
  out=$2
  shift 2
  export LEAN_PATH="$out:$LEAN_PATH"
  for name do
    lean -j1 -DElab.async=false -R "$src" -o "$out/$name.olean" "$src/$name.lean"
  done
' sh "$src" "$out" ThetaTrace ThetaRows ThetaSearch ThetaFinite ThetaUpper ThetaMilestone
