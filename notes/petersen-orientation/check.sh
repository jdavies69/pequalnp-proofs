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
  shift 2
  export LEAN_PATH="$build:$LEAN_PATH"
  for name do
    lean -j1 -DElab.async=false -R "$src" -o "$build/$name.olean" "$src/$name.lean"
  done
' sh "$src" "$build" Core Verify Stages FastStages ReadOnce ReadMask ReadFold Sym SymCheck ReadSearch Positive PosMask SignedTree SharedTree ModuleCut Partitions FlexMarks SignedMask OrbitHit Cheap LocalAtlas Grant OrientationCut OrientationExample ModuleCertificate TopologyExample NearExample TightCertificate AdaptiveForest
