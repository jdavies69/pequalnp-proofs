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
    dir=$1
    name=$2
    lean -j1 -DElab.async=false -R "$dir" -o "$build/$name.olean" "$dir/$name.lean"
  }
  dir="$src/../petersen-orientation"
  for m in Core Verify Stages FastStages ReadOnce ReadMask ReadFold Sym SymCheck ReadSearch Positive PosMask SignedTree SharedTree ModuleCut Partitions FlexMarks SignedMask OrbitHit Cheap LocalAtlas Grant OrientationCut OrientationExample ModuleCertificate TightCertificate; do check "$dir" "$m"; done
  for m in DeskForestData ForestBridge; do check "$src/../petersen-2504" "$m"; done
  for m in CutInterpreter AdaptiveForest AdaptiveRoot AdaptiveData AdaptiveSamples AdaptiveResult; do check "$src" "$m"; done
  lean -j1 --run "$src/AdaptiveEval.lean"
' sh "$src" "$build"
