#!/bin/sh
set -eu
src=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$(git -C "$src" rev-parse --show-toplevel)
cd "$repo/lean"
lake build PEqualNP.Outside.L_meta_1667 PEqualNP.Outside.L_meta_2036 PEqualNP.Outside.L_meta_2502
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
' sh "$src" "$build" Marked MarkedNodes MarkedRotate SmallTables MarkedTables Core Verify Stages FastStages ReadOnce ReadMask ReadFold Sym SymCheck ReadSearch Positive PosMask SignedTree SharedTree ModuleCut Partitions FlexMarks SignedMask OrbitHit Cheap LocalAtlas Grant OrientationCut OrientationExample ModuleCertificate Near GrantMasks Coherent DataAll BundleAll Root383 PetersenReaderCofactors ReaderTrace TraceCircuit TracedOptimal ReaderMapping SeedFilter TraceBudget TraceSemantics CofactorJoin ReaderBranches ReaderSetup ReaderConclusion ReaderFinite EvaluateAll
