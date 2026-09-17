#!/usr/bin/env bash
# Compile Challenge.lean the way the canonical Palomar verifier does: against the pinned
# dependency packages alone, with no Lake configuration and no access to this repository's
# own `Tablet` library. A Challenge that only builds via `lake build Challenge` can still
# fail here, which is what "unknown module prefix 'Tablet'" looks like.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
packages="$root/.lake/packages"

if [ ! -d "$packages" ]; then
  echo "error: $packages does not exist; run 'lake exe cache get && lake build' first" >&2
  exit 1
fi

search_path=$(find "$packages" -maxdepth 6 -type d -path '*/.lake/build/lib/lean' | sort | paste -sd: -)
if [ -z "$search_path" ]; then
  echo "error: no built packages under $packages; run 'lake build' first" >&2
  exit 1
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# `lean-toolchain` travels with the source so elan resolves the pinned toolchain, exactly as
# the verifier's own checkout does.
cp "$root/Challenge.lean" "$root/lean-toolchain" "$work/"

echo "Challenge.lean, search path: $(echo "$search_path" | tr ':' '\n' | wc -l) pinned packages, no Lake config"
cd "$work"
env -u LEAN_PATH LEAN_PATH="$search_path" lean Challenge.lean

echo "Challenge.lean compiles against the pinned dependencies alone"
