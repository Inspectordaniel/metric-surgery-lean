#!/usr/bin/env bash
# Comparator's core check, run locally without Go, Rust or Landrun.
#
# Comparator compiles Challenge.lean and Solution.lean into separate environments and then
# requires (a) the five compared theorems to have equal types and (b) every constant reachable
# from those types to be equal in both. This script reproduces that walk inside Lean: it loads
# each module on its own, serialises the whole non-Mathlib closure structurally, and diffs.
#
# Binder names are elided before the diff because Comparator compares expressions with
# `BEq Expr`, which is alpha-equivalence; Lean's hygienic instance-binder names embed the
# module they were elaborated in, so they differ between the two modules by construction and
# are not part of what Comparator compares.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

for module in Challenge Solution; do
  { printf 'import %s\n' "$module"; cat "$root/scripts/surface_dump.lean.in"; } > "$work/Dump$module.lean"
  (cd "$root" && lake env lean "$work/Dump$module.lean") > "$work/$module.dump"
  sed -E -e 's/\((all|fun) [^ ]*:/(\1 _:/g' -e 's/\(let [^ ]* /(let _ /g' \
    "$work/$module.dump" > "$work/$module.norm"
done

compared=$(grep -cE '^(def|theorem|inductive|ctor|rec|opaque|axiom|quot) ' "$work/Challenge.norm")

if ! diff -q "$work/Challenge.norm" "$work/Solution.norm" >/dev/null; then
  echo "error: the Challenge and Solution environments disagree; Comparator would reject" >&2
  diff "$work/Challenge.norm" "$work/Solution.norm" | cut -c1-200 | head -40 >&2
  exit 1
fi

echo "Challenge and Solution agree on all 5 compared theorems and their $compared-declaration closure"
