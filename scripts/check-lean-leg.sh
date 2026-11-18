#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# check-lean-leg.sh: the Lean recheck leg under lake (PROOF-POLICY §8.2 names
# `lean` under `lake` as the qualifying kernel run). It builds the Lake package
# in verification/proofs/lean4 from a copy in a temporary directory, so no
# .lake/ build output lands in the tree, and takes the axiom census from that
# build. Lake prints each `#print axioms` report as an
# `info: <file>:<line>:<col>:` line.
#
# It fails loudly when: the build fails; any report says `depends on axioms`;
# the reports attributed to ResourceAlgebra.lean that say `does not depend on
# any axioms` differ in number from the `#print axioms` commands in the file
# (or there are none); or the build rewrote lake-manifest.json.
# LAKE overrides the lake binary.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

lake="${LAKE:-lake}"
src=verification/proofs/lean4
file=ResourceAlgebra.lean

work="$(mktemp -d)"
trap 'rm -rf "$work" "$work.manifest.before"' EXIT
for f in lakefile.toml lake-manifest.json lean-toolchain "$file"; do
  cp -- "$src/$f" "$work/"
done
# What lake was given, kept apart from the tree: a later edit of the tree
# is then never mistaken for a rewrite by lake, and never counted.
cp -- "$work/lake-manifest.json" "$work.manifest.before"

# The census needs every module compiled in this run: an artifact cache hit
# would build nothing and print no report.
if ! out="$(cd "$work" && LAKE_ARTIFACT_CACHE=false "$lake" build 2>&1)"; then
  printf '%s\n' "$out" >&2
  echo "ERROR: the Lean leg does not build under lake" >&2
  exit 1
fi
printf '%s\n' "$out"

if grep -q 'depends on axioms' <<<"$out"; then
  echo "ERROR: a printed theorem depends on axioms" >&2
  exit 1
fi

n_print="$(grep -cE '^[[:space:]]*#print[[:space:]]+axioms[[:space:]]' "$work/$file" || true)"
n_free="$(grep -cE "^info: ${file//./\\.}:[0-9]+:[0-9]+: .* does not depend on any axioms\$" <<<"$out" || true)"
if [ "$n_print" -eq 0 ] || [ "$n_free" != "$n_print" ]; then
  echo "ERROR: only $n_free of $n_print printed theorems are axiom-free" >&2
  exit 1
fi

if ! cmp -s "$work.manifest.before" "$work/lake-manifest.json"; then
  diff -u "$work.manifest.before" "$work/lake-manifest.json" >&2 || true
  echo "ERROR: the build rewrote lake-manifest.json (diff above). Regenerate it with lake update in a copy of $src, put it in the repository's canonical JSON form (scripts/check-ijson-jcs.sh), and commit it" >&2
  exit 1
fi

echo "PASS: Lean leg under lake; $n_free of $n_print printed theorems depend on no axiom"
