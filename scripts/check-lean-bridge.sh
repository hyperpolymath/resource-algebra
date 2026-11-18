#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# check-lean-bridge.sh: the M-2 bridge (docs/status/PROOF-STATUS.adoc).
#
# verification/bridges/tropical-types/TropicalBridge.lean proves that this
# repository's MaxPlus (the Lean leg, verification/proofs/lean4) is isomorphic
# to the Tropical semiring of hyperpolymath/tropical-types. It imports one
# file of that repository, read at the commit pinned below. This script is the
# only place the pin lives (PROOF-POLICY §8.5.1, imported repositories), so a
# repin changes this file and with it the home input digest.
#
# The three files are built as a dependency-free Lake package (PROOF-POLICY
# §8.2 names `lean` under `lake` as the qualifying run): the lakefile and its
# lake-manifest.json sit beside the bridge, and `lake build` runs in a work
# directory so no .lake/ output lands in the tree. The tropical-types pin stays
# here, not in a lake `require`.
#
# It fails loudly when: the pinned commit cannot be fetched or is not what was
# checked out; any module or the bridge does not build; any printed theorem
# depends on an axiom; the bridge prints no theorem or not all axiom-free; or
# the build rewrote lake-manifest.json. On success it prints the facts a
# receipt needs. LAKE overrides the lake binary.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

TT_REPOSITORY=hyperpolymath/tropical-types
TT_COMMIT=f2e465c966d14d4986dfc492875cc54653d9751e
TT_FILE=TropicalSessionTypes.lean
BRIDGE=verification/bridges/tropical-types/TropicalBridge.lean
BRIDGE_DIR=verification/bridges/tropical-types
RA_FILE=verification/proofs/lean4/ResourceAlgebra.lean
TOOLCHAIN=verification/proofs/lean4/lean-toolchain
lake="${LAKE:-lake}"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

git init -q "$work/tt"
git -C "$work/tt" fetch -q --depth 1 "https://github.com/$TT_REPOSITORY" "$TT_COMMIT" \
  || { echo "ERROR: could not fetch $TT_REPOSITORY at $TT_COMMIT" >&2; exit 1; }
git -C "$work/tt" checkout -q FETCH_HEAD
got="$(git -C "$work/tt" rev-parse HEAD)"
[ "$got" = "$TT_COMMIT" ] \
  || { echo "ERROR: fetched $got, not the pinned $TT_COMMIT" >&2; exit 1; }
[ -f "$work/tt/$TT_FILE" ] \
  || { echo "ERROR: $TT_FILE is not in $TT_REPOSITORY at $TT_COMMIT" >&2; exit 1; }

mkdir -p "$work/pkg"
cp -- "$BRIDGE_DIR/lakefile.toml" "$BRIDGE_DIR/lake-manifest.json" "$BRIDGE" \
  "$RA_FILE" "$TOOLCHAIN" "$work/tt/$TT_FILE" "$work/pkg/"

if ! out="$(cd "$work/pkg" && "$lake" build 2>&1)" || grep -q 'error:' <<<"$out"; then
  printf '%s\n' "$out" >&2
  echo "ERROR: the bridge package does not build under lake" >&2
  exit 1
fi
if grep -q 'depends on axioms' <<<"$out"; then
  printf '%s\n' "$out" >&2
  echo "ERROR: a printed theorem depends on axioms" >&2
  exit 1
fi
if ! cmp -s "$BRIDGE_DIR/lake-manifest.json" "$work/pkg/lake-manifest.json"; then
  echo "ERROR: the build rewrote lake-manifest.json; commit the manifest lake writes" >&2
  exit 1
fi

# A counted witness lists its axioms (§8.4): every theorem the bridge prints
# must say it depends on none. Lake prints each report as an
# `info: <file>:<line>:<col>:` line; count those attributed to the bridge.
bridge_name="$(basename -- "$BRIDGE")"
n_print="$(grep -cE '^#print axioms' "$BRIDGE" || true)"
n_free="$(grep -cE "^info: ${bridge_name//./\\.}:[0-9]+:[0-9]+: .* does not depend on any axioms\$" <<<"$out" || true)"
if [ "$n_print" -eq 0 ] || [ "$n_free" != "$n_print" ]; then
  printf '%s\n' "$out" >&2
  echo "ERROR: only $n_free of $n_print bridge theorems are axiom-free" >&2
  exit 1
fi

echo "PASS: M-2 bridge to $TT_REPOSITORY@$TT_COMMIT; $n_free of $n_print printed theorems depend on no axiom"
echo "import: $TT_REPOSITORY $TT_COMMIT $TT_FILE $(sha256sum "$work/tt/$TT_FILE" | cut -d' ' -f1)"
echo "bridge: $BRIDGE $(sha256sum "$BRIDGE" | cut -d' ' -f1)"
