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
# It fails loudly when: the pinned commit cannot be fetched or is not what was
# checked out; either module or the bridge does not compile; or any printed
# theorem depends on an axiom. On success it prints the facts a receipt needs.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

TT_REPOSITORY=hyperpolymath/tropical-types
TT_COMMIT=f2e465c966d14d4986dfc492875cc54653d9751e
TT_FILE=TropicalSessionTypes.lean
BRIDGE=verification/bridges/tropical-types/TropicalBridge.lean
lean="${LEAN:-lean}"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/build"

git init -q "$work/tt"
git -C "$work/tt" fetch -q --depth 1 "https://github.com/$TT_REPOSITORY" "$TT_COMMIT" \
  || { echo "ERROR: could not fetch $TT_REPOSITORY at $TT_COMMIT" >&2; exit 1; }
git -C "$work/tt" checkout -q FETCH_HEAD
got="$(git -C "$work/tt" rev-parse HEAD)"
[ "$got" = "$TT_COMMIT" ] \
  || { echo "ERROR: fetched $got, not the pinned $TT_COMMIT" >&2; exit 1; }
[ -f "$work/tt/$TT_FILE" ] \
  || { echo "ERROR: $TT_FILE is not in $TT_REPOSITORY at $TT_COMMIT" >&2; exit 1; }

compile() { # $1 dir, $2 file, $3 olean
  local out
  if ! out="$(cd "$1" && "$lean" -o "$3" "$2" 2>&1)" || grep -q 'error:' <<<"$out"; then
    printf '%s\n' "$out" >&2
    echo "ERROR: $2 does not compile" >&2
    exit 1
  fi
}
compile "$work/tt" "$TT_FILE" "$work/build/TropicalSessionTypes.olean"
compile verification/proofs/lean4 ResourceAlgebra.lean "$work/build/ResourceAlgebra.olean"

if ! out="$(cd "$(dirname "$BRIDGE")" && LEAN_PATH="$work/build" "$lean" "$(basename "$BRIDGE")" 2>&1)" \
   || grep -q 'error:' <<<"$out"; then
  printf '%s\n' "$out" >&2
  echo "ERROR: the bridge does not compile" >&2
  exit 1
fi

# A counted witness lists its axioms (§8.4): every printed theorem must say
# it depends on none.
n_print="$(grep -c '^#print axioms' "$BRIDGE")"
n_free="$(grep -c 'does not depend on any axioms' <<<"$out" || true)"
if [ "$n_print" -eq 0 ] || [ "$n_free" != "$n_print" ]; then
  printf '%s\n' "$out" >&2
  echo "ERROR: only $n_free of $n_print bridge theorems are axiom-free" >&2
  exit 1
fi

echo "PASS: M-2 bridge to $TT_REPOSITORY@$TT_COMMIT; $n_free of $n_print printed theorems depend on no axiom"
echo "import: $TT_REPOSITORY $TT_COMMIT $TT_FILE $(sha256sum "$work/tt/$TT_FILE" | cut -d' ' -f1)"
echo "bridge: $BRIDGE $(sha256sum "$BRIDGE" | cut -d' ' -f1)"
