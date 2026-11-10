#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Core proofs plus expected rejections.  Pattern: residual-evidence-types.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL="${LC_ALL:-C.UTF-8}"
prover="${AGDA:-agda}"
"$prover" --version
# The canonical theory-proof invocation (standards PROOF-POLICY §2.1,
# 2026-11-01) is --safe --without-K --cubical-compatible. -W error makes any
# warning a failure, except UnsupportedIndexedMatch, which is suppressed.
# --no-libraries keeps the import cone first-party (no standard library);
# --double-check re-checks every term with the core type checker.
flags=(--safe --without-K --cubical-compatible --no-libraries --ignore-interfaces --double-check -W error -W noUnsupportedIndexedMatch -i src)
# PROOF-POLICY §8.4.6: a comment-aware postulate scan of the import cone
# (src/), alongside --safe. scripts/scan-postulates.pl reads each file in
# source order (nested block comments, line comments, strings) and fails on
# a file it cannot read.
# find runs to a file, not a process substitution, so its own failure (a
# directory it cannot read) stops the gate instead of leaving a partial cone.
cone_list="$(mktemp)"
trap 'rm -f "$cone_list"' EXIT
find src -name '*.agda' -print0 > "$cone_list" \
  || { echo "ERROR: could not list the import cone (src/)" >&2; exit 1; }
mapfile -d '' cone < "$cone_list"
(( ${#cone[@]} > 0 )) || { echo "ERROR: no Agda sources in the import cone" >&2; exit 1; }
if ! perl scripts/scan-postulates.pl "${cone[@]}"; then
  echo "ERROR: postulate in the import cone (src/), or an unreadable file" >&2
  exit 1
fi
echo "PASS: no postulate in the import cone (src/)"
"$prover" "${flags[@]}" src/ResourceAlgebra/All.agda
# Unit tests (closed computations and small lemmas over the instances).
"$prover" "${flags[@]}" -i tests/unit tests/unit/AllTests.agda
echo "PASS: unit tests (tests/unit/AllTests.agda)"
mkdir -p _build/check-logs
shopt -s nullglob
rejects=(tests/reject/*.agda)
shopt -u nullglob
if (( ${#rejects[@]} == 0 )); then
  echo 'ERROR: no expected-rejection modules found under tests/reject' >&2
  exit 1
fi
for file in "${rejects[@]}"; do
  name="$(basename -- "$file" .agda)"
  # The refusal must carry the message the fixture names: failing at the
  # declaration for some other reason must not pass.
  expect="$(sed -n 's/^-- EXPECT: //p' "$file" | head -1)"
  if [ -z "$expect" ]; then
    echo "ERROR: $name has no '-- EXPECT: <regex>' line" >&2
    exit 1
  fi
  log="_build/check-logs/$name.log"
  # The lines of the fixture's `invalid` definition: from its first clause
  # (the first `invalid` line that is not the type signature) to the last
  # clause or continuation line before the next top-level declaration.
  read -r def_first def_last < <(awk '
    !start { if (/^invalid([[:space:]]|$)/ && !/^invalid[[:space:]]*:/) start = last = NR; next }
    done || !NF || /^--/ { next }
    /^invalid([[:space:]]|$)/ || /^[[:space:]]/ { last = NR; next }
    { done = 1 }
    END { print start + 0, last + 0 }' "$file")
  if (( def_first == 0 )); then
    echo "ERROR: $file has no \`invalid\` definition to reject" >&2
    exit 1
  fi
  if "$prover" "${flags[@]}" -i tests/reject "$file" >"$log" 2>&1; then
    cat "$log"
    echo "ERROR: invalid proof accepted: $name" >&2
    exit 1
  fi
  # Agda stops at its first error, so the first location it reports in this
  # file must lie inside `invalid`.  Any `when checking that` diagnostic used
  # to pass, so an earlier, unrelated type error passed before Agda ever
  # reached the claim the fixture exists to refute.
  err_line="$(grep -oE "/$name\.agda:[0-9]+," "$log" | head -1 | sed -E 's/.*:([0-9]+),$/\1/' || true)"
  if [[ -z "$err_line" ]] ||
     (( err_line < def_first || err_line > def_last )) ||
     ! grep -q 'when checking that' "$log" ||
     grep -Eq 'Not in scope|Failed to find|Unsolved|Parse error' "$log"; then
    cat "$log"
    echo "ERROR: unexpected failure while checking $name" \
         "(first error at line ${err_line:-none}; \`invalid\` spans lines $def_first-$def_last)" >&2
    exit 1
  fi
  if ! grep -Eq -- "$expect" "$log"; then
    cat "$log"
    echo "ERROR: $name was refused, but not with: $expect" >&2
    exit 1
  fi
  echo "PASS: rejected $name at its invalid declaration (line $err_line: $expect)"
done
echo "PASS: core proofs, unit tests and all ${#rejects[@]} expected rejections"
